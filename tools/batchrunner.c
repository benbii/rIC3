#include "batchrunner.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/mempolicy.h>
#include <numa.h>
#include <sched.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/signalfd.h>
#include <sys/syscall.h>
#include <sys/timerfd.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

struct RunQueue run_pending;
struct RunQueue run_finished;
atomic_bool run_stop;
size_t run_nr_worker;
size_t run_timelim;
size_t run_memlim_kb;
size_t run_nr_numa;
bool run_capture_output;

// 1MB bitmap with running child PGIDs set to 1; covers PIDs up to 8M.
static atomic_ullong run_pids[125000];
_Static_assert(sizeof(atomic_ullong) == 8, "");

static void run_sig_handler(int sig) {
  atomic_store(&run_stop, true);
  for (size_t i = 0; i < 125000; ++i) {
    unsigned long long bits = atomic_load(&run_pids[i]);
    if (!bits) continue;
    for (size_t j = 0; j < 64; ++j)
      if (bits & (1ULL << j))
        kill(-(pid_t)(i * 64 + j), sig);
  }
  sleep(2);
  for (size_t i = 0; i < 125000; ++i) {
    unsigned long long bits = atomic_load(&run_pids[i]);
    if (!bits) continue;
    for (size_t j = 0; j < 64; ++j)
      if (bits & (1ULL << j))
        kill(-(pid_t)(i * 64 + j), SIGKILL);
  }
  _exit(128 + sig);
}

void run_setup_handler(void) {
  struct sigaction sa = {0};
  sa.sa_handler = run_sig_handler;
  sigfillset(&sa.sa_mask);
  assert(sigaction(SIGINT, &sa, NULL) == 0);
  assert(sigaction(SIGTERM, &sa, NULL) == 0);
  assert(sigaction(SIGHUP, &sa, NULL) == 0);
}

static uint64_t run_now_ns(void) {
  struct timespec ts;
  assert(clock_gettime(CLOCK_MONOTONIC, &ts) == 0);
  return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static size_t run_memory_usage(pid_t pid) {
  char filename[64], line[256];
  snprintf(filename, sizeof(filename), "/proc/%d/status", pid);
  FILE *file = fopen(filename, "r");
  if (file == NULL) return 0;
  size_t memory_usage = 0;
  while (fgets(line, sizeof(line), file)) {
    if (strncmp(line, "VmRSS:", 6) == 0) {
      (void)sscanf(line, "VmRSS: %zu kB", &memory_usage);
      break;
    }
  }
  fclose(file);
  return memory_usage;
}

// Read one captured stream.  Called both for epoll events and final draining.
static void run_read_output(int epfd, struct RunInfo *info,
                               unsigned stream, bool finish) {
  int *fd = stream == 0 ? &info->stdout_fd : &info->stderr_fd;
  char **buf = stream == 0 ? &info->stdout_ : &info->stderr_;
  size_t *size = stream == 0 ? &info->stdout_sz : &info->stderr_sz;
  size_t *cap = stream == 0 ? &info->stdout_cap : &info->stderr_cap;
  if (*fd < 0) return;

  bool eof = false;
  size_t read_now = 0;
  for (;;) {
    if (*size == *cap) {
      *cap *= 2;
      *buf = realloc(*buf, *cap);
      assert(*buf);
    }
    ssize_t n = read(*fd, *buf + *size, *cap - *size);
    if (n > 0) {
      *size += (size_t)n;
      read_now += (size_t)n;
      if (!finish && read_now >= 65536) break;
      continue;
    }
    if (n == 0) {
      eof = true;
      break;
    }
    if (errno == EINTR) continue;
    if (errno == EAGAIN || errno == EWOULDBLOCK) break;
    assert(false);
  }

  if (finish || eof) {
    assert(epoll_ctl(epfd, EPOLL_CTL_DEL, *fd, NULL) == 0);
    close(*fd);
    *fd = -1;
  }
}

size_t run_enqueue_group(const char *grpstr, size_t grpsz,
                            const char *chkpt, size_t chkpt_sz) {
  assert(grpsz >= 3);
  assert(grpstr[grpsz - 1] == 0 && grpstr[grpsz - 2] == 0 &&
         grpstr[grpsz - 3] == 0);

  char *argbuf = malloc(grpsz);
  assert(argbuf);
  memcpy(argbuf, grpstr, grpsz);

  struct RunInfo info[RUN_GROUP_MAX] = {0};
  char *p = argbuf, *end = argbuf + grpsz;
  size_t nr_run = 0;
  while (*p) {
    char *q = p;
    size_t argc = 0;
    while (*q) {
      ++argc;
      q += strlen(q) + 1;
      assert(q < end);
    }
    assert(argc > 0 && q + 1 < end);

    size_t cmdsz = (size_t)(q - p);
    char cmdline[cmdsz];
    memcpy(cmdline, p, cmdsz);
    for (size_t i = 0; i < cmdsz; ++i)
      if (cmdline[i] == '\0') cmdline[i] = ' ';

    if (!(chkpt && memmem(chkpt, chkpt_sz, cmdline, cmdsz))) {
      assert(nr_run < RUN_GROUP_MAX);
      info[nr_run].argv = calloc(argc + 1, sizeof(char *));
      assert(info[nr_run].argv);
      info[nr_run].program = p;
      info[nr_run].argc = argc;
      info[nr_run].group_pos = (unsigned)nr_run;
      char *a = p;
      for (size_t i = 0; i < argc; ++i) {
        info[nr_run].argv[i] = a;
        a += strlen(a) + 1;
      }
      ++nr_run;
    }
    p = q + 1;
  }
  assert(p + 1 == end);

  if (nr_run == 0) {
    free(argbuf);
    return 0;
  }
  assert(nr_run <= run_nr_worker);

  struct RunGroup *group = malloc(sizeof(*group));
  assert(group);
  *group = (struct RunGroup){
      .argbuf = argbuf,
      .nr_run = nr_run,
      .nr_running = nr_run,
  };
  for (size_t i = 0; i < nr_run; ++i)
    info[i].group = group;

  size_t tail = atomic_load_explicit(&run_pending.tail, memory_order_relaxed);
  size_t head = atomic_load_explicit(&run_pending.head, memory_order_acquire);
  assert(tail - head + nr_run <= RUN_QUEUE_CAP);
  for (size_t i = 0; i < nr_run; ++i)
    run_pending.item[(tail + i) % RUN_QUEUE_CAP] = info[i];
  atomic_store_explicit(&run_pending.tail, tail + nr_run,
                        memory_order_release);
  return nr_run;
}

void run_print(const struct RunInfo *info, FILE *file, bool oneline) {
  if (!file) return;
  if (!oneline) fprintf(file, "## ");
  for (size_t i = 0; i < info->argc; ++i)
    fprintf(file, "%s ", info->argv[i]);
  fprintf(file,
          oneline ? "%" PRIu64 "sec %zuKB "
                  : "\nDuration: %" PRIu64
                    " seconds\nPeak Memory: %zuKB\nExit: ",
          info->duration, info->peak_mem);
  if (info->timed_out)
    fputs("timeout\n", file);
  else if (info->mem_out)
    fputs("memout\n", file);
  else if (info->lost)
    fputs("underperformed\n", file);
  else if (WIFEXITED(info->retval))
    fprintf(file, "status %d\n", WEXITSTATUS(info->retval));
  else
    fprintf(file, "signal %d\n", WTERMSIG(info->retval));
  if (oneline) {
    fflush(file);
    return;
  }
  fprintf(file, "MemLim %zuKB, TimeLim %zus\n", run_memlim_kb,
          run_timelim);
  fprintf(file, "\n\n### Standard Output\n");
  if (info->stdout_sz)
    fwrite(info->stdout_, info->stdout_sz, 1, file);
  fprintf(file, "\n\n### Standard Error\n");
  if (info->stderr_sz)
    fwrite(info->stderr_, info->stderr_sz, 1, file);
  fprintf(file, "\n-------------------------------------------\n\n");
  fflush(file);
}

void *run_runner(void *unused) {
  (void)unused;
  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGINT);
  sigaddset(&blocked, SIGTERM);
  sigaddset(&blocked, SIGHUP);
  assert(pthread_sigmask(SIG_BLOCK, &blocked, NULL) == 0);

  const size_t nr_worker = run_nr_worker;
  const size_t nr_numa = run_nr_numa;
  assert(nr_worker > 0);
  struct RunInfo active[nr_worker];
  memset(active, 0, sizeof(active));

  const size_t nr_node_array = nr_numa ? nr_numa : 1;
  long numa_slot[nr_node_array];
  cpu_set_t cpu_mask[nr_node_array];
  struct bitmask *mem_mask[nr_node_array];
  memset(numa_slot, 0, sizeof(numa_slot));
  memset(mem_mask, 0, sizeof(mem_mask));

  if (nr_numa) {
    assert(numa_available() >= 0);
    assert(nr_numa <= (size_t)numa_max_node() + 1);
    int nr_cpu = numa_num_configured_cpus();
    assert(nr_cpu > 0 && nr_cpu <= CPU_SETSIZE);
    size_t per_node = (nr_worker + nr_numa - 1) / nr_numa;
    size_t bubbles = per_node * nr_numa - nr_worker;
    for (size_t node = 0; node < nr_numa; ++node) {
      size_t node_bubbles = bubbles < per_node ? bubbles : per_node;
      numa_slot[node] = (long)(per_node - node_bubbles);
      bubbles -= node_bubbles;
      CPU_ZERO(&cpu_mask[node]);
      struct bitmask *mask = numa_allocate_cpumask();
      assert(mask);
      assert(numa_node_to_cpus((int)node, mask) == 0);
      for (int cpu = 0; cpu < nr_cpu; ++cpu)
        if (numa_bitmask_isbitset(mask, (unsigned)cpu))
          CPU_SET((size_t)cpu, &cpu_mask[node]);
      numa_free_cpumask(mask);
      mem_mask[node] = numa_allocate_nodemask();
      assert(mem_mask[node]);
      numa_bitmask_clearall(mem_mask[node]);
      numa_bitmask_setbit(mem_mask[node], (unsigned)node);
    }
    assert(bubbles == 0);
  }

  int epfd = epoll_create1(EPOLL_CLOEXEC);
  int timerfd = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC);
  sigset_t child_signal;
  sigemptyset(&child_signal);
  sigaddset(&child_signal, SIGCHLD);
  int childfd = signalfd(-1, &child_signal, SFD_CLOEXEC | SFD_NONBLOCK);
  assert(epfd >= 0 && timerfd >= 0 && childfd >= 0);
  struct itimerspec timer = {{1, 500000000}, {1, 500000000}};
  assert(timerfd_settime(timerfd, 0, &timer, NULL) == 0);
  struct epoll_event timer_event = {
      .events = EPOLLIN,
      .data.u64 = UINT64_MAX,
  };
  assert(epoll_ctl(epfd, EPOLL_CTL_ADD, timerfd, &timer_event) == 0);
  struct epoll_event child_event = {
      .events = EPOLLIN,
      .data.u64 = UINT64_MAX - 1,
  };
  assert(epoll_ctl(epfd, EPOLL_CTL_ADD, childfd, &child_event) == 0);

  int nullfd = -1;
  if (!run_capture_output) {
    nullfd = open("/dev/null", O_WRONLY | O_CLOEXEC);
    assert(nullfd >= 0);
  }

  struct epoll_event events[2 * nr_worker + 2];
  size_t nr_active = 0;
  bool tick = true;

  for (;;) {
    // Reap before admitting pending work so newly released slots are visible.
    for (;;) {
      int status;
      pid_t pid = waitpid(-1, &status, WNOHANG);
      if (pid == 0) break;
      if (pid < 0) {
        assert(errno == ECHILD);
        break;
      }

      size_t slot = 0;
      while (slot < nr_worker && active[slot].pid != pid) ++slot;
      assert(slot < nr_worker);
      struct RunInfo *info = &active[slot];
      run_read_output(epfd, info, 0, true);
      run_read_output(epfd, info, 1, true);
      info->retval = status;
      info->duration = (run_now_ns() - info->started_ns) / 1000000000ULL;

      if (WIFEXITED(status) && !info->group->won) {
        info->group->won = true;
        for (size_t i = 0; i < nr_worker; ++i) {
          if (i == slot || active[i].pid <= 0 ||
              active[i].group != info->group)
            continue;
          active[i].lost = true;
          if (active[i].terminating == 0) {
            (void)kill(-active[i].pid, SIGINT);
            active[i].terminating = 1;
            active[i].signal_ns = run_now_ns();
          }
        }
      }

      assert(info->group->nr_running > 0);
      --info->group->nr_running;
      if (info->numa_node)
        ++numa_slot[info->numa_node - 1];
      atomic_fetch_and(&run_pids[(size_t)pid / 64],
                       ~(1ULL << ((size_t)pid % 64)));

      struct RunInfo done = *info;
      memset(info, 0, sizeof(*info));
      --nr_active;

      size_t tail = atomic_load_explicit(&run_finished.tail,
                                         memory_order_relaxed);
      size_t head = atomic_load_explicit(&run_finished.head,
                                         memory_order_acquire);
      assert(tail - head < RUN_QUEUE_CAP);
      run_finished.item[tail % RUN_QUEUE_CAP] = done;
      atomic_store_explicit(&run_finished.tail, tail + 1,
                            memory_order_release);
    }

    uint64_t now = run_now_ns();
    if (tick) {
      for (size_t i = 0; i < nr_worker; ++i) {
        struct RunInfo *info = &active[i];
        if (info->pid <= 0) continue;

        size_t usage = run_memory_usage(info->pid);
        if (usage > info->peak_mem) info->peak_mem = usage;
        if (info->terminating) {
          if (info->terminating == 1 &&
              now - info->signal_ns >= 500000000ULL) {
            (void)kill(-info->pid, SIGKILL);
            info->terminating = 2;
          }
          continue;
        }

        uint64_t elapsed = now - info->started_ns;
        info->timed_out = elapsed >= run_timelim * 1000000000ULL;
        info->mem_out = usage > run_memlim_kb;
        if (info->timed_out || info->mem_out) {
          (void)kill(-info->pid, SIGINT);
          info->terminating = 1;
          info->signal_ns = now;
        }
      }
      tick = false;
    }

    // A pending group is published in one release-store and admitted whole.
    for (;;) {
      if (atomic_load_explicit(&run_stop, memory_order_acquire)) break;
      size_t head = atomic_load_explicit(&run_pending.head,
                                         memory_order_relaxed);
      size_t tail = atomic_load_explicit(&run_pending.tail,
                                         memory_order_acquire);
      if (head == tail) break;
      struct RunInfo *first = &run_pending.item[head % RUN_QUEUE_CAP];
      assert(first->group_pos == 0);
      size_t nr_group = first->group->nr_run;
      assert(tail - head >= nr_group);
      if (nr_worker - nr_active < nr_group) break;
      size_t finished_head = atomic_load_explicit(&run_finished.head,
                                                  memory_order_acquire);
      size_t finished_tail = atomic_load_explicit(&run_finished.tail,
                                                  memory_order_relaxed);
      if (finished_tail - finished_head + nr_active + nr_group >
          RUN_QUEUE_CAP)
        break;

      for (size_t g = 0; g < nr_group; ++g) {
        struct RunInfo queued =
            run_pending.item[(head + g) % RUN_QUEUE_CAP];
        assert(queued.group == first->group && queued.group_pos == g);

        size_t slot = 0;
        while (slot < nr_worker && active[slot].pid > 0) ++slot;
        assert(slot < nr_worker);

        size_t node = 0;
        if (nr_numa) {
          for (size_t n = 1; n < nr_numa; ++n)
            if (numa_slot[n] > numa_slot[node]) node = n;
          assert(numa_slot[node] > 0);
          --numa_slot[node];
          queued.numa_node = (unsigned)node + 1;
        }
        queued.stdout_fd = queued.stderr_fd = -1;

        int stdout_pipe[2] = {-1, -1}, stderr_pipe[2] = {-1, -1};
        if (run_capture_output) {
          assert(pipe2(stdout_pipe, O_CLOEXEC) == 0);
          assert(pipe2(stderr_pipe, O_CLOEXEC) == 0);
          int flags = fcntl(stdout_pipe[0], F_GETFL);
          assert(flags >= 0 &&
                 fcntl(stdout_pipe[0], F_SETFL, flags | O_NONBLOCK) == 0);
          flags = fcntl(stderr_pipe[0], F_GETFL);
          assert(flags >= 0 &&
                 fcntl(stderr_pipe[0], F_SETFL, flags | O_NONBLOCK) == 0);
        }

        pid_t pid = fork();
        assert(pid >= 0);
        if (pid == 0) {
          struct sigaction child_action = {.sa_handler = SIG_DFL};
          sigemptyset(&child_action.sa_mask);
          assert(sigaction(SIGINT, &child_action, NULL) == 0);
          assert(sigaction(SIGTERM, &child_action, NULL) == 0);
          assert(sigaction(SIGHUP, &child_action, NULL) == 0);
          sigset_t clear;
          sigemptyset(&clear);
          assert(sigprocmask(SIG_SETMASK, &clear, NULL) == 0);
          assert(setpgid(0, 0) == 0);
          if (nr_numa) {
            size_t child_node = queued.numa_node - 1;
            assert(syscall(SYS_set_mempolicy, MPOL_BIND,
                           mem_mask[child_node]->maskp,
                           mem_mask[child_node]->size + 1) == 0);
            assert(sched_setaffinity(0, sizeof(cpu_set_t),
                                     &cpu_mask[child_node]) == 0);
          }
          if (run_capture_output) {
            close(stdout_pipe[0]);
            close(stderr_pipe[0]);
            assert(dup2(stdout_pipe[1], STDOUT_FILENO) == STDOUT_FILENO);
            assert(dup2(stderr_pipe[1], STDERR_FILENO) == STDERR_FILENO);
            close(stdout_pipe[1]);
            close(stderr_pipe[1]);
          } else {
            assert(dup2(nullfd, STDOUT_FILENO) == STDOUT_FILENO);
            assert(dup2(nullfd, STDERR_FILENO) == STDERR_FILENO);
          }
          execvp(queued.program, queued.argv);
          perror("execvp");
          abort();
        }

        if (run_capture_output) {
          close(stdout_pipe[1]);
          close(stderr_pipe[1]);
          queued.stdout_fd = stdout_pipe[0];
          queued.stderr_fd = stderr_pipe[0];
          queued.stdout_cap = queued.stderr_cap = 4096;
          queued.stdout_ = malloc(queued.stdout_cap);
          queued.stderr_ = malloc(queued.stderr_cap);
          assert(queued.stdout_ && queued.stderr_);
        }
        (void)setpgid(pid, pid);
        queued.pid = pid;
        queued.started_ns = run_now_ns();
        assert((size_t)pid / 64 < 125000);
        atomic_fetch_or(&run_pids[(size_t)pid / 64],
                        1ULL << ((size_t)pid % 64));
        active[slot] = queued;

        if (run_capture_output) {
          struct epoll_event event = {
              .events = EPOLLIN | EPOLLHUP | EPOLLERR,
              .data.u64 = slot * 2,
          };
          assert(epoll_ctl(epfd, EPOLL_CTL_ADD, queued.stdout_fd, &event) == 0);
          event.data.u64 = slot * 2 + 1;
          assert(epoll_ctl(epfd, EPOLL_CTL_ADD, queued.stderr_fd, &event) == 0);
        }
        ++nr_active;
      }
      atomic_store_explicit(&run_pending.head, head + nr_group,
                            memory_order_release);
    }

    size_t pending_head = atomic_load_explicit(&run_pending.head,
                                               memory_order_relaxed);
    size_t pending_tail = atomic_load_explicit(&run_pending.tail,
                                               memory_order_acquire);
    if (atomic_load_explicit(&run_stop, memory_order_acquire) &&
        nr_active == 0 && pending_head == pending_tail)
      break;

    int nr_event = epoll_wait(epfd, events, (int)(2 * nr_worker + 2), -1);
    if (nr_event < 0 && errno == EINTR) continue;
    assert(nr_event >= 0);
    for (int i = 0; i < nr_event; ++i) {
      if (events[i].data.u64 == UINT64_MAX) {
        uint64_t expirations;
        assert(read(timerfd, &expirations, sizeof(expirations)) ==
               (ssize_t)sizeof(expirations));
        tick = true;
        continue;
      }
      if (events[i].data.u64 == UINT64_MAX - 1) {
        struct signalfd_siginfo signals[32];
        for (;;) {
          ssize_t n = read(childfd, signals, sizeof(signals));
          if (n > 0) continue;
          if (n < 0 && errno == EINTR) continue;
          assert(n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK));
          break;
        }
        continue;
      }
      size_t slot = (size_t)(events[i].data.u64 / 2);
      unsigned stream = (unsigned)(events[i].data.u64 % 2);
      assert(slot < nr_worker && active[slot].pid > 0);
      run_read_output(epfd, &active[slot], stream, false);
    }
  }

  if (nullfd >= 0) close(nullfd);
  for (size_t node = 0; node < nr_numa; ++node)
    numa_free_nodemask(mem_mask[node]);
  close(childfd);
  close(timerfd);
  close(epfd);
  return NULL;
}
