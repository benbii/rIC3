#include "run-info.h"
#include <numa.h>
#include <poll.h>
#include <signal.h>
#include <stdatomic.h>
#include <sys/timerfd.h>
#include <sys/wait.h>

// 1MB bitmap with running child PGIDs set to 1; covers PIDs up to 8M
static atomic_ullong bmp[125000];
_Static_assert(sizeof(atomic_ullong) == 8, "");

void run_sig_handler(int sig) {
  // first pass: polite signal
  for (size_t i = 0; i < 125000; ++i) {
    unsigned long long bits = atomic_load(&bmp[i]);
    if (!bits) continue;
    for (size_t j = 0; j < 64; ++j)
      if (bits & (1ULL << j)) {
        pid_t pg = (pid_t)(i * 64 + j);
        kill(-pg, sig);
      }
  }
  sleep(2);
  // second pass: force kill anyone still alive
  for (size_t i = 0; i < 125000; ++i) {
    unsigned long long bits = atomic_load(&bmp[i]);
    if (!bits) continue;
    for (size_t j = 0; j < 64; ++j)
      if (bits & (1ULL << j)) {
        pid_t pg = (pid_t)(i * 64 + j);
        kill(-pg, SIGKILL);
      }
  }
  _exit(128 + sig);
}

void run_setup_handler(void) {
  struct sigaction sa = {0};
  sa.sa_handler = run_sig_handler;
  sigfillset(&sa.sa_mask);
  sigaction(SIGINT, &sa, NULL);
  sigaction(SIGTERM, &sa, NULL);
  sigaction(SIGHUP, &sa, NULL);
}

size_t get_memory_usage(pid_t pid) {
  char filename[256];
  snprintf(filename, sizeof(filename), "/proc/%d/status", pid);
  FILE *file = fopen(filename, "r");
  if (file == NULL) return 0;
  char line[256];
  size_t memory_usage = 0;
  // Read the status file line by line
  while (fgets(line, sizeof(line), file)) {
    // Look for the line containing "VmRSS", which gives the current memory usage
    if (strncmp(line, "VmRSS:", 6) == 0) {
      // Extract the memory usage in kilobytes (kB)
      sscanf(line, "VmRSS: %zu kB", &memory_usage);
      break;
    }
  }
  fclose(file);
  return memory_usage;  // Memory usage in kilobytes
}

void run_one(struct RunInfo* info) {
  if (info->numa_node > 0) {
    // numactl -m0 -N0
    unsigned node = info->numa_node - 1, c = numa_num_configured_cpus();
    struct bitmask *mem_mask = numa_allocate_nodemask();
    numa_bitmask_clearall(mem_mask);
    numa_bitmask_setbit(mem_mask, node);
    numa_set_membind(mem_mask);
    struct bitmask *cpu_mask = numa_allocate_cpumask();
    numa_node_to_cpus(node, cpu_mask);
    cpu_set_t cpuset; CPU_ZERO(&cpuset);
    for (int i = 0; i < c; i++)
      if (numa_bitmask_isbitset(cpu_mask, i))
        CPU_SET(i, &cpuset);
    if (sched_setaffinity(0, sizeof(cpuset), &cpuset) != 0)
      perror("sched_setaffinity");
    numa_free_cpumask(cpu_mask), numa_free_nodemask(mem_mask);
  }

  // Create pipes to capture stdout_ and stderr
  int stdout_pipe[2], stderr_pipe[2];
  if (pipe2(stdout_pipe, O_CLOEXEC) != 0 ||
      pipe2(stderr_pipe, O_CLOEXEC) != 0) {
    perror("pipe");
    exit(6);
  }
  // Fork the process
  pid_t pid = fork();
  assert(pid >= 0);
  if (pid == 0) {
    // Child process
    sigset_t s;
    sigemptyset(&s);
    sigprocmask(SIG_SETMASK, &s, NULL);
    setpgid(0, 0);
    // Redirect stdout_ to the stdout pipe
    close(stdout_pipe[0]);  // Close the read end of the stdout_ pipe
    dup2(stdout_pipe[1], STDOUT_FILENO);  // Redirect stdout_ to the pipe
    // Redirect stderr to the stderr pipe
    close(stderr_pipe[0]);  // Close the read end of the stderr pipe
    dup2(stderr_pipe[1], STDERR_FILENO);  // Redirect stderr to the pipe
    close(stdout_pipe[1]);
    close(stderr_pipe[1]);
    // Execute the program
    execvp(info->program, (char **)info->argv);
    perror("execvp");
    abort(); // SIGABRT the child
  }

  // Parent process
  // Close the write ends of the pipes
  close(stdout_pipe[1]), close(stderr_pipe[1]);
  setpgid(pid, pid);
  atomic_fetch_or(&bmp[pid / 64], 1ULL << (pid % 64));
  // Initialize variables for reading from pipes
  size_t out_cap = 4096, out_nread = 0;
  size_t err_cap = 4096, err_nread = 0;
  // Setup info
  info->duration = 0;
  info->stdout_ = malloc(out_cap), info->stderr_ = malloc(err_cap);
  assert(info->stdout_ && info->stderr_);

  int tfd = timerfd_create(CLOCK_MONOTONIC, 0);
  assert(tfd >= 0);
  struct itimerspec spec = {{1, 0}, {1, 0}};
  timerfd_settime(tfd, 0, &spec, NULL);
  struct pollfd pfds[3] = {
      {stdout_pipe[0], POLLIN}, {stderr_pipe[0], POLLIN}, {tfd, POLLIN}};

  // While not finished
  while (0 == waitpid(pid, &(info->retval), WNOHANG)) {
    // Wait for data to be available on any pipe
    int ready_fds = poll(pfds, 3, -1);
    assert(ready_fds >= 0);

    // Check if stdout_ pipe has data
    if (pfds[0].revents & POLLIN) {
      ssize_t n = read(stdout_pipe[0], info->stdout_ + out_nread, out_cap - out_nread);
      if (n <= 0) {
        pfds[0].fd = -1;  // Stop monitoring this fd (EOF or error)
        continue;
      }
      out_nread += n;
      // Reallocate memory if necessary
      if (out_nread == out_cap) {
        out_cap *= 2;
        info->stdout_ = realloc(info->stdout_, out_cap);
        assert(info->stdout_);
      }
    }
    // Check if stderr pipe has data
    if (pfds[1].revents & POLLIN) {
      ssize_t n = read(stderr_pipe[0], info->stderr_ + err_nread, err_cap - err_nread);
      if (n <= 0) {
        pfds[1].fd = -1;  // Stop monitoring this fd (EOF or error)
        continue;
      }
      err_nread += n;
      // Reallocate memory if necessary
      if (err_nread == err_cap) {
        err_cap *= 2;
        info->stderr_ = realloc(info->stderr_, err_cap);
        assert(info->stderr_);
      }
    }

    // Get memory usage once per second
    if (pfds[2].revents & POLLIN) {
      size_t cur_usage = get_memory_usage(pid);
      if (cur_usage > info->peak_mem)
        info->peak_mem = cur_usage;
      uint64_t nr_timeout;
      (void)read(tfd, &nr_timeout, 8);
      info->duration += nr_timeout;
      if (cur_usage <= info->memlim_kb && info->duration < info->timelim &&
          atomic_load_explicit(info->_grp_ctr, memory_order_relaxed) > 0)
        continue;
      // Timeout, out of memory or competitors finished
      kill(-pid, SIGINT);
      usleep(500000);
      // Wait for the terminated process to finish
      while (0 == waitpid(pid, &(info->retval), WNOHANG)) {
        kill(-pid, SIGKILL); // failed to finish after 500ms; kill it
        usleep(300000);
      }
      break;
    }
  }

  // Close the read ends of the pipes
  close(stdout_pipe[0]), close(stderr_pipe[0]);
  close(tfd);
  atomic_fetch_and(&bmp[pid / 64], ~(1ULL << (pid % 64)));
  info->stdout_sz = out_nread;
  info->stderr_sz = err_nread;
  if (atomic_fetch_sub_explicit(
      info->_grp_ctr, WIFEXITED(info->retval) ? 9999 : 1, memory_order_relaxed) < 0)
    info->retval = 9999; // magic number for "lost to competitor in group"
  // A group finishes together :)
  // All signal -> ctr reaches 0;
  // Some finishes -> ctr -= 9999 and therefore <= 0
  while (atomic_load_explicit(info->_grp_ctr, memory_order_relaxed) > 0)
    sleep(1);
}

void* run_one_pthread(void* _a) {
  run_one(_a);
  return NULL;
}

void run_print(const struct RunInfo *info, FILE* file, _Bool oneline) {
  // static pthread_mutex_t mtx = PTHREAD_MUTEX_INITIALIZER;
  if (!file) return;
  flockfile(file);
  if (!oneline) fprintf(file, "## ");
  for (size_t i = 0; i < info->argc; ++i)
    fprintf(file, "%s ", info->argv[i]);
  fprintf(file,
          oneline ? "%zusec %zuKB "
                  : "\nDuration: %lu seconds\nPeak Memory: %zuKB\nExit: ",
          info->duration, info->peak_mem);
  if (info->duration >= info->timelim)
    fputs("timeout\n", file);
  else if (info->peak_mem >= info->memlim_kb)
    fputs("memout\n", file);
  else if (info->retval == 9999)
    fputs("underperformed\n", file);
  else if (WIFEXITED(info->retval))
    fprintf(file, "status %d\n", WEXITSTATUS(info->retval));
  else fprintf(file, "signal %d\n", WTERMSIG(info->retval));
  fflush(file);
  if (oneline) {
    funlockfile(file);
    return;
  }
  fprintf(file, "MemLim %zuKB, TimeLim %zus\n", info->memlim_kb, info->timelim);
  fprintf(file, "\n\n### Standard Output\n");
  fwrite(info->stdout_, info->stdout_sz, 1, file);
  fprintf(file, "\n\n### Standard Error\n");
  fwrite(info->stderr_, info->stderr_sz, 1, file);
  fprintf(file, "\n-------------------------------------------\n\n");
  funlockfile(file);
}

void run_group(struct RunInfo info[], size_t n, FILE *logsmall, FILE *logbig) {
  atomic_long ctr = n;
  pthread_t thrd[n];
  for (size_t i = 1; i < n; ++i) {
    info[i]._grp_ctr = &ctr;
    pthread_create(&thrd[i], NULL, run_one_pthread, info + i);
  }
  info[0]._grp_ctr = &ctr;
  run_one(info);
  run_print(info, stdout, 1);
  if (logsmall) run_print(info, logsmall, 1);
  if (logbig) run_print(info, logbig, 0);
  for (size_t i = 1; i < n; ++i) {
    pthread_join(thrd[i], NULL);
    run_print(info + i, stdout, 1);
    if (logsmall) run_print(info + i, logsmall, 1);
    if (logbig) run_print(info + i, logbig, 0);
  }
}

void* run_group_pthread(void* _a) {
  sigset_t s; sigemptyset(&s);
  sigaddset(&s, SIGINT);
  sigaddset(&s, SIGHUP);
  sigaddset(&s, SIGTERM);
  pthread_sigmask(SIG_BLOCK, &s, NULL);
  struct RunGroupPthread *a = _a;
  run_group(a->info, a->n, a->logsmall, a->logbig);
  for (size_t i = 0; i < a->n; ++i) {
    if (a->slotcnt != NULL && a->info[i].numa_node != 0)
      atomic_fetch_sub_explicit(a->slotcnt + a->info[i].numa_node, 1,
                                memory_order_relaxed);
    free(a->info[i].stdout_), free(a->info[i].stderr_), free(a->info[i].argv);
  }
  if (a->slotcnt != NULL)
    atomic_fetch_add_explicit(a->slotcnt, (long)a->n, memory_order_relaxed);
  free(a->argbuf);
  free(_a);
  return NULL;
}

// Each "\0" marks end of parameter; "\0\0" marks end of command,
// returns pointer to the char after "\0\0";
// `info` must outlive `str`
const char *run_from_str(struct RunInfo *info, const char *str) {
  memset(info, 0, sizeof(*info));
  const char *p = str;
  size_t argc = 0;
  while (*p) {
    ++argc;
    p += strlen(p) + 1;
  }
  if (argc == 0) return p + 1;
  info->argv = calloc(argc + 1, sizeof(char *));
  assert(info->argv);
  info->argc = argc;
  p = str;
  for (size_t i = 0; i < argc; ++i) {
    info->argv[i] = p;
    p += strlen(p) + 1;
  }
  info->program = info->argv[0];
  return p + 1;
}

// "\0\0\0" marks end of group; last "\0\0\0" must NOT be skipped;
// reads nr_run for size of info array and writes it with actual populated count;
// returns pointer to the char after "\0\0\0"
// `info` must outlive `str`
const char *run_group_from_str(struct RunInfo *info, size_t *nr_run,
                               const char *str) {
  size_t cap = *nr_run, n = 0;
  while (*str) {
    if (n == cap) {*nr_run = cap + 1; return str;}
    str = run_from_str(info + n, str);
    ++n;
  }
  *nr_run = n;
  return str + 1;
}

// from config to running, no fuss
const char *run_group_ez(const char *grpstr, size_t sz, atomic_long *slotcnt,
                         size_t timelim, size_t memlim, FILE *small,
                         FILE *large, size_t maxnuma) {
  const char *grpend = memmem(grpstr, sz, "\0\0", 3);
  if (grpend == NULL) return NULL;
  grpend += 3;
  char *argbuf = malloc(grpend - grpstr); // owned by thread
  assert(argbuf);
  memcpy(argbuf, grpstr, grpend - grpstr);

  struct RunGroupPthread *g =
      malloc(16 * sizeof(struct RunInfo) + sizeof(struct RunGroupPthread));
  assert(g);
  size_t nprg = 16;
  const char *parsed_end = run_group_from_str(g->info, &nprg, argbuf);
  // Refuse any group > 16 commands; TODO: make limit configurable
  if (nprg == 0 || nprg > 16 || parsed_end != argbuf + (grpend - grpstr)) {
    size_t nfree = nprg > 16 ? 16 : nprg;
    for (size_t i = 0; i < nfree; ++i)
      free(g->info[i].argv);
    free(argbuf), free(g);
    return grpend;
  }

  for (size_t i = 0; i < nprg; ++i) {
    g->info[i].timelim = timelim;
    g->info[i].memlim_kb = memlim;
    if (maxnuma == 0)
      continue;
    size_t min_numa = 1;
    long min_load = atomic_load_explicit(slotcnt + 1, memory_order_relaxed);
    for (size_t j = 2; j <= maxnuma; ++j) {
      long load = atomic_load_explicit(slotcnt + j, memory_order_relaxed);
      if (load < min_load) {
        min_numa = j;
        min_load = load;
      }
    }
    g->info[i].numa_node = min_numa;
    atomic_fetch_add_explicit(slotcnt + min_numa, 1, memory_order_relaxed);
  }
  g->n = nprg, g->slotcnt = slotcnt;
  g->logsmall = small, g->logbig = large;
  g->argbuf = argbuf;

  pthread_t thrd;
  if (pthread_create(&thrd, NULL, run_group_pthread, g) != 0)
    perror("pthread_create");
  atomic_fetch_sub_explicit(slotcnt, (long)nprg, memory_order_relaxed);
  if (pthread_detach(thrd) != 0)
    perror("pthread_detach");
  return grpend;
}
