#include "batchrunner.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static int send_exact(int sock, const void *p, size_t left) {
  const char *c = p;
  while (left > 0) {
    ssize_t n = send(sock, c, left, MSG_NOSIGNAL);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) return -1;
    c += n;
    left -= (size_t)n;
  }
  return 0;
}

static char *load_checkpoint(FILE *small, size_t *size) {
  *size = 0;
  if (!small) return NULL;
  assert(fseek(small, 0, SEEK_END) == 0);
  long end = ftell(small);
  assert(end >= 0);
  assert(fseek(small, 0, SEEK_SET) == 0);
  *size = (size_t)end;
  if (*size == 0) return NULL;
  char *checkpoint = malloc(*size);
  assert(checkpoint);
  assert(fread(checkpoint, *size, 1, small) == 1);
  return checkpoint;
}

static pthread_t start_runner(size_t nr_worker, size_t timelim,
                              size_t memlim_kb, size_t nr_numa,
                              bool capture_output) {
  assert(nr_worker > 0 && nr_worker <= INT_MAX);
  assert(2 * nr_worker + RUN_GROUP_MAX <= RUN_QUEUE_CAP);
  run_nr_worker = nr_worker;
  run_timelim = timelim;
  run_memlim_kb = memlim_kb;
  run_nr_numa = nr_numa;
  run_capture_output = capture_output;
  atomic_init(&run_pending.head, 0);
  atomic_init(&run_pending.tail, 0);
  atomic_init(&run_finished.head, 0);
  atomic_init(&run_finished.tail, 0);
  atomic_init(&run_stop, false);

  // Only the runner reaps.  Children clear this inherited mask before exec.
  sigset_t child_signal;
  sigemptyset(&child_signal);
  sigaddset(&child_signal, SIGCHLD);
  assert(pthread_sigmask(SIG_BLOCK, &child_signal, NULL) == 0);
  run_setup_handler();

  pthread_t thread;
  assert(pthread_create(&thread, NULL, run_runner, NULL) == 0);
  return thread;
}

static size_t pending_count(void) {
  size_t tail = atomic_load_explicit(&run_pending.tail,
                                     memory_order_relaxed);
  size_t head = atomic_load_explicit(&run_pending.head,
                                     memory_order_acquire);
  return tail - head;
}

static size_t drain_finished(FILE *small, FILE *large) {
  size_t count = 0;
  for (;;) {
    size_t head = atomic_load_explicit(&run_finished.head,
                                       memory_order_relaxed);
    size_t tail = atomic_load_explicit(&run_finished.tail,
                                       memory_order_acquire);
    if (head == tail) break;
    struct RunInfo info =
        run_finished.item[head % RUN_QUEUE_CAP];
    atomic_store_explicit(&run_finished.head, head + 1,
                          memory_order_release);

    run_print(&info, stdout, true);
    run_print(&info, small, true);
    run_print(&info, large, false);
    free(info.stdout_);
    free(info.stderr_);
    free(info.argv);
    assert(info.group->nr_returned < info.group->nr_run);
    if (++info.group->nr_returned == info.group->nr_run) {
      assert(info.group->nr_running == 0);
      free(info.group->argbuf);
      free(info.group);
    }
    ++count;
  }
  return count;
}

// -w WORKERS -t TIMELIM -m MEMLIM -n NR_NUMA
// -l SUCCINCT_LOG [-L VERBOSE_LOG] TASK_FILE
static int run_local_main(int argc, const char *argv[]) {
  size_t timelim = 3600, nr_numa = 0, memlim = 10 << 20;
  size_t nr_worker = 16;
  FILE *small = NULL, *large = NULL;
  for (int i = 1; i < argc - 1; i += 2) {
    assert(i + 1 < argc - 1);
    if (strcmp(argv[i], "-w") == 0)
      nr_worker = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-t") == 0)
      timelim = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-n") == 0)
      nr_numa = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-m") == 0)
      memlim = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-l") == 0) {
      small = fopen(argv[i + 1], "a+");
      assert(small);
    } else if (strcmp(argv[i], "-L") == 0) {
      large = fopen(argv[i + 1], "a");
      assert(large);
    } else {
      assert(false && "unknown argument");
    }
  }
  assert(argc >= 2 && nr_worker > 0 && timelim > 0 && memlim > 0);

  int taskfd = open(argv[argc - 1], O_RDONLY | O_CLOEXEC);
  assert(taskfd >= 0);
  struct stat st;
  assert(fstat(taskfd, &st) == 0 && st.st_size >= 3);
  const char *tasks = mmap(NULL, (size_t)st.st_size, PROT_READ,
                           MAP_PRIVATE, taskfd, 0);
  assert(tasks != MAP_FAILED);
  close(taskfd);
  assert(tasks[st.st_size - 1] == 0 && tasks[st.st_size - 2] == 0 &&
         tasks[st.st_size - 3] == 0);
  assert(memmem(tasks, (size_t)st.st_size, "\0\0\0", 4) == NULL);

  size_t checkpoint_size;
  char *checkpoint = load_checkpoint(small, &checkpoint_size);
  pthread_t runner = start_runner(nr_worker, timelim, memlim, nr_numa,
                                  large != NULL);

  const char *p = tasks, *task_end = tasks + st.st_size;
  size_t submitted = 0, completed = 0;
  while (p < task_end) {
    while (pending_count() >= 2 * nr_worker ||
           pending_count() + RUN_GROUP_MAX > RUN_QUEUE_CAP) {
      completed += drain_finished(small, large);
      sleep(1);
    }
    const char *next = memmem(p, (size_t)(task_end - p), "\0\0", 3);
    assert(next);
    next += 3;
    submitted += run_enqueue_group(p, (size_t)(next - p), checkpoint,
                                      checkpoint_size);
    p = next;
  }

  while (completed < submitted) {
    completed += drain_finished(small, large);
    if (completed < submitted) sleep(1);
  }
  atomic_store_explicit(&run_stop, true, memory_order_release);
  assert(pthread_join(runner, NULL) == 0);
  assert(drain_finished(small, large) == 0);

  free(checkpoint);
  assert(munmap((void *)tasks, (size_t)st.st_size) == 0);
  if (small) fclose(small);
  if (large) fclose(large);
  return 0;
}

static int run_daemon_main(int argc, const char *argv[]) {
  size_t timelim = 3600, nr_numa = 0, memlim = 10 << 20;
  size_t nr_worker = 16;
  uint64_t secret = 0x409f143dd97f62b7;
  const char *addr = "localhost", *port = "9559";
  FILE *small = NULL, *large = NULL;
  for (int i = 1; i < argc; i += 2) {
    assert(i + 1 < argc);
    if (strcmp(argv[i], "-w") == 0)
      nr_worker = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-t") == 0)
      timelim = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-n") == 0)
      nr_numa = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-m") == 0)
      memlim = (size_t)atol(argv[i + 1]);
    else if (strcmp(argv[i], "-l") == 0) {
      small = fopen(argv[i + 1], "a+");
      assert(small);
    } else if (strcmp(argv[i], "-L") == 0) {
      large = fopen(argv[i + 1], "a");
      assert(large);
    } else if (strcmp(argv[i], "-a") == 0)
      addr = argv[i + 1];
    else if (strcmp(argv[i], "-p") == 0)
      port = argv[i + 1];
    else if (strcmp(argv[i], "-S") == 0)
      secret = strtoull(argv[i + 1], NULL, 0);
    else
      assert(false && "unknown argument");
  }
  assert(nr_worker > 0 && timelim > 0 && memlim > 0);

  struct addrinfo hints = {.ai_socktype = SOCK_STREAM}, *res = NULL;
  int gai = getaddrinfo(addr, port, &hints, &res);
  assert(gai == 0);
  size_t checkpoint_size;
  char *checkpoint = load_checkpoint(small, &checkpoint_size);
  (void)checkpoint;  // Permanently owned by this daemon main loop.
  pthread_t runner = start_runner(nr_worker, timelim, memlim, nr_numa,
                                  large != NULL);
  (void)runner;

  char *groupbuf = malloc(32768);
  assert(groupbuf);
  for (;;) {
    int sock = -1;
    for (struct addrinfo *rp = res; rp; rp = rp->ai_next) {
      sock = socket(rp->ai_family, rp->ai_socktype | SOCK_CLOEXEC,
                    rp->ai_protocol);
      if (sock < 0) continue;
      if (connect(sock, rp->ai_addr, rp->ai_addrlen) == 0) break;
      close(sock);
      sock = -1;
    }
    if (sock < 0) {
      for (int i = 0; i < 5; ++i) {
        (void)drain_finished(small, large);
        sleep(1);
      }
      continue;
    }

    puts("connected to server");
    uint64_t peer_secret;
    if (recv(sock, &peer_secret, 8, MSG_WAITALL) != 8 ||
        peer_secret != secret)
      goto close_connection;

    size_t groupbuf_size = 0;
    size_t queued = pending_count();
    size_t headroom = queued >= 2 * nr_worker ? 0 : 2 * nr_worker - queued;
    int slot = (int)(headroom > nr_worker ? nr_worker : headroom);
    if (send_exact(sock, &slot, sizeof(slot)) != 0)
      goto close_connection;
    bool paused = slot <= 0;

    for (;;) {
      (void)drain_finished(small, large);
      queued = pending_count();
      if (queued >= 2 * nr_worker) {
        if (!paused) {
          slot = 0;
          if (send_exact(sock, &slot, sizeof(slot)) != 0)
            goto close_connection;
          paused = true;
        }
        sleep(1);
        continue;
      }

      if (paused) {
        headroom = 2 * nr_worker - queued;
        slot = (int)(headroom > nr_worker ? nr_worker : headroom);
        if (send_exact(sock, &slot, sizeof(slot)) != 0)
          goto close_connection;
        paused = false;
      }

      while (queued < 2 * nr_worker) {
        if (memmem(groupbuf, groupbuf_size, "\0\0\0", 4) != NULL)
          goto close_connection;
        const char *next = memmem(groupbuf, groupbuf_size, "\0\0", 3);
        if (!next) break;
        next += 3;
        (void)run_enqueue_group(groupbuf, (size_t)(next - groupbuf),
                                   checkpoint, checkpoint_size);
        groupbuf_size -= (size_t)(next - groupbuf);
        memmove(groupbuf, next, groupbuf_size);

        queued = pending_count();
        headroom = queued >= 2 * nr_worker ? 0 : 2 * nr_worker - queued;
        slot = (int)(headroom > nr_worker ? nr_worker : headroom);
        if (send_exact(sock, &slot, sizeof(slot)) != 0)
          goto close_connection;
        paused = slot <= 0;
        if (paused) break;
      }
      if (paused) continue;
      if (groupbuf_size == 32768) goto close_connection;

      struct pollfd pfd = {.fd = sock, .events = POLLIN};
      int ready = poll(&pfd, 1, 1000);
      if (ready < 0 && errno == EINTR) continue;
      if (ready < 0) goto close_connection;
      if (ready == 0) continue;
      if (!(pfd.revents & POLLIN)) goto close_connection;

      ssize_t received = recv(sock, groupbuf + groupbuf_size,
                              32768 - groupbuf_size, MSG_DONTWAIT);
      if (received < 0 && (errno == EINTR || errno == EAGAIN ||
                           errno == EWOULDBLOCK))
        continue;
      if (received <= 0) goto close_connection;
      groupbuf_size += (size_t)received;
    }

close_connection:
    close(sock);
    puts("connection to server closed");
    for (int i = 0; i < 30; ++i) {
      (void)drain_finished(small, large);
      sleep(1);
    }
  }
}

static int run_submit_main(int argc, const char *argv[]) {
  if (argc < 4 || argc > 5)
    return fputs("usage: batchrunner submit ADDR PORT TASK_FILE [SECRET]\n",
                 stderr);
  const char *addr = argv[1], *port = argv[2];
  uint64_t secret = argc > 4 ? strtoull(argv[4], NULL, 0)
                             : 0x409f143dd97f62b7;
  int taskfd = open(argv[3], O_RDONLY | O_CLOEXEC), one = 1;
  assert(taskfd >= 0);
  struct stat st;
  assert(fstat(taskfd, &st) == 0 && st.st_size >= 3);
  const char *tasks = mmap(NULL, (size_t)st.st_size, PROT_READ,
                           MAP_PRIVATE, taskfd, 0);
  assert(tasks != MAP_FAILED);
  close(taskfd);
  assert(tasks[st.st_size - 1] == 0 && tasks[st.st_size - 2] == 0 &&
         tasks[st.st_size - 3] == 0);
  assert(memmem(tasks, (size_t)st.st_size, "\0\0\0", 4) == NULL);

  struct addrinfo hints = {
      .ai_family = AF_UNSPEC,
      .ai_socktype = SOCK_STREAM,
      .ai_flags = AI_PASSIVE,
  };
  struct addrinfo *res = NULL;
  assert(getaddrinfo(addr, port, &hints, &res) == 0);
  int listenfd = -1;
  for (struct addrinfo *rp = res; rp; rp = rp->ai_next) {
    listenfd = socket(rp->ai_family, rp->ai_socktype | SOCK_CLOEXEC,
                      rp->ai_protocol);
    if (listenfd < 0) continue;
    (void)setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    if (bind(listenfd, rp->ai_addr, rp->ai_addrlen) == 0 &&
        listen(listenfd, 32) == 0)
      break;
    close(listenfd);
    listenfd = -1;
  }
  freeaddrinfo(res);
  assert(listenfd >= 0);
  printf("listening to %s:%s\n", addr, port);

  struct Leftover {
    uint8_t slotbuf[3], slotbuf_n;
  } lefts[64] = {0};
  struct pollfd pollfds[65] = {0};
  size_t nr_client = 0;
  pollfds[0].fd = listenfd;
  pollfds[0].events = POLLIN;

  const char *group = tasks, *task_end = tasks + st.st_size;
  while (group < task_end) {
    int ready = poll(pollfds, nr_client + 1, -1);
    if (ready < 0 && errno == EINTR) continue;
    assert(ready >= 0);

    if (pollfds[0].revents & POLLIN) {
      int client = accept4(listenfd, NULL, NULL, SOCK_CLOEXEC);
      if (client >= 0) {
        (void)setsockopt(client, SOL_SOCKET, SO_KEEPALIVE, &one, sizeof(one));
        if (nr_client == 64 || send_exact(client, &secret, 8) != 0) {
          close(client);
        } else {
          memset(&lefts[nr_client], 0, sizeof(lefts[nr_client]));
          ++nr_client;
          pollfds[nr_client].fd = client;
          pollfds[nr_client].events = POLLIN;
          pollfds[nr_client].revents = 0;
          printf("connection accepted: %d, nr %zu\n", client, nr_client);
        }
      }
    }

    unsigned char recv_buf[1024];
    for (size_t i = 1; i <= nr_client; ++i) {
      if (!(pollfds[i].revents & (POLLIN | POLLERR | POLLHUP | POLLNVAL)))
        continue;
      if (pollfds[i].revents & (POLLERR | POLLHUP | POLLNVAL))
        goto close_client;

      struct Leftover *left = &lefts[i - 1];
      memcpy(recv_buf, left->slotbuf, left->slotbuf_n);
      ssize_t n = recv(pollfds[i].fd, recv_buf + left->slotbuf_n,
                       sizeof(recv_buf) - left->slotbuf_n, 0);
      if (n < 0 && errno == EINTR) continue;
      if (n <= 0) {
close_client:
        close(pollfds[i].fd);
        printf("closed: %d, nr %zu\n", pollfds[i].fd, nr_client - 1);
        pollfds[i] = pollfds[nr_client];
        --i;
        --nr_client;
        lefts[i] = lefts[nr_client];
        continue;
      }

      n += left->slotbuf_n;
      left->slotbuf_n = (uint8_t)(n % 4);
      if (left->slotbuf_n)
        memcpy(left->slotbuf, recv_buf + n - left->slotbuf_n,
               left->slotbuf_n);
      if (n < 4) continue;

      int slot;
      memcpy(&slot, recv_buf + n - left->slotbuf_n - 4, 4);
      printf("%d has %d slots\n", pollfds[i].fd, slot);
      if (slot <= 0) continue;
      const char *next = memmem(group, (size_t)(task_end - group),
                                "\0\0", 3);
      assert(next);
      next += 3;
      if (send_exact(pollfds[i].fd, group, (size_t)(next - group)) != 0)
        goto close_client;
      printf("sent group of %zdB to %d\n", next - group, pollfds[i].fd);
      group = next;
      if (group >= task_end) break;
    }
  }

  for (size_t i = 1; i <= nr_client; ++i) close(pollfds[i].fd);
  close(listenfd);
  assert(munmap((void *)tasks, (size_t)st.st_size) == 0);
  return 0;
}

int main(int argc, const char *argv[]) {
  const char *program = strrchr(argv[0], '/');
  program = program ? program + 1 : argv[0];
  if (strcmp(program, "run-local-rev") == 0)
    return run_local_main(argc, argv);
  if (strcmp(program, "run-daemon-rev") == 0)
    return run_daemon_main(argc, argv);
  if (strcmp(program, "run-submit-rev") == 0)
    return run_submit_main(argc, argv);
  if (argc > 1 && strcmp(argv[1], "local") == 0)
    return run_local_main(argc - 1, argv + 1);
  if (argc > 1 && strcmp(argv[1], "daemon") == 0)
    return run_daemon_main(argc - 1, argv + 1);
  if (argc > 1 && strcmp(argv[1], "submit") == 0)
    return run_submit_main(argc - 1, argv + 1);
  return fputs("usage: batchrunner local|daemon|submit ...\n", stderr);
}
