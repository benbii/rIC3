#include "run-info.h"
#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <netdb.h>
#include <poll.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

// maybe make it `send_exact`
static int send_exact(int sock, const void *p, size_t left) {
  const char *c = p;
  while (left > 0) {
    ssize_t n = send(sock, c, left, MSG_NOSIGNAL);
    if (n < 0 && errno == EINTR)
      continue;
    if (n <= 0)
      return -1;
    c += n;
    left -= n;
  }
  return 0;
}

// -w LOCAL_WORKER_THRESH -t TIMELIM -m MEMLIM -n MAX_NUMA_NODE
// -l SUCCINCT_LOG -L VERBOSE_LOG TASK_FILE
int run_local_main(int argc, const char* argv[]) {
  size_t timelim = 3600, maxnuma = 0, memlim = 10 << 20;
  long worker_thresh = 16;
  FILE *small = NULL, *large = NULL;
  for (int i = 1; i < argc - 1; i += 2) {
    if (i + 1 >= argc - 1)
      exit(fprintf(stderr, "missing value for %s\n", argv[i]));
    if (strcmp(argv[i], "-w") == 0)
      worker_thresh = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-t") == 0)
      timelim = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-n") == 0)
      maxnuma = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-m") == 0)
      memlim = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-l") == 0)
      small = fopen(argv[i + 1], "a");
    else if (strcmp(argv[i], "-L") == 0)
      large = fopen(argv[i + 1], "a");
    else
      exit(fprintf(stderr, "unknown arg %s\n", argv[i]));
  }

  int x = open(argv[argc - 1], O_RDONLY);
  if (x < 0)
    return perror("task file open"), 1;
  struct stat st;
  if (fstat(x, &st) != 0)
    return perror("task file fstat"), 2;
  const char *str = mmap(NULL, st.st_size, PROT_READ, MAP_SHARED, x, 0);
  if (str == MAP_FAILED)
    return perror("mmap"), 3;
  // Sanity check on last 3 char of `str`, or all hell break free
  if (str[st.st_size - 1] || str[st.st_size - 2] || str[st.st_size - 3])
    exit(fputs("must end in 3 NULLs\n", stderr));
  if (memmem(str, st.st_size, "\0\0\0", 4) != NULL)
    exit(fputs("4 consecutive \\0 found\n", stderr));

  atomic_long slotcnt[maxnuma + 1];
  for (size_t i = 0; i <= maxnuma; ++i)
    atomic_init(slotcnt + i, 0);
  atomic_store_explicit(slotcnt, worker_thresh, memory_order_relaxed);
  run_setup_handler();
  const char *p = str;
  // Local running logic looks simple:
  // while end of file content str not reached:
  //   if nr. of running workers >= WORKER_THRESH
  //     wait till some jobs finish so running workers < threshold
  //   parses and starts one group of jobs
  while (p < str + st.st_size) {
    while (atomic_load_explicit(slotcnt, memory_order_relaxed) <= 0)
      usleep(500000); // 500ms negligible in long running tasks
    const char *next = run_group_ez(p, str + st.st_size - p, slotcnt,
                                    timelim, memlim, small, large, maxnuma);
    if (next == NULL)
      exit(fputs("malformed task file\n", stderr));
    p = next;
  }

  while (atomic_load_explicit(slotcnt, memory_order_relaxed) < worker_thresh)
    sleep(1);
  munmap((void*)str, st.st_size);
  return 0;
}

int run_daemon_main(int argc, const char* argv[]) {
  size_t timelim = 3600, maxnuma = 0, memlim = 10 << 20;
  long worker_thresh = 16;
  uint64_t secret = 0x409f143dd97f62b7;
  const char *addr = "localhost", *port = "9559";
  FILE *small = NULL, *large = NULL;
  for (int i = 1; i < argc; i += 2) {
    if (strcmp(argv[i], "-w") == 0)
      worker_thresh = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-t") == 0)
      timelim = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-n") == 0)
      maxnuma = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-m") == 0)
      memlim = atol(argv[i + 1]);
    else if (strcmp(argv[i], "-l") == 0)
      small = fopen(argv[i + 1], "a");
    else if (strcmp(argv[i], "-L") == 0)
      large = fopen(argv[i + 1], "a");
    else if (strcmp(argv[i], "-a") == 0)
      addr = argv[i + 1];
    else if (strcmp(argv[i], "-p") == 0)
      port = argv[i + 1];
    else if (strcmp(argv[i], "-S") == 0)
      secret = strtoull(argv[i + 1], NULL, 0);
    else
      return fprintf(stderr, "unknown arg %s\n", argv[i]);
  }
  if (worker_thresh <= 0) worker_thresh = 1;

  atomic_long slotcnt[maxnuma + 1];
  for (size_t i = 0; i <= maxnuma; ++i)
    atomic_init(slotcnt + i, 0);
  atomic_store_explicit(slotcnt, worker_thresh, memory_order_relaxed);
  run_setup_handler();
  char* groupstr_buf = malloc(32768);
  assert(groupstr_buf);
  size_t groupstr_size = 0;
  struct addrinfo hints = {.ai_socktype = SOCK_STREAM}, *res = NULL, *rp = NULL;
  int sock = -1, gai = getaddrinfo(addr, port, &hints, &res);
  if (gai != 0)
    return fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(gai));
  // leak the result lol

  while (1) {
    for (rp = res; rp != NULL; rp = rp->ai_next) {
      sock = socket(rp->ai_family, rp->ai_socktype | SOCK_CLOEXEC, rp->ai_protocol);
      if (sock < 0) continue;
      if (connect(sock, rp->ai_addr, rp->ai_addrlen) == 0)
        break;
      close(sock);
      sock = -1;
    }
    if (sock == -1) {
      sleep(5); // try connecting once per 5s
      continue;
    }
    puts("connected to server");
    uint64_t peer_secret;
    if (recv(sock, &peer_secret, 8, MSG_WAITALL) != 8 || peer_secret != secret)
      goto close_connection;

    groupstr_size = 0;
    int slot = (int)atomic_load_explicit(slotcnt, memory_order_relaxed);
    if (send_exact(sock, &slot, 4) != 0)
      goto close_connection;

    ssize_t recv_ret;
    while (groupstr_size < 32768) {
      recv_ret = recv(sock, groupstr_buf + groupstr_size,
                      32768 - groupstr_size, 0);
      if (recv_ret < 0 && errno == EINTR)
        continue;
      if (recv_ret <= 0)
        goto close_connection;
      groupstr_size += recv_ret;
      // bad input; break the recv loop to actively terminate the connection
      if (memmem(groupstr_buf, groupstr_size, "\0\0\0", 4) != NULL)
        break;

      while (1) {
        const char* p = run_group_ez(groupstr_buf, groupstr_size, slotcnt,
                                     timelim, memlim, small, large, maxnuma);
        if (p == NULL)
          break;
        groupstr_size -= p - groupstr_buf;
        // non optimal string op; shouldn't be a bottleneck (<32K, in L1)
        memmove(groupstr_buf, p, groupstr_size);

        slot = (int)atomic_load_explicit(slotcnt, memory_order_relaxed);
        if (slot <= 0) {
          // Notify "job server" that this compute node is full
          if (send_exact(sock, &slot, 4) != 0)
            goto close_connection;
          while (atomic_load_explicit(slotcnt, memory_order_relaxed) <= 0)
            usleep(500000); // 500ms negligible in long running tasks
          slot = (int)atomic_load_explicit(slotcnt, memory_order_relaxed);
          if (send_exact(sock, &slot, 4) != 0)
            goto close_connection;
        }
      } // while (p != NULL)

      // Acknowledge data read or notify server this node is free
      slot = (int)atomic_load_explicit(slotcnt, memory_order_relaxed);
      if (send_exact(sock, &slot, 4) != 0)
        goto close_connection;
    } // while (recv_ret > 0)

    // bad input or recv finishes; terminate connection here
close_connection:
    close(sock);
    groupstr_size = 0;
    puts("connection to server closed");
    sleep(30); // sleeps longer when connection terminates
  } // while (1)
}

int run_submit_main(int argc, const char* argv[]) {
  if (argc < 4 || argc > 5)
    return fputs("usage: run-info submit ADDR PORT TASK_FILE [SECRET]\n", stderr);
  const char *addr = argv[1], *port = argv[2];
  uint64_t secret = argc > 4 ? strtoull(argv[4], NULL, 0) : 0x409f143dd97f62b7;
  int x = open(argv[3], O_RDONLY), one = 1;
  if (x < 0)
    return perror("task file open"), 1;
  struct stat st;
  if (fstat(x, &st) != 0)
    return perror("task file fstat"), 2;
  const char *str = mmap(NULL, st.st_size, PROT_READ, MAP_SHARED, x, 0);
  if (str == MAP_FAILED)
    return perror("mmap"), 3;
  // Sanity check on last 3 char of `str`, or all hell break free
  if (str[st.st_size - 1] || str[st.st_size - 2] || str[st.st_size - 3])
    exit(fputs("must end in 3 NULLs\n", stderr));
  if (memmem(str, st.st_size, "\0\0\0", 4) != NULL)
    exit(fputs("4 consecutive \\0 found\n", stderr));

  struct addrinfo hints = {0}, *res = NULL, *rp = NULL;
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;
  int gai = getaddrinfo(addr, port, &hints, &res);
  if (gai != 0)
    return fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(gai));
  int listenfd = -1;
  for (rp = res; rp != NULL; rp = rp->ai_next) {
    listenfd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
    if (listenfd < 0) continue;
    setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    if (bind(listenfd, rp->ai_addr, rp->ai_addrlen) == 0 &&
        listen(listenfd, 32) == 0)
      break;
    close(listenfd);
    listenfd = -1;
  }
  freeaddrinfo(res);
  if (listenfd < 0)
    return fputs("listen failed\n", stderr);
  printf("listening to %s:%s\n", addr, port);

  struct Leftover {
    uint8_t slotbuf[3], slotbuf_n;
  };
  struct Leftover lefts[64] = {0};
  struct pollfd pollfds[65];
  memset(pollfds, 0, sizeof(pollfds));
  size_t nr_client = 0;
  pollfds[0].fd = listenfd;
  pollfds[0].events = POLLIN;

  const char *grp = str;
  // poll loop
  while (grp < str + st.st_size) {
    if (poll(pollfds, nr_client + 1, -1) < 0) {
      if (errno == EINTR) continue;
      return perror("poll"), 4;
    }

    if (pollfds[0].revents & POLLIN) {
      int cfd = accept(listenfd, NULL, NULL);
      if (cfd >= 0) {
        setsockopt(cfd, SOL_SOCKET, SO_KEEPALIVE, &one, sizeof(one));
        if (nr_client == 64 || send_exact(cfd, &secret, 8) != 0) {
          close(cfd);
        } else {
          memset(&lefts[nr_client], 0, sizeof(lefts[nr_client]));
          ++nr_client;
          pollfds[nr_client].fd = cfd;
          pollfds[nr_client].events = POLLIN;
          pollfds[nr_client].revents = 0;
          printf("connection accepted: %d, nr %zu\n", cfd, nr_client);
        }
      }
    }

    // blindly send a group to a client with nr_left > 0;
    // accept a possible overcommit by 0~15 threads
    unsigned char recv_buf[1024];
    for (size_t i = 1; i <= nr_client; ++i) {
      if (!(pollfds[i].revents & (POLLIN | POLLERR | POLLHUP | POLLNVAL)))
        continue;
      if (pollfds[i].revents & (POLLERR | POLLHUP | POLLNVAL))
        goto close_client;

      struct Leftover *c = &lefts[i - 1];
      memcpy(recv_buf, c->slotbuf, 4);
      ssize_t r = recv(pollfds[i].fd, recv_buf + c->slotbuf_n,
                       sizeof(recv_buf) - c->slotbuf_n, 0);
      if (r < 0 && errno == EINTR) continue;
      if (r <= 0) {
close_client:
        close(pollfds[i].fd);
        printf("closed: %d, nr %zu\n", pollfds[i].fd, nr_client - 1);
        pollfds[i] = pollfds[nr_client];
        --i, --nr_client;
        lefts[i] = lefts[nr_client];
        continue;
      }
      r += c->slotbuf_n;
      // *c = *(struct Leftover*)(recv_buf + r - r % 4);
      if (c->slotbuf_n)
        memcpy(c->slotbuf, recv_buf + r - r % 4, 4);
      c->slotbuf_n = r % 4;
      if (r < 4) continue;

      int slot;
      memcpy(&slot, recv_buf + r - r % 4 - 4, 4);
      printf("%d has %d slots\n", pollfds[i].fd, slot);
      if (slot <= 0) continue;
      const char *nxt = memmem(grp, str + st.st_size - grp, "\0\0", 3);
      assert(nxt != NULL);
      nxt += 3;
      if (send_exact(pollfds[i].fd, grp, nxt - grp) != 0)
        goto close_client;
      printf("sent group of %zdB to %d\n", nxt - grp, pollfds[i].fd);
      grp = nxt;
      if (grp >= str + st.st_size)
        break;
    }
  }
  for (size_t i = 1; i <= nr_client; ++i)
    close(pollfds[i].fd);
  close(listenfd);
  munmap((void*)str, st.st_size);
  return 0;
}

int main(int argc, const char *argv[]) {
  const char *prog = strrchr(argv[0], '/');
  prog = prog ? prog + 1 : argv[0];
  // launch with either binary name (symlink) or first argument
  if (strcmp(prog, "run-local") == 0)
    return run_local_main(argc, argv);
  if (argc > 1 && strcmp(argv[1], "local") == 0)
    return run_local_main(argc - 1, argv + 1);
  if (strcmp(prog, "run-daemon") == 0)
    return run_daemon_main(argc, argv);
  if (argc > 1 && strcmp(argv[1], "daemon") == 0)
    return run_daemon_main(argc - 1, argv + 1);
  if (strcmp(prog, "run-submit") == 0)
    return run_submit_main(argc, argv);
  if (argc > 1 && strcmp(argv[1], "submit") == 0)
    return run_submit_main(argc - 1, argv + 1);
  return fputs("usage: run-info local|daemon|submit ...\n", stderr);
}
