#ifndef BATCHRUNNER_H
#define BATCHRUNNER_H
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/types.h>

#define RUN_QUEUE_CAP 2048
#define RUN_GROUP_MAX 16

struct RunGroup {
  char *argbuf;
  size_t nr_run;
  size_t nr_running;   // runner thread only
  size_t nr_returned;  // main thread only
  bool won;            // runner thread only
};

struct RunInfo {
  // Ownership follows main -> pending -> runner -> finished -> main.
  struct RunGroup *group;
  const char *program;
  char **argv;
  size_t argc;
  unsigned group_pos;

  // Runner-owned process state.
  pid_t pid;
  int stdout_fd, stderr_fd;
  unsigned numa_node;  // 0 disables binding; otherwise node + 1
  unsigned terminating;
  uint64_t started_ns, signal_ns;

  // Result fields returned to the main thread.
  int retval;
  uint64_t duration;
  size_t peak_mem;
  bool timed_out, mem_out, lost;
  char *stdout_, *stderr_;
  size_t stdout_sz, stderr_sz, stdout_cap, stderr_cap;
};

struct RunQueue {
  _Alignas(64) atomic_size_t head;
  _Alignas(64) atomic_size_t tail;
  _Alignas(64) struct RunInfo item[RUN_QUEUE_CAP];
};

extern struct RunQueue run_pending;
extern struct RunQueue run_finished;
extern atomic_bool run_stop;
extern size_t run_nr_worker;
extern size_t run_timelim;
extern size_t run_memlim_kb;
extern size_t run_nr_numa;
extern bool run_capture_output;

void run_setup_handler(void);
void *run_runner(void *unused);
size_t run_enqueue_group(const char *grpstr, size_t grpsz,
                            const char *chkpt, size_t chkpt_sz);
void run_print(const struct RunInfo *info, FILE *file, bool oneline);

#endif
