#ifndef RUN_INFO_H
#define RUN_INFO_H
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <assert.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>

// construct one with 0 init
struct RunInfo {
  // internal to `run_one` only
  atomic_long *_grp_ctr;
  // configs
  const char* program;
  size_t argc;
  const char** argv;
  size_t memlim_kb, timelim;
  unsigned numa_node;
  // stats
  int retval;
  uint64_t duration;  // in seconds
  size_t peak_mem, stdout_sz, stderr_sz;
  char* stdout_, *stderr_;  // malloced by the function
};

struct RunGroupPthread {
  size_t n;
  FILE *logsmall, *logbig;
  char *argbuf;
  // optional counters: [0] free total slots, [1..] occupied per NUMA node
  atomic_long *slotcnt;
  struct RunInfo info[];
};

size_t get_memory_usage(pid_t pid);
void run_sig_handler(int sig);
void run_setup_handler(void);
void run_one(struct RunInfo* info);
void* run_one_pthread(void* _a);
void run_print(const struct RunInfo *info, FILE* file, _Bool oneline);

void run_group(struct RunInfo info[], size_t n, FILE *logsmall, FILE *logbig);
void* run_group_pthread(void* _a);
const char *run_from_str(struct RunInfo *info, const char *str);
const char *run_group_from_str(struct RunInfo *info, size_t *nr_run,
                               const char *str);
const char *run_group_ez(const char *grpstr, size_t grpsz, atomic_long *slotcnt,
                         size_t timelim, size_t memlim, FILE *small,
                         FILE *large, size_t maxnuma);

#endif
