#define _GNU_SOURCE
#include "counters.h"
#include <string.h>
#include <time.h>

#if defined(__APPLE__)
#include <libproc.h>
#include <pthread.h>
#include <pthread/qos.h>
#include <sys/resource.h>
#include <unistd.h>

static int ok;

int vb_counters_init(void)
{
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    struct rusage_info_v4 ri;
    memset(&ri, 0, sizeof ri);
    ok = proc_pid_rusage(getpid(), RUSAGE_INFO_V4, (rusage_info_t *)&ri) == 0 && ri.ri_instructions > 0;
    return ok;
}

uint64_t vb_now_ns(void) { return clock_gettime_nsec_np(CLOCK_UPTIME_RAW); }

void vb_counters_read(int64_t *ins, int64_t *cyc)
{
    struct rusage_info_v4 ri;
    if (ok && proc_pid_rusage(getpid(), RUSAGE_INFO_V4, (rusage_info_t *)&ri) == 0) {
        *ins = (int64_t)ri.ri_instructions;
        *cyc = (int64_t)ri.ri_cycles;
    } else {
        *ins = *cyc = -1;
    }
}

#elif defined(__linux__)
#include <linux/perf_event.h>
#include <sys/syscall.h>
#include <unistd.h>

static int fd_ins = -1, fd_cyc = -1;

static int open_counter(uint64_t config)
{
    struct perf_event_attr a;
    memset(&a, 0, sizeof a);
    a.size = sizeof a;
    a.type = PERF_TYPE_HARDWARE;
    a.config = config;
    a.exclude_kernel = 1;
    a.exclude_hv = 1;
    a.inherit = 0;
    return (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}

int vb_counters_init(void)
{
    fd_ins = open_counter(PERF_COUNT_HW_INSTRUCTIONS);
    fd_cyc = open_counter(PERF_COUNT_HW_CPU_CYCLES);
    return fd_ins >= 0;
}

uint64_t vb_now_ns(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

static int64_t rd(int fd)
{
    uint64_t v;
    if (fd < 0 || read(fd, &v, sizeof v) != (ssize_t)sizeof v) return -1;
    return (int64_t)v;
}

void vb_counters_read(int64_t *ins, int64_t *cyc)
{
    *ins = rd(fd_ins);
    *cyc = rd(fd_cyc);
}

#else
int vb_counters_init(void) { return 0; }
uint64_t vb_now_ns(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}
void vb_counters_read(int64_t *ins, int64_t *cyc) { *ins = *cyc = -1; }
#endif
