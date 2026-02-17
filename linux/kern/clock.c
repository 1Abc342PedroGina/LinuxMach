/* SPDX License Indentifier: GPL-2.0 */
/*
 * sched_clock() for unstable CPU clocks
 *
 *  Copyright (C) 2008 Red Hat, Inc., Peter Zijlstra
 *
 *  Updates and enhancements:
 *    Copyright (C) 2008 Red Hat, Inc. Steven Rostedt <srostedt@redhat.com>
 *
 * Based on code by:
 *   Ingo Molnar <mingo@redhat.com>
 *   Guillaume Chazarain <guichaz@gmail.com>
 *
 *
 * What this file implements:
 *
 * cpu_clock(i) provides a fast (execution time) high resolution
 * clock with bounded drift between CPUs. The value of cpu_clock(i)
 * is monotonic for constant i. The timestamp returned is in nanoseconds.
 *
 * ######################### BIG FAT WARNING ##########################
 * # when comparing cpu_clock(i) to cpu_clock(j) for i != j, time can #
 * # go backwards !!                                                  #
 * ####################################################################
 *
 * There is no strict promise about the base, although it tends to start
 * at 0 on boot (but people really shouldn't rely on that).
 *
 * cpu_clock(i)       -- can be used from any context, including NMI.
 * local_clock()      -- is cpu_clock() on the current CPU.
 *
 * sched_clock_cpu(i)
 *
 * How it is implemented:
 *
 * The implementation either uses sched_clock() when
 * !CONFIG_HAVE_UNSTABLE_SCHED_CLOCK, which means in that case the
 * sched_clock() is assumed to provide these properties (mostly it means
 * the architecture provides a globally synchronized highres time source).
 *
 * Otherwise it tries to create a semi stable clock from a mixture of other
 * clocks, including:
 *
 *  - GTOD (clock monotonic)
 *  - sched_clock()
 *  - explicit idle events
 *
 * We use GTOD as base and use sched_clock() deltas to improve resolution. The
 * deltas are filtered to provide monotonicity and keeping it within an
 * expected window.
 *
 * Furthermore, explicit sleep and wakeup hooks allow us to account for time
 * that is otherwise invisible (TSC gets stopped).
 *
 */

#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt

#include <linux/device.h>
#include <linux/clocksource.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/sched.h> /* for spin_unlock_irq() using preempt_count() m68k */
#include <linux/tick.h>
#include <linux/kthread.h>
#include <linux/delay.h>
#include <linux/prandom.h>
#include <linux/cpu.h>

#include "tick-internal.h"
#include <mach/mach_types.h>

#include <kern/spl.h>
#include <kern/sched_prim.h>
#include <kern/thread.h>
#include <kern/clock.h>
#include <kern/host_notify.h>
#include <kern/thread_call.h>
#include <libkern/OSAtomic.h>

#include <IOKit/IOPlatformExpert.h>

#include <machine/commpage.h>
#include <machine/config.h>
#include <machine/machine_routines.h>

#include <mach/mach_traps.h>
#include <mach/mach_time.h>

#include <sys/kdebug.h>
#include <sys/timex.h>
#include <kern/arithmetic_128.h>
#include <os/log.h>
#include <mach/mach_types.h>
#include <linux/device.h>
#include <linux/clocksource.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/sched.h> /* for spin_unlock_irq() using preempt_count() m68k */
#include <linux/tick.h>
#include <linux/kthread.h>
#include <linux/prandom.h>
#include <linux/cpu.h>
#include <linux/clockchips.h>
#include <linux/hrtimer.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/smp.h>
#include <linux/device.h>

#include "tick-internal.h"


#include "tick-internal.h"
#include "timekeeping_internal.h"
#include <kern/host.h>
#include <kern/spl.h>
#include <kern/sched_prim.h>
#include <kern/thread.h>
#include <kern/ipc_host.h>
#include <kern/clock.h>
#include <kern/zalloc.h>

#include <ipc/ipc_types.h>
#include <ipc/ipc_port.h>

#include <mach/mach_traps.h>
#include <mach/mach_time.h>

#include <mach/clock_server.h>
#include <mach/clock_reply.h>

#include <mach/mach_host_server.h>
#include <mach/host_priv_server.h>
#include <libkern/section_keywords.h>
#include <linux/sched/clock.h>
#include "sched.h"
#include <linux/time.h>
#include <linux/hrtimer.h>
#include <linux/timerqueue.h>
#include <linux/rtc.h>
#include <linux/sched/signal.h>
#include <linux/sched/debug.h>
#include <linux/alarmtimer.h>
#include <linux/mutex.h>
#include <linux/platform_device.h>
#include <linux/posix-timers.h>
#include <linux/workqueue.h>
#include <linux/freezer.h>
#include <linux/compat.h>
#include <linux/module.h>
#include <linux/time_namespace.h>

#include "posix-timers.h"

#define CREATE_TRACE_POINTS
#include <trace/events/alarmtimer.h>
#if HIBERNATION && HAS_CONTINUOUS_HWCLOCK
// On ARM64, the hwclock keeps ticking across a normal S2R so we use it to reset the
// system clock after a normal wake. However, on hibernation we cut power to the hwclock,
// so we have to add an offset to the hwclock to compute continuous_time after hibernate resume.
uint64_t hwclock_conttime_offset = 0;
#endif /* HIBERNATION && HAS_CONTINUOUS_HWCLOCK */

#if HIBERNATION_USES_LEGACY_CLOCK || !HAS_CONTINUOUS_HWCLOCK
#define ENABLE_LEGACY_CLOCK_CODE 1
#endif /* HIBERNATION_USES_LEGACY_CLOCK || !HAS_CONTINUOUS_HWCLOCK */

#if HIBERNATION_USES_LEGACY_CLOCK
#include <IOKit/IOHibernatePrivate.h>
#endif /* HIBERNATION_USES_LEGACY_CLOCK */

uint32_t        hz_tick_interval = 1;
#if ENABLE_LEGACY_CLOCK_CODE
static uint64_t has_monotonic_clock = 0;
#endif /* ENABLE_LEGACY_CLOCK_CODE */

lck_ticket_t clock_lock;
LCK_GRP_DECLARE(clock_lock_grp, "clock");

static LCK_GRP_DECLARE(settime_lock_grp, "settime");
static LCK_MTX_DECLARE(settime_lock, &settime_lock_grp);

#define clock_lock()    \
	lck_ticket_lock(&clock_lock, &clock_lock_grp)

#define clock_unlock()  \
	lck_ticket_unlock(&clock_lock)

boolean_t
kdp_clock_is_locked()
{
	return kdp_lck_ticket_is_acquired(&clock_lock);
}

struct bintime {
	time_t  sec;
	uint64_t frac;
};

static __inline void
bintime_addx(struct bintime *_bt, uint64_t _x)
{
	uint64_t _u;

	_u = _bt->frac;
	_bt->frac += _x;
	if (_u > _bt->frac) {
		_bt->sec++;
	}
}

static __inline void
bintime_subx(struct bintime *_bt, uint64_t _x)
{
	uint64_t _u;

	_u = _bt->frac;
	_bt->frac -= _x;
	if (_u < _bt->frac) {
		_bt->sec--;
	}
}

static __inline void
bintime_addns(struct bintime *bt, uint64_t ns)
{
	bt->sec += ns / (uint64_t)NSEC_PER_SEC;
	ns = ns % (uint64_t)NSEC_PER_SEC;
	if (ns) {
		/* 18446744073 = int(2^64 / NSEC_PER_SEC) */
		ns = ns * (uint64_t)18446744073LL;
		bintime_addx(bt, ns);
	}
}

static __inline void
bintime_subns(struct bintime *bt, uint64_t ns)
{
	bt->sec -= ns / (uint64_t)NSEC_PER_SEC;
	ns = ns % (uint64_t)NSEC_PER_SEC;
	if (ns) {
		/* 18446744073 = int(2^64 / NSEC_PER_SEC) */
		ns = ns * (uint64_t)18446744073LL;
		bintime_subx(bt, ns);
	}
}

static __inline void
bintime_addxns(struct bintime *bt, uint64_t a, int64_t xns)
{
	uint64_t uxns = (xns > 0)?(uint64_t)xns:(uint64_t)-xns;
	uint64_t ns = multi_overflow(a, uxns);
	if (xns > 0) {
		if (ns) {
			bintime_addns(bt, ns);
		}
		ns = (a * uxns) / (uint64_t)NSEC_PER_SEC;
		bintime_addx(bt, ns);
	} else {
		if (ns) {
			bintime_subns(bt, ns);
		}
		ns = (a * uxns) / (uint64_t)NSEC_PER_SEC;
		bintime_subx(bt, ns);
	}
}


static __inline void
bintime_add(struct bintime *_bt, const struct bintime *_bt2)
{
	uint64_t _u;

	_u = _bt->frac;
	_bt->frac += _bt2->frac;
	if (_u > _bt->frac) {
		_bt->sec++;
	}
	_bt->sec += _bt2->sec;
}

static __inline void
bintime_sub(struct bintime *_bt, const struct bintime *_bt2)
{
	uint64_t _u;

	_u = _bt->frac;
	_bt->frac -= _bt2->frac;
	if (_u < _bt->frac) {
		_bt->sec--;
	}
	_bt->sec -= _bt2->sec;
}

static __inline void
clock2bintime(const clock_sec_t *secs, const clock_usec_t *microsecs, struct bintime *_bt)
{
	_bt->sec = *secs;
	/* 18446744073709 = int(2^64 / 1000000) */
	_bt->frac = *microsecs * (uint64_t)18446744073709LL;
}

static __inline void
bintime2usclock(const struct bintime *_bt, clock_sec_t *secs, clock_usec_t *microsecs)
{
	*secs = _bt->sec;
	*microsecs = ((uint64_t)USEC_PER_SEC * (uint32_t)(_bt->frac >> 32)) >> 32;
}

static __inline void
bintime2nsclock(const struct bintime *_bt, clock_sec_t *secs, clock_usec_t *nanosecs)
{
	*secs = _bt->sec;
	*nanosecs = ((uint64_t)NSEC_PER_SEC * (uint32_t)(_bt->frac >> 32)) >> 32;
}

#if ENABLE_LEGACY_CLOCK_CODE
static __inline void
bintime2absolutetime(const struct bintime *_bt, uint64_t *abs)
{
	uint64_t nsec;
	nsec = (uint64_t) _bt->sec * (uint64_t)NSEC_PER_SEC + (((uint64_t)NSEC_PER_SEC * (uint32_t)(_bt->frac >> 32)) >> 32);
	nanoseconds_to_absolutetime(nsec, abs);
}

struct latched_time {
	uint64_t monotonic_time_usec;
	uint64_t mach_time;
};

extern int
kernel_sysctlbyname(const char *name, void *oldp, size_t *oldlenp, void *newp, size_t newlen);

#endif /* ENABLE_LEGACY_CLOCK_CODE */
/*
 *	Time of day (calendar) variables.
 *
 *	Algorithm:
 *
 *	TOD <- bintime + delta*scale
 *
 *	where :
 *      bintime is a cumulative offset that includes bootime and scaled time elapsed betweed bootime and last scale update.
 *	delta is ticks elapsed since last scale update.
 *	scale is computed according to an adjustment provided by ntp_kern.
 */
static struct clock_calend {
	uint64_t                s_scale_ns; /* scale to apply for each second elapsed, it converts in ns */
	int64_t                 s_adj_nsx; /* additional adj to apply for each second elapsed, it is expressed in 64 bit frac of ns */
	uint64_t                tick_scale_x; /* scale to apply for each tick elapsed, it converts in 64 bit frac of s */
	uint64_t                offset_count; /* abs time from which apply current scales */
	struct bintime          offset; /* cumulative offset expressed in (sec, 64 bits frac of a second) */
	struct bintime          bintime; /* cumulative offset (it includes bootime) expressed in (sec, 64 bits frac of a second) */
	struct bintime          boottime; /* boot time expressed in (sec, 64 bits frac of a second) */
#if ENABLE_LEGACY_CLOCK_CODE
	struct bintime          basesleep;
#endif /* ENABLE_LEGACY_CLOCK_CODE */
} clock_calend;

static uint64_t ticks_per_sec; /* ticks in a second (expressed in abs time) */

#if DEVELOPMENT || DEBUG
extern int g_should_log_clock_adjustments;

static void print_all_clock_variables(const char*, clock_sec_t* pmu_secs, clock_usec_t* pmu_usec, clock_sec_t* sys_secs, clock_usec_t* sys_usec, struct clock_calend* calend_cp);
static void print_all_clock_variables_internal(const char *, struct clock_calend* calend_cp);
#else
#define print_all_clock_variables(...) do { } while (0)
#define print_all_clock_variables_internal(...) do { } while (0)
#endif

#if     CONFIG_DTRACE


/*
 *	Unlocked calendar flipflop; this is used to track a clock_calend such
 *	that we can safely access a snapshot of a valid  clock_calend structure
 *	without needing to take any locks to do it.
 *
 *	The trick is to use a generation count and set the low bit when it is
 *	being updated/read; by doing this, we guarantee, through use of the
 *	os_atomic functions, that the generation is incremented when the bit
 *	is cleared atomically (by using a 1 bit add).
 */
static struct unlocked_clock_calend {
	struct clock_calend     calend;         /* copy of calendar */
	uint32_t                gen;            /* generation count */
} flipflop[2];

static void clock_track_calend_nowait(void);

#endif

void _clock_delay_until_deadline(uint64_t interval, uint64_t deadline);
void _clock_delay_until_deadline_with_leeway(uint64_t interval, uint64_t deadline, uint64_t leeway);

/* Boottime variables*/
static uint64_t clock_boottime;
static uint32_t clock_boottime_usec;

#define TIME_ADD(rsecs, secs, rfrac, frac, unit)        \
MACRO_BEGIN                                                                                     \
	if (((rfrac) += (frac)) >= (unit)) {                    \
	        (rfrac) -= (unit);                                                      \
	        (rsecs) += 1;                                                           \
	}                                                                                               \
	(rsecs) += (secs);                                                              \
MACRO_END

#define TIME_SUB(rsecs, secs, rfrac, frac, unit)        \
MACRO_BEGIN                                                                                     \
	if ((int)((rfrac) -= (frac)) < 0) {                             \
	        (rfrac) += (unit);                                                      \
	        (rsecs) -= 1;                                                           \
	}                                                                                               \
	(rsecs) -= (secs);                                                              \
MACRO_END

/*
 *	clock_config:
 *
 *	Called once at boot to configure the clock subsystem.
 */
void
clock_config(void)
{
	lck_ticket_init(&clock_lock, &clock_lock_grp);

	clock_oldconfig();

	ntp_init();

	nanoseconds_to_absolutetime((uint64_t)NSEC_PER_SEC, &ticks_per_sec);
}

/*
 *	clock_init:
 *
 *	Called on a processor each time started.
 */
void
clock_init(void)
{
	clock_oldinit();
}

/*
 *	clock_timebase_init:
 *
 *	Called by machine dependent code
 *	to initialize areas dependent on the
 *	timebase value.  May be called multiple
 *	times during start up.
 */
void
clock_timebase_init(void)
{
	uint64_t        abstime;

	/*
	 * BSD expects a tick to represent 10ms.
	 */
	nanoseconds_to_absolutetime(NSEC_PER_SEC / 100, &abstime);
	hz_tick_interval = (uint32_t)abstime;

	sched_timebase_init();
}

/*
 *	mach_timebase_info_trap:
 *
 *	User trap returns timebase constant.
 */
kern_return_t
mach_timebase_info_trap(
	struct mach_timebase_info_trap_args *args)
{
	mach_vm_address_t                       out_info_addr = args->info;
	mach_timebase_info_data_t       info = {};

	clock_timebase_info(&info);

	copyout((void *)&info, out_info_addr, sizeof(info));

	return KERN_SUCCESS;
}

/*
 *	Calendar routines.
 */

/*
 *	clock_get_calendar_microtime:
 *
 *	Returns the current calendar value,
 *	microseconds as the fraction.
 */
void
clock_get_calendar_microtime(
	clock_sec_t             *secs,
	clock_usec_t            *microsecs)
{
	clock_get_calendar_absolute_and_microtime(secs, microsecs, NULL);
}

/*
 * get_scale_factors_from_adj:
 *
 * computes scale factors from the value given in adjustment.
 *
 * Part of the code has been taken from tc_windup of FreeBSD
 * written by Poul-Henning Kamp <phk@FreeBSD.ORG>, Julien Ridoux and
 * Konstantin Belousov.
 * https://github.com/freebsd/freebsd/blob/master/sys/kern/kern_tc.c
 */
static void
get_scale_factors_from_adj(int64_t adjustment, uint64_t* tick_scale_x, uint64_t* s_scale_ns, int64_t* s_adj_nsx)
{
	uint64_t scale;
	int64_t nano, frac;

	/*-
	 * Calculating the scaling factor.  We want the number of 1/2^64
	 * fractions of a second per period of the hardware counter, taking
	 * into account the th_adjustment factor which the NTP PLL/adjtime(2)
	 * processing provides us with.
	 *
	 * The th_adjustment is nanoseconds per second with 32 bit binary
	 * fraction and we want 64 bit binary fraction of second:
	 *
	 *	 x = a * 2^32 / 10^9 = a * 4.294967296
	 *
	 * The range of th_adjustment is +/- 5000PPM so inside a 64bit int
	 * we can only multiply by about 850 without overflowing, that
	 * leaves no suitably precise fractions for multiply before divide.
	 *
	 * Divide before multiply with a fraction of 2199/512 results in a
	 * systematic undercompensation of 10PPM of th_adjustment.  On a
	 * 5000PPM adjustment this is a 0.05PPM error.  This is acceptable.
	 *
	 * We happily sacrifice the lowest of the 64 bits of our result
	 * to the goddess of code clarity.
	 *
	 */
	scale = (uint64_t)1 << 63;
	scale += (adjustment / 1024) * 2199;
	scale /= ticks_per_sec;
	*tick_scale_x = scale * 2;

	/*
	 * hi part of adj
	 * it contains ns (without fraction) to add to the next sec.
	 * Get ns scale factor for the next sec.
	 */
	nano = (adjustment > 0)? adjustment >> 32 : -((-adjustment) >> 32);
	scale = (uint64_t) NSEC_PER_SEC;
	scale += nano;
	*s_scale_ns = scale;

	/*
	 * lo part of adj
	 * it contains 32 bit frac of ns to add to the next sec.
	 * Keep it as additional adjustment for the next sec.
	 */
	frac = (adjustment > 0)? ((uint32_t) adjustment) : -((uint32_t) (-adjustment));
	*s_adj_nsx = (frac > 0)? ((uint64_t) frac) << 32 : -(((uint64_t) (-frac)) << 32);

	return;
}

/*
 * scale_delta:
 *
 * returns a bintime struct representing delta scaled accordingly to the
 * scale factors provided to this function.
 */
static struct bintime
scale_delta(uint64_t delta, uint64_t tick_scale_x, uint64_t s_scale_ns, int64_t s_adj_nsx)
{
	uint64_t sec, new_ns, over;
	struct bintime bt;

	bt.sec = 0;
	bt.frac = 0;

	/*
	 * If more than one second is elapsed,
	 * scale fully elapsed seconds using scale factors for seconds.
	 * s_scale_ns -> scales sec to ns.
	 * s_adj_nsx -> additional adj expressed in 64 bit frac of ns to apply to each sec.
	 */
	if (delta > ticks_per_sec) {
		sec = (delta / ticks_per_sec);
		new_ns = sec * s_scale_ns;
		bintime_addns(&bt, new_ns);
		if (s_adj_nsx) {
			if (sec == 1) {
				/* shortcut, no overflow can occur */
				if (s_adj_nsx > 0) {
					bintime_addx(&bt, (uint64_t)s_adj_nsx / (uint64_t)NSEC_PER_SEC);
				} else {
					bintime_subx(&bt, (uint64_t)-s_adj_nsx / (uint64_t)NSEC_PER_SEC);
				}
			} else {
				/*
				 * s_adj_nsx is 64 bit frac of ns.
				 * sec*s_adj_nsx might overflow in int64_t.
				 * use bintime_addxns to not lose overflowed ns.
				 */
				bintime_addxns(&bt, sec, s_adj_nsx);
			}
		}
		delta = (delta % ticks_per_sec);
	}

	over = multi_overflow(tick_scale_x, delta);
	if (over) {
		bt.sec += over;
	}

	/*
	 * scale elapsed ticks using the scale factor for ticks.
	 */
	bintime_addx(&bt, delta * tick_scale_x);

	return bt;
}

/*
 * get_scaled_time:
 *
 * returns the scaled time of the time elapsed from the last time
 * scale factors were updated to now.
 */
static struct bintime
get_scaled_time(uint64_t now)
{
	uint64_t delta;

	/*
	 * Compute ticks elapsed since last scale update.
	 * This time will be scaled according to the value given by ntp kern.
	 */
	delta = now - clock_calend.offset_count;

	return scale_delta(delta, clock_calend.tick_scale_x, clock_calend.s_scale_ns, clock_calend.s_adj_nsx);
}

static void
clock_get_calendar_absolute_and_microtime_locked(
	clock_sec_t             *secs,
	clock_usec_t            *microsecs,
	uint64_t                *abstime)
{
	uint64_t now;
	struct bintime bt;

	now  = mach_absolute_time();
	if (abstime) {
		*abstime = now;
	}

	bt = get_scaled_time(now);
	bintime_add(&bt, &clock_calend.bintime);
	bintime2usclock(&bt, secs, microsecs);
}

static void
clock_get_calendar_absolute_and_nanotime_locked(
	clock_sec_t             *secs,
	clock_usec_t            *nanosecs,
	uint64_t                *abstime)
{
	uint64_t now;
	struct bintime bt;

	now  = mach_absolute_time();
	if (abstime) {
		*abstime = now;
	}

	bt = get_scaled_time(now);
	bintime_add(&bt, &clock_calend.bintime);
	bintime2nsclock(&bt, secs, nanosecs);
}

/*
 *	clock_get_calendar_absolute_and_microtime:
 *
 *	Returns the current calendar value,
 *	microseconds as the fraction. Also
 *	returns mach_absolute_time if abstime
 *	is not NULL.
 */
void
clock_get_calendar_absolute_and_microtime(
	clock_sec_t             *secs,
	clock_usec_t            *microsecs,
	uint64_t                *abstime)
{
	spl_t                   s;

	s = splclock();
	clock_lock();

	clock_get_calendar_absolute_and_microtime_locked(secs, microsecs, abstime);

	clock_unlock();
	splx(s);
}

/*
 *	clock_get_calendar_nanotime:
 *
 *	Returns the current calendar value,
 *	nanoseconds as the fraction.
 *
 *	Since we do not have an interface to
 *	set the calendar with resolution greater
 *	than a microsecond, we honor that here.
 */
void
clock_get_calendar_nanotime(
	clock_sec_t             *secs,
	clock_nsec_t            *nanosecs)
{
	spl_t                   s;

	s = splclock();
	clock_lock();

	clock_get_calendar_absolute_and_nanotime_locked(secs, nanosecs, NULL);

	clock_unlock();
	splx(s);
}

/*
 *	clock_gettimeofday:
 *
 *	Kernel interface for commpage implementation of
 *	gettimeofday() syscall.
 *
 *	Returns the current calendar value, and updates the
 *	commpage info as appropriate.  Because most calls to
 *	gettimeofday() are handled in user mode by the commpage,
 *	this routine should be used infrequently.
 */
void
clock_gettimeofday(
	clock_sec_t     *secs,
	clock_usec_t    *microsecs)
{
	clock_gettimeofday_and_absolute_time(secs, microsecs, NULL);
}

void
clock_gettimeofday_and_absolute_time(
	clock_sec_t     *secs,
	clock_usec_t    *microsecs,
	uint64_t        *mach_time)
{
	uint64_t                now;
	spl_t                   s;
	struct bintime  bt;

	s = splclock();
	clock_lock();

	now = mach_absolute_time();
	bt = get_scaled_time(now);
	bintime_add(&bt, &clock_calend.bintime);
	bintime2usclock(&bt, secs, microsecs);

	clock_gettimeofday_set_commpage(now, bt.sec, bt.frac, clock_calend.tick_scale_x, ticks_per_sec);

	clock_unlock();
	splx(s);

	if (mach_time) {
		*mach_time = now;
	}
}

/*
 *	clock_set_calendar_microtime:
 *
 *	Sets the current calendar value by
 *	recalculating the epoch and offset
 *	from the system clock.
 *
 *	Also adjusts the boottime to keep the
 *	value consistent, writes the new
 *	calendar value to the platform clock,
 *	and sends calendar change notifications.
 */
void
clock_set_calendar_microtime(
	clock_sec_t             secs,
	clock_usec_t            microsecs)
{
	uint64_t                absolutesys;
	clock_sec_t             newsecs;
	clock_sec_t             oldsecs;
	clock_usec_t            newmicrosecs;
	clock_usec_t            oldmicrosecs;
	uint64_t                commpage_value;
	spl_t                   s;
	struct bintime          bt;
	clock_sec_t             deltasecs;
	clock_usec_t            deltamicrosecs;

	newsecs = secs;
	newmicrosecs = microsecs;

	/*
	 * settime_lock mtx is used to avoid that racing settimeofdays update the wall clock and
	 * the platform clock concurrently.
	 *
	 * clock_lock cannot be used for this race because it is acquired from interrupt context
	 * and it needs interrupts disabled while instead updating the platform clock needs to be
	 * called with interrupts enabled.
	 */
	lck_mtx_lock(&settime_lock);

	s = splclock();
	clock_lock();

#if DEVELOPMENT || DEBUG
	struct clock_calend clock_calend_cp = clock_calend;
#endif
	commpage_disable_timestamp();

	/*
	 *	Adjust the boottime based on the delta.
	 */
	clock_get_calendar_absolute_and_microtime_locked(&oldsecs, &oldmicrosecs, &absolutesys);

#if DEVELOPMENT || DEBUG
	if (g_should_log_clock_adjustments) {
		os_log(OS_LOG_DEFAULT, "%s wall %lu s %d u computed with %llu abs\n",
		    __func__, (unsigned long)oldsecs, oldmicrosecs, absolutesys);
		os_log(OS_LOG_DEFAULT, "%s requested %lu s %d u\n",
		    __func__, (unsigned long)secs, microsecs );
	}
#endif

	if (oldsecs < secs || (oldsecs == secs && oldmicrosecs < microsecs)) {
		// moving forwards
		deltasecs = secs;
		deltamicrosecs = microsecs;

		TIME_SUB(deltasecs, oldsecs, deltamicrosecs, oldmicrosecs, USEC_PER_SEC);

		TIME_ADD(clock_boottime, deltasecs, clock_boottime_usec, deltamicrosecs, USEC_PER_SEC);
		clock2bintime(&deltasecs, &deltamicrosecs, &bt);
		bintime_add(&clock_calend.boottime, &bt);
	} else {
		// moving backwards
		deltasecs = oldsecs;
		deltamicrosecs = oldmicrosecs;

		TIME_SUB(deltasecs, secs, deltamicrosecs, microsecs, USEC_PER_SEC);

		TIME_SUB(clock_boottime, deltasecs, clock_boottime_usec, deltamicrosecs, USEC_PER_SEC);
		clock2bintime(&deltasecs, &deltamicrosecs, &bt);
		bintime_sub(&clock_calend.boottime, &bt);
	}

	clock_calend.bintime = clock_calend.boottime;
	bintime_add(&clock_calend.bintime, &clock_calend.offset);

	clock2bintime((clock_sec_t *) &secs, (clock_usec_t *) &microsecs, &bt);

	clock_gettimeofday_set_commpage(absolutesys, bt.sec, bt.frac, clock_calend.tick_scale_x, ticks_per_sec);

#if DEVELOPMENT || DEBUG
	struct clock_calend clock_calend_cp1 = clock_calend;
#endif

	commpage_value = clock_boottime * USEC_PER_SEC + clock_boottime_usec;

	commpage_update_boottime(commpage_value);

	clock_unlock();
	splx(s);

	/*
	 *	Set the new value for the platform clock.
	 *	This call might block, so interrupts must be enabled.
	 */
#if DEVELOPMENT || DEBUG
	uint64_t now_b = mach_absolute_time();
#endif

	PESetUTCTimeOfDay(newsecs, newmicrosecs);

#if DEVELOPMENT || DEBUG
	uint64_t now_a = mach_absolute_time();
	if (g_should_log_clock_adjustments) {
		os_log(OS_LOG_DEFAULT, "%s mach bef PESet %llu mach aft %llu \n", __func__, now_b, now_a);
	}
#endif

	print_all_clock_variables_internal(__func__, &clock_calend_cp);
	print_all_clock_variables_internal(__func__, &clock_calend_cp1);

	/*
	 *	Send host notifications.
	 */
	host_notify_calendar_change();
	host_notify_calendar_set();

#if CONFIG_DTRACE
	clock_track_calend_nowait();
#endif

	lck_mtx_unlock(&settime_lock);
}

uint64_t mach_absolutetime_asleep = 0;
uint64_t mach_absolutetime_last_sleep = 0;

void
clock_get_calendar_uptime(clock_sec_t *secs)
{
	uint64_t now;
	spl_t s;
	struct bintime bt;

	s = splclock();
	clock_lock();

	now = mach_absolute_time();

	bt = get_scaled_time(now);
	bintime_add(&bt, &clock_calend.offset);

	*secs = bt.sec;

	clock_unlock();
	splx(s);
}


/*
 * clock_update_calendar:
 *
 * called by ntp timer to update scale factors.
 */
void
clock_update_calendar(void)
{
	uint64_t now, delta;
	struct bintime bt;
	spl_t s;
	int64_t adjustment;

	s = splclock();
	clock_lock();

	now  = mach_absolute_time();

	/*
	 * scale the time elapsed since the last update and
	 * add it to offset.
	 */
	bt = get_scaled_time(now);
	bintime_add(&clock_calend.offset, &bt);

	/*
	 * update the base from which apply next scale factors.
	 */
	delta = now - clock_calend.offset_count;
	clock_calend.offset_count += delta;

	clock_calend.bintime = clock_calend.offset;
	bintime_add(&clock_calend.bintime, &clock_calend.boottime);

	/*
	 * recompute next adjustment.
	 */
	ntp_update_second(&adjustment, clock_calend.bintime.sec);

#if DEVELOPMENT || DEBUG
	if (g_should_log_clock_adjustments) {
		os_log(OS_LOG_DEFAULT, "%s adjustment %lld\n", __func__, adjustment);
	}
#endif

	/*
	 * recomputing scale factors.
	 */
	get_scale_factors_from_adj(adjustment, &clock_calend.tick_scale_x, &clock_calend.s_scale_ns, &clock_calend.s_adj_nsx);

	clock_gettimeofday_set_commpage(now, clock_calend.bintime.sec, clock_calend.bintime.frac, clock_calend.tick_scale_x, ticks_per_sec);

#if DEVELOPMENT || DEBUG
	struct clock_calend calend_cp = clock_calend;
#endif

	clock_unlock();
	splx(s);

	print_all_clock_variables(__func__, NULL, NULL, NULL, NULL, &calend_cp);
}


#if DEVELOPMENT || DEBUG

void
print_all_clock_variables_internal(const char* func, struct clock_calend* clock_calend_cp)
{
	clock_sec_t     offset_secs;
	clock_usec_t    offset_microsecs;
	clock_sec_t     bintime_secs;
	clock_usec_t    bintime_microsecs;
	clock_sec_t     bootime_secs;
	clock_usec_t    bootime_microsecs;

	if (!g_should_log_clock_adjustments) {
		return;
	}

	bintime2usclock(&clock_calend_cp->offset, &offset_secs, &offset_microsecs);
	bintime2usclock(&clock_calend_cp->bintime, &bintime_secs, &bintime_microsecs);
	bintime2usclock(&clock_calend_cp->boottime, &bootime_secs, &bootime_microsecs);

	os_log(OS_LOG_DEFAULT, "%s s_scale_ns %llu s_adj_nsx %lld tick_scale_x %llu offset_count %llu\n",
	    func, clock_calend_cp->s_scale_ns, clock_calend_cp->s_adj_nsx,
	    clock_calend_cp->tick_scale_x, clock_calend_cp->offset_count);
	os_log(OS_LOG_DEFAULT, "%s offset.sec %ld offset.frac %llu offset_secs %lu offset_microsecs %d\n",
	    func, clock_calend_cp->offset.sec, clock_calend_cp->offset.frac,
	    (unsigned long)offset_secs, offset_microsecs);
	os_log(OS_LOG_DEFAULT, "%s bintime.sec %ld bintime.frac %llu bintime_secs %lu bintime_microsecs %d\n",
	    func, clock_calend_cp->bintime.sec, clock_calend_cp->bintime.frac,
	    (unsigned long)bintime_secs, bintime_microsecs);
	os_log(OS_LOG_DEFAULT, "%s bootime.sec %ld bootime.frac %llu bootime_secs %lu bootime_microsecs %d\n",
	    func, clock_calend_cp->boottime.sec, clock_calend_cp->boottime.frac,
	    (unsigned long)bootime_secs, bootime_microsecs);

#if !HAS_CONTINUOUS_HWCLOCK
	clock_sec_t     basesleep_secs;
	clock_usec_t    basesleep_microsecs;

	bintime2usclock(&clock_calend_cp->basesleep, &basesleep_secs, &basesleep_microsecs);
	os_log(OS_LOG_DEFAULT, "%s basesleep.sec %ld basesleep.frac %llu basesleep_secs %lu basesleep_microsecs %d\n",
	    func, clock_calend_cp->basesleep.sec, clock_calend_cp->basesleep.frac,
	    (unsigned long)basesleep_secs, basesleep_microsecs);
#endif
}


void
print_all_clock_variables(const char* func, clock_sec_t* pmu_secs, clock_usec_t* pmu_usec, clock_sec_t* sys_secs, clock_usec_t* sys_usec, struct clock_calend* clock_calend_cp)
{
	if (!g_should_log_clock_adjustments) {
		return;
	}

	struct bintime  bt;
	clock_sec_t     wall_secs;
	clock_usec_t    wall_microsecs;
	uint64_t now;
	uint64_t delta;

	if (pmu_secs) {
		os_log(OS_LOG_DEFAULT, "%s PMU %lu s %d u \n", func, (unsigned long)*pmu_secs, *pmu_usec);
	}
	if (sys_secs) {
		os_log(OS_LOG_DEFAULT, "%s sys %lu s %d u \n", func, (unsigned long)*sys_secs, *sys_usec);
	}

	print_all_clock_variables_internal(func, clock_calend_cp);

	now = mach_absolute_time();
	delta = now - clock_calend_cp->offset_count;

	bt = scale_delta(delta, clock_calend_cp->tick_scale_x, clock_calend_cp->s_scale_ns, clock_calend_cp->s_adj_nsx);
	bintime_add(&bt, &clock_calend_cp->bintime);
	bintime2usclock(&bt, &wall_secs, &wall_microsecs);

	os_log(OS_LOG_DEFAULT, "%s wall %lu s %d u computed with %llu abs\n",
	    func, (unsigned long)wall_secs, wall_microsecs, now);
}


#endif /* DEVELOPMENT || DEBUG */


/*
 *	clock_initialize_calendar:
 *
 *	Set the calendar and related clocks
 *	from the platform clock at boot.
 *
 *	Also sends host notifications.
 */
void
clock_initialize_calendar(void)
{
	clock_sec_t             sys;  // sleepless time since boot in seconds
	clock_sec_t             secs; // Current UTC time
	clock_sec_t             utc_offset_secs; // Difference in current UTC time and sleepless time since boot
	clock_usec_t            microsys;
	clock_usec_t            microsecs;
	clock_usec_t            utc_offset_microsecs;
	spl_t                   s;
	struct bintime          bt;
#if ENABLE_LEGACY_CLOCK_CODE
	struct bintime          monotonic_bt;
	struct latched_time     monotonic_time;
	uint64_t                monotonic_usec_total;
	clock_sec_t             sys2, monotonic_sec;
	clock_usec_t            microsys2, monotonic_usec;
	size_t                  size;

#endif /* ENABLE_LEGACY_CLOCK_CODE */
	//Get the UTC time and corresponding sys time
	PEGetUTCTimeOfDay(&secs, &microsecs);
	clock_get_system_microtime(&sys, &microsys);

#if ENABLE_LEGACY_CLOCK_CODE
	/*
	 * If the platform has a monotonic clock, use kern.monotonicclock_usecs
	 * to estimate the sleep/wake time, otherwise use the UTC time to estimate
	 * the sleep time.
	 */
	size = sizeof(monotonic_time);
	if (kernel_sysctlbyname("kern.monotonicclock_usecs", &monotonic_time, &size, NULL, 0) != 0) {
		has_monotonic_clock = 0;
		os_log(OS_LOG_DEFAULT, "%s system does not have monotonic clock\n", __func__);
	} else {
		has_monotonic_clock = 1;
		monotonic_usec_total = monotonic_time.monotonic_time_usec;
		absolutetime_to_microtime(monotonic_time.mach_time, &sys2, &microsys2);
		os_log(OS_LOG_DEFAULT, "%s system has monotonic clock\n", __func__);
	}
#endif /* ENABLE_LEGACY_CLOCK_CODE */

	s = splclock();
	clock_lock();

	commpage_disable_timestamp();

	utc_offset_secs = secs;
	utc_offset_microsecs = microsecs;

	/*
	 * We normally expect the UTC clock to be always-on and produce
	 * greater readings than the tick counter.  There may be corner cases
	 * due to differing clock resolutions (UTC clock is likely lower) and
	 * and errors reading the UTC clock (some implementations return 0
	 * on error) in which that doesn't hold true.  Bring the UTC measurements
	 * in-line with the tick counter measurements as a best effort in that case.
	 */
	if ((sys > secs) || ((sys == secs) && (microsys > microsecs))) {
		os_log(OS_LOG_DEFAULT, "%s WARNING: UTC time is less then sys time, (%lu s %d u) UTC (%lu s %d u) sys\n",
		    __func__, (unsigned long) secs, microsecs, (unsigned long)sys, microsys);
		secs = utc_offset_secs = sys;
		microsecs = utc_offset_microsecs = microsys;
	}

	// UTC - sys
	// This macro stores the subtraction result in utc_offset_secs and utc_offset_microsecs
	TIME_SUB(utc_offset_secs, sys, utc_offset_microsecs, microsys, USEC_PER_SEC);
	// This function converts utc_offset_secs and utc_offset_microsecs in bintime
	clock2bintime(&utc_offset_secs, &utc_offset_microsecs, &bt);

	/*
	 *	Initialize the boot time based on the platform clock.
	 */
	clock_boottime = secs;
	clock_boottime_usec = microsecs;
	commpage_update_boottime(clock_boottime * USEC_PER_SEC + clock_boottime_usec);

	nanoseconds_to_absolutetime((uint64_t)NSEC_PER_SEC, &ticks_per_sec);
	clock_calend.boottime = bt;
	clock_calend.bintime = bt;
	clock_calend.offset.sec = 0;
	clock_calend.offset.frac = 0;

	clock_calend.tick_scale_x = (uint64_t)1 << 63;
	clock_calend.tick_scale_x /= ticks_per_sec;
	clock_calend.tick_scale_x *= 2;

	clock_calend.s_scale_ns = NSEC_PER_SEC;
	clock_calend.s_adj_nsx = 0;

#if ENABLE_LEGACY_CLOCK_CODE
	if (has_monotonic_clock) {
		OS_ANALYZER_SUPPRESS("82347749") monotonic_sec = monotonic_usec_total / (clock_sec_t)USEC_PER_SEC;
		monotonic_usec = monotonic_usec_total % (clock_usec_t)USEC_PER_SEC;

		// monotonic clock - sys
		// This macro stores the subtraction result in monotonic_sec and monotonic_usec
		TIME_SUB(monotonic_sec, sys2, monotonic_usec, microsys2, USEC_PER_SEC);
		clock2bintime(&monotonic_sec, &monotonic_usec, &monotonic_bt);

		// set the baseleep as the difference between monotonic clock - sys
		clock_calend.basesleep = monotonic_bt;
	}
#endif /* ENABLE_LEGACY_CLOCK_CODE */
	commpage_update_mach_continuous_time(mach_absolutetime_asleep);

#if DEVELOPMENT || DEBUG
	struct clock_calend clock_calend_cp = clock_calend;
#endif

	clock_unlock();
	splx(s);

	print_all_clock_variables(__func__, &secs, &microsecs, &sys, &microsys, &clock_calend_cp);

	/*
	 *	Send host notifications.
	 */
	host_notify_calendar_change();

#if CONFIG_DTRACE
	clock_track_calend_nowait();
#endif
}

#if HAS_CONTINUOUS_HWCLOCK

static void
scale_sleep_time(void)
{
	/* Apply the current NTP frequency adjustment to the time slept.
	 * The frequency adjustment remains stable between calls to ntp_adjtime(),
	 * and should thus provide a reasonable approximation of the total adjustment
	 * required for the time slept. */
	struct bintime sleep_time;
	uint64_t tick_scale_x, s_scale_ns;
	int64_t s_adj_nsx;
	int64_t sleep_adj = ntp_get_freq();
	if (sleep_adj) {
		get_scale_factors_from_adj(sleep_adj, &tick_scale_x, &s_scale_ns, &s_adj_nsx);
		sleep_time = scale_delta(mach_absolutetime_last_sleep, tick_scale_x, s_scale_ns, s_adj_nsx);
	} else {
		tick_scale_x = (uint64_t)1 << 63;
		tick_scale_x /= ticks_per_sec;
		tick_scale_x *= 2;
		sleep_time.sec = mach_absolutetime_last_sleep / ticks_per_sec;
		sleep_time.frac = (mach_absolutetime_last_sleep % ticks_per_sec) * tick_scale_x;
	}
	bintime_add(&clock_calend.offset, &sleep_time);
	bintime_add(&clock_calend.bintime, &sleep_time);
}

static void
clock_wakeup_calendar_hwclock(void)
{
	spl_t   s;

	s = splclock();
	clock_lock();

	commpage_disable_timestamp();

	uint64_t abstime = mach_absolute_time();
	uint64_t total_sleep_time = mach_continuous_time() - abstime;

	mach_absolutetime_last_sleep = total_sleep_time - mach_absolutetime_asleep;
	mach_absolutetime_asleep = total_sleep_time;

	scale_sleep_time();

	KDBG_RELEASE(MACHDBG_CODE(DBG_MACH_CLOCK, MACH_EPOCH_CHANGE),
	    (uintptr_t)mach_absolutetime_last_sleep,
	    (uintptr_t)mach_absolutetime_asleep,
	    (uintptr_t)(mach_absolutetime_last_sleep >> 32),
	    (uintptr_t)(mach_absolutetime_asleep >> 32));

	commpage_update_mach_continuous_time(mach_absolutetime_asleep);
#if HIBERNATION
	commpage_update_mach_continuous_time_hw_offset(hwclock_conttime_offset);
#endif
	adjust_cont_time_thread_calls();

	clock_unlock();
	splx(s);

	host_notify_calendar_change();

#if CONFIG_DTRACE
	clock_track_calend_nowait();
#endif
}

#endif /* HAS_CONTINUOUS_HWCLOCK */

#if ENABLE_LEGACY_CLOCK_CODE

static void
clock_wakeup_calendar_legacy(void)
{
	clock_sec_t             wake_sys_sec;
	clock_usec_t            wake_sys_usec;
	clock_sec_t             wake_sec;
	clock_usec_t            wake_usec;
	clock_sec_t             wall_time_sec;
	clock_usec_t            wall_time_usec;
	clock_sec_t             diff_sec;
	clock_usec_t            diff_usec;
	clock_sec_t             var_s;
	clock_usec_t            var_us;
	spl_t                   s;
	struct bintime          bt, last_sleep_bt;
	struct latched_time     monotonic_time;
	uint64_t                monotonic_usec_total;
	uint64_t                wake_abs;
	size_t                  size;

	/*
	 * If the platform has the monotonic clock use that to
	 * compute the sleep time. The monotonic clock does not have an offset
	 * that can be modified, so nor kernel or userspace can change the time
	 * of this clock, it can only monotonically increase over time.
	 * During sleep mach_absolute_time (sys time) does not tick,
	 * so the sleep time is the difference between the current monotonic time
	 * less the absolute time and the previous difference stored at wake time.
	 *
	 * basesleep = (monotonic - sys) ---> computed at last wake
	 * sleep_time = (monotonic - sys) - basesleep
	 *
	 * If the platform does not support monotonic clock we set the wall time to what the
	 * UTC clock returns us.
	 * Setting the wall time to UTC time implies that we loose all the adjustments
	 * done during wake time through adjtime/ntp_adjustime.
	 * The UTC time is the monotonic clock + an offset that can be set
	 * by kernel.
	 * The time slept in this case is the difference between wall time and UTC
	 * at wake.
	 *
	 * IMPORTANT:
	 * We assume that only the kernel is setting the offset of the PMU/RTC and that
	 * it is doing it only througth the settimeofday interface.
	 */
	if (has_monotonic_clock) {
#if DEVELOPMENT || DEBUG
		/*
		 * Just for debugging, get the wake UTC time.
		 */
		PEGetUTCTimeOfDay(&var_s, &var_us);
#endif
		/*
		 * Get monotonic time with corresponding sys time
		 */
		size = sizeof(monotonic_time);
		if (kernel_sysctlbyname("kern.monotonicclock_usecs", &monotonic_time, &size, NULL, 0) != 0) {
			panic("%s: could not call kern.monotonicclock_usecs", __func__);
		}
		wake_abs = monotonic_time.mach_time;
		absolutetime_to_microtime(wake_abs, &wake_sys_sec, &wake_sys_usec);

		monotonic_usec_total = monotonic_time.monotonic_time_usec;
		wake_sec = monotonic_usec_total / (clock_sec_t)USEC_PER_SEC;
		wake_usec = monotonic_usec_total % (clock_usec_t)USEC_PER_SEC;
	} else {
		/*
		 * Get UTC time and corresponding sys time
		 */
		PEGetUTCTimeOfDay(&wake_sec, &wake_usec);
		wake_abs = mach_absolute_time();
		absolutetime_to_microtime(wake_abs, &wake_sys_sec, &wake_sys_usec);
	}

#if DEVELOPMENT || DEBUG
	os_log(OS_LOG_DEFAULT, "time at wake %lu s %d u from %s clock, abs %llu\n", (unsigned long)wake_sec, wake_usec, (has_monotonic_clock)?"monotonic":"UTC", wake_abs);
	if (has_monotonic_clock) {
		OS_ANALYZER_SUPPRESS("82347749") os_log(OS_LOG_DEFAULT, "UTC time %lu s %d u\n", (unsigned long)var_s, var_us);
	}
#endif /* DEVELOPMENT || DEBUG */

	s = splclock();
	clock_lock();

	commpage_disable_timestamp();

#if DEVELOPMENT || DEBUG
	struct clock_calend clock_calend_cp1 = clock_calend;
#endif /* DEVELOPMENT || DEBUG */

	/*
	 * We normally expect the UTC/monotonic clock to be always-on and produce
	 * greater readings than the sys counter.  There may be corner cases
	 * due to differing clock resolutions (UTC/monotonic clock is likely lower) and
	 * and errors reading the UTC/monotonic clock (some implementations return 0
	 * on error) in which that doesn't hold true.
	 */
	if ((wake_sys_sec > wake_sec) || ((wake_sys_sec == wake_sec) && (wake_sys_usec > wake_usec))) {
		os_log_error(OS_LOG_DEFAULT, "WARNING: %s clock is less then sys clock at wake: %lu s %d u vs %lu s %d u, defaulting sleep time to zero\n", (has_monotonic_clock)?"monotonic":"UTC", (unsigned long)wake_sec, wake_usec, (unsigned long)wake_sys_sec, wake_sys_usec);
		mach_absolutetime_last_sleep = 0;
		goto done;
	}

	if (has_monotonic_clock) {
		/*
		 * computer the difference monotonic - sys
		 * we already checked that monotonic time is
		 * greater than sys.
		 */
		diff_sec = wake_sec;
		diff_usec = wake_usec;
		// This macro stores the subtraction result in diff_sec and diff_usec
		TIME_SUB(diff_sec, wake_sys_sec, diff_usec, wake_sys_usec, USEC_PER_SEC);
		//This function converts diff_sec and diff_usec in bintime
		clock2bintime(&diff_sec, &diff_usec, &bt);

		/*
		 * Safety belt: the monotonic clock will likely have a lower resolution than the sys counter.
		 * It's also possible that the device didn't fully transition to the powered-off state on
		 * the most recent sleep, so the sys counter may not have reset or may have only briefly
		 * turned off.  In that case it's possible for the difference between the monotonic clock and the
		 * sys counter to be less than the previously recorded value in clock.calend.basesleep.
		 * In that case simply record that we slept for 0 ticks.
		 */
		if ((bt.sec > clock_calend.basesleep.sec) ||
		    ((bt.sec == clock_calend.basesleep.sec) && (bt.frac > clock_calend.basesleep.frac))) {
			//last_sleep is the difference between (current monotonic - abs) and (last wake monotonic - abs)
			last_sleep_bt = bt;
			bintime_sub(&last_sleep_bt, &clock_calend.basesleep);

			bintime2absolutetime(&last_sleep_bt, &mach_absolutetime_last_sleep);
			mach_absolutetime_asleep += mach_absolutetime_last_sleep;

			//set basesleep to current monotonic - abs
			clock_calend.basesleep = bt;

			//update wall time
			bintime_add(&clock_calend.offset, &last_sleep_bt);
			bintime_add(&clock_calend.bintime, &last_sleep_bt);

			bintime2usclock(&last_sleep_bt, &var_s, &var_us);
			os_log(OS_LOG_DEFAULT, "time_slept (%lu s %d u)\n", (unsigned long) var_s, var_us);
		} else {
			bintime2usclock(&clock_calend.basesleep, &var_s, &var_us);
			os_log_error(OS_LOG_DEFAULT, "WARNING: last wake monotonic-sys time (%lu s %d u) is greater then current monotonic-sys time(%lu s %d u), defaulting sleep time to zero\n", (unsigned long) var_s, var_us, (unsigned long) diff_sec, diff_usec);

			mach_absolutetime_last_sleep = 0;
		}
	} else {
		/*
		 * set the wall time to UTC value
		 */
		bt = get_scaled_time(wake_abs);
		bintime_add(&bt, &clock_calend.bintime);
		bintime2usclock(&bt, &wall_time_sec, &wall_time_usec);

		if (wall_time_sec > wake_sec || (wall_time_sec == wake_sec && wall_time_usec > wake_usec)) {
			os_log(OS_LOG_DEFAULT, "WARNING: wall time (%lu s %d u) is greater than current UTC time (%lu s %d u), defaulting sleep time to zero\n", (unsigned long) wall_time_sec, wall_time_usec, (unsigned long) wake_sec, wake_usec);

			mach_absolutetime_last_sleep = 0;
		} else {
			diff_sec = wake_sec;
			diff_usec = wake_usec;
			// This macro stores the subtraction result in diff_sec and diff_usec
			TIME_SUB(diff_sec, wall_time_sec, diff_usec, wall_time_usec, USEC_PER_SEC);
			//This function converts diff_sec and diff_usec in bintime
			clock2bintime(&diff_sec, &diff_usec, &bt);

			//time slept in this case is the difference between PMU/RTC and wall time
			last_sleep_bt = bt;

			bintime2absolutetime(&last_sleep_bt, &mach_absolutetime_last_sleep);
			mach_absolutetime_asleep += mach_absolutetime_last_sleep;

			//update wall time
			bintime_add(&clock_calend.offset, &last_sleep_bt);
			bintime_add(&clock_calend.bintime, &last_sleep_bt);

			bintime2usclock(&last_sleep_bt, &var_s, &var_us);
			os_log(OS_LOG_DEFAULT, "time_slept (%lu s %d u)\n", (unsigned long)var_s, var_us);
		}
	}
done:
	KDBG_RELEASE(MACHDBG_CODE(DBG_MACH_CLOCK, MACH_EPOCH_CHANGE),
	    (uintptr_t)mach_absolutetime_last_sleep,
	    (uintptr_t)mach_absolutetime_asleep,
	    (uintptr_t)(mach_absolutetime_last_sleep >> 32),
	    (uintptr_t)(mach_absolutetime_asleep >> 32));

	commpage_update_mach_continuous_time(mach_absolutetime_asleep);
	adjust_cont_time_thread_calls();

#if DEVELOPMENT || DEBUG
	struct clock_calend clock_calend_cp = clock_calend;
#endif

	clock_unlock();
	splx(s);

#if DEVELOPMENT || DEBUG
	if (g_should_log_clock_adjustments) {
		print_all_clock_variables("clock_wakeup_calendar: BEFORE", NULL, NULL, NULL, NULL, &clock_calend_cp1);
		print_all_clock_variables("clock_wakeup_calendar: AFTER", NULL, NULL, NULL, NULL, &clock_calend_cp);
	}
#endif /* DEVELOPMENT || DEBUG */

	host_notify_calendar_change();

#if CONFIG_DTRACE
	clock_track_calend_nowait();
#endif
}

#endif /* ENABLE_LEGACY_CLOCK_CODE */

void
clock_wakeup_calendar(void)
{
#if HAS_CONTINUOUS_HWCLOCK
#if HIBERNATION_USES_LEGACY_CLOCK
	if (gIOHibernateState) {
		// if we're resuming from hibernation, we have to take the legacy wakeup path
		return clock_wakeup_calendar_legacy();
	}
#endif /* HIBERNATION_USES_LEGACY_CLOCK */
	// use the hwclock wakeup path
	return clock_wakeup_calendar_hwclock();
#elif ENABLE_LEGACY_CLOCK_CODE
	return clock_wakeup_calendar_legacy();
#else
#error "can't determine which clock code to run"
#endif
}

/*
 *	clock_get_boottime_nanotime:
 *
 *	Return the boottime, used by sysctl.
 */
void
clock_get_boottime_nanotime(
	clock_sec_t                     *secs,
	clock_nsec_t            *nanosecs)
{
	spl_t   s;

	s = splclock();
	clock_lock();

	*secs = (clock_sec_t)clock_boottime;
	*nanosecs = (clock_nsec_t)clock_boottime_usec * NSEC_PER_USEC;

	clock_unlock();
	splx(s);
}

/*
 *	clock_get_boottime_nanotime:
 *
 *	Return the boottime, used by sysctl.
 */
void
clock_get_boottime_microtime(
	clock_sec_t                     *secs,
	clock_usec_t            *microsecs)
{
	spl_t   s;

	s = splclock();
	clock_lock();

	*secs = (clock_sec_t)clock_boottime;
	*microsecs = (clock_nsec_t)clock_boottime_usec;

	clock_unlock();
	splx(s);
}


/*
 *	Wait / delay routines.
 */
static void
mach_wait_until_continue(
	__unused void   *parameter,
	wait_result_t   wresult)
{
	thread_syscall_return((wresult == THREAD_INTERRUPTED)? KERN_ABORTED: KERN_SUCCESS);
	/*NOTREACHED*/
}

/*
 * mach_wait_until_trap: Suspend execution of calling thread until the specified time has passed
 *
 * Parameters:    args->deadline          Amount of time to wait
 *
 * Returns:        0                      Success
 *                !0                      Not success
 *
 */
kern_return_t
mach_wait_until_trap(
	struct mach_wait_until_trap_args        *args)
{
	uint64_t                deadline = args->deadline;
	wait_result_t   wresult;


	wresult = assert_wait_deadline_with_leeway((event_t)mach_wait_until_trap, THREAD_ABORTSAFE,
	    TIMEOUT_URGENCY_USER_NORMAL, deadline, 0);
	if (wresult == THREAD_WAITING) {
		wresult = thread_block(mach_wait_until_continue);
	}

	return (wresult == THREAD_INTERRUPTED)? KERN_ABORTED: KERN_SUCCESS;
}

void
clock_delay_until(
	uint64_t                deadline)
{
	uint64_t                now = mach_absolute_time();

	if (now >= deadline) {
		return;
	}

	_clock_delay_until_deadline(deadline - now, deadline);
}

/*
 * Preserve the original precise interval that the client
 * requested for comparison to the spin threshold.
 */
void
_clock_delay_until_deadline(
	uint64_t                interval,
	uint64_t                deadline)
{
	_clock_delay_until_deadline_with_leeway(interval, deadline, 0);
}

/*
 * Like _clock_delay_until_deadline, but it accepts a
 * leeway value.
 */
void
_clock_delay_until_deadline_with_leeway(
	uint64_t                interval,
	uint64_t                deadline,
	uint64_t                leeway)
{
	if (interval == 0) {
		return;
	}

	if (ml_delay_should_spin(interval) ||
	    get_preemption_level() != 0 ||
	    ml_get_interrupts_enabled() == FALSE) {
		machine_delay_until(interval, deadline);
	} else {
		/*
		 * For now, assume a leeway request of 0 means the client does not want a leeway
		 * value. We may want to change this interpretation in the future.
		 */

		if (leeway) {
			assert_wait_deadline_with_leeway((event_t)clock_delay_until, THREAD_UNINT, TIMEOUT_URGENCY_LEEWAY, deadline, leeway);
		} else {
			assert_wait_deadline((event_t)clock_delay_until, THREAD_UNINT, deadline);
		}

		thread_block(THREAD_CONTINUE_NULL);
	}
}

void
delay_for_interval(
	uint32_t                interval,
	uint32_t                scale_factor)
{
	uint64_t                abstime;

	clock_interval_to_absolutetime_interval(interval, scale_factor, &abstime);

	_clock_delay_until_deadline(abstime, mach_absolute_time() + abstime);
}

void
delay_for_interval_with_leeway(
	uint32_t                interval,
	uint32_t                leeway,
	uint32_t                scale_factor)
{
	uint64_t                abstime_interval;
	uint64_t                abstime_leeway;

	clock_interval_to_absolutetime_interval(interval, scale_factor, &abstime_interval);
	clock_interval_to_absolutetime_interval(leeway, scale_factor, &abstime_leeway);

	_clock_delay_until_deadline_with_leeway(abstime_interval, mach_absolute_time() + abstime_interval, abstime_leeway);
}

void
delay(
	int             usec)
{
	delay_for_interval((usec < 0)? -usec: usec, NSEC_PER_USEC);
}

/*
 *	Miscellaneous routines.
 */
void
clock_interval_to_deadline(
	uint32_t                        interval,
	uint32_t                        scale_factor,
	uint64_t                        *result)
{
	uint64_t        abstime;

	clock_interval_to_absolutetime_interval(interval, scale_factor, &abstime);

	if (os_add_overflow(mach_absolute_time(), abstime, result)) {
		*result = UINT64_MAX;
	}
}

void
nanoseconds_to_deadline(
	uint64_t                        interval,
	uint64_t                        *result)
{
	uint64_t        abstime;

	nanoseconds_to_absolutetime(interval, &abstime);

	if (os_add_overflow(mach_absolute_time(), abstime, result)) {
		*result = UINT64_MAX;
	}
}

void
clock_absolutetime_interval_to_deadline(
	uint64_t                        abstime,
	uint64_t                        *result)
{
	if (os_add_overflow(mach_absolute_time(), abstime, result)) {
		*result = UINT64_MAX;
	}
}

void
clock_continuoustime_interval_to_deadline(
	uint64_t                        conttime,
	uint64_t                        *result)
{
	if (os_add_overflow(mach_continuous_time(), conttime, result)) {
		*result = UINT64_MAX;
	}
}

void
clock_get_uptime(
	uint64_t        *result)
{
	*result = mach_absolute_time();
}

void
clock_deadline_for_periodic_event(
	uint64_t                        interval,
	uint64_t                        abstime,
	uint64_t                        *deadline)
{
	assert(interval != 0);

	// *deadline += interval;
	if (os_add_overflow(*deadline, interval, deadline)) {
		*deadline = UINT64_MAX;
	}

	if (*deadline <= abstime) {
		// *deadline = abstime + interval;
		if (os_add_overflow(abstime, interval, deadline)) {
			*deadline = UINT64_MAX;
		}

		abstime = mach_absolute_time();
		if (*deadline <= abstime) {
			// *deadline = abstime + interval;
			if (os_add_overflow(abstime, interval, deadline)) {
				*deadline = UINT64_MAX;
			}
		}
	}
}

uint64_t
mach_continuous_time(void)
{
#if HIBERNATION && HAS_CONTINUOUS_HWCLOCK
	return ml_get_hwclock() + hwclock_conttime_offset;
#elif HAS_CONTINUOUS_HWCLOCK
	return ml_get_hwclock();
#else
	while (1) {
		uint64_t read1 = mach_absolutetime_asleep;
		uint64_t absolute = mach_absolute_time();
		OSMemoryBarrier();
		uint64_t read2 = mach_absolutetime_asleep;

		if (__builtin_expect(read1 == read2, 1)) {
			return absolute + read1;
		}
	}
#endif
}

uint64_t
mach_continuous_speculative_time(void)
{
#if HIBERNATION && HAS_CONTINUOUS_HWCLOCK
	return ml_get_hwclock_speculative() + hwclock_conttime_offset;
#elif HAS_CONTINUOUS_HWCLOCK
	return ml_get_hwclock_speculative();
#else
	return mach_continuous_time();
#endif
}

uint64_t
mach_continuous_approximate_time(void)
{
#if HAS_CONTINUOUS_HWCLOCK
	return mach_continuous_time();
#else
	while (1) {
		uint64_t read1 = mach_absolutetime_asleep;
		uint64_t absolute = mach_approximate_time();
		OSMemoryBarrier();
		uint64_t read2 = mach_absolutetime_asleep;

		if (__builtin_expect(read1 == read2, 1)) {
			return absolute + read1;
		}
	}
#endif
}

/*
 * continuoustime_to_absolutetime
 * Must be called with interrupts disabled
 * Returned value is only valid until the next update to
 * mach_continuous_time
 */
uint64_t
continuoustime_to_absolutetime(uint64_t conttime)
{
	if (conttime <= mach_absolutetime_asleep) {
		return 0;
	} else {
		return conttime - mach_absolutetime_asleep;
	}
}

/*
 * absolutetime_to_continuoustime
 * Must be called with interrupts disabled
 * Returned value is only valid until the next update to
 * mach_continuous_time
 */
uint64_t
absolutetime_to_continuoustime(uint64_t abstime)
{
	return abstime + mach_absolutetime_asleep;
}

#if     CONFIG_DTRACE

/*
 * clock_get_calendar_nanotime_nowait
 *
 * Description:	Non-blocking version of clock_get_calendar_nanotime()
 *
 * Notes:	This function operates by separately tracking calendar time
 *		updates using a two element structure to copy the calendar
 *		state, which may be asynchronously modified.  It utilizes
 *		barrier instructions in the tracking process and in the local
 *		stable snapshot process in order to ensure that a consistent
 *		snapshot is used to perform the calculation.
 */
void
clock_get_calendar_nanotime_nowait(
	clock_sec_t                     *secs,
	clock_nsec_t            *nanosecs)
{
	int i = 0;
	uint64_t                now;
	struct unlocked_clock_calend stable;
	struct bintime bt;

	for (;;) {
		stable = flipflop[i];           /* take snapshot */

		/*
		 * Use a barrier instructions to ensure atomicity.  We AND
		 * off the "in progress" bit to get the current generation
		 * count.
		 */
		os_atomic_andnot(&stable.gen, 1, relaxed);

		/*
		 * If an update _is_ in progress, the generation count will be
		 * off by one, if it _was_ in progress, it will be off by two,
		 * and if we caught it at a good time, it will be equal (and
		 * our snapshot is threfore stable).
		 */
		if (flipflop[i].gen == stable.gen) {
			break;
		}

		/* Switch to the other element of the flipflop, and try again. */
		i ^= 1;
	}

	now = mach_absolute_time();

	bt = get_scaled_time(now);

	bintime_add(&bt, &clock_calend.bintime);

	bintime2nsclock(&bt, secs, nanosecs);
}

static void
clock_track_calend_nowait(void)
{
	int i;

	for (i = 0; i < 2; i++) {
		struct clock_calend tmp = clock_calend;

		/*
		 * Set the low bit if the generation count; since we use a
		 * barrier instruction to do this, we are guaranteed that this
		 * will flag an update in progress to an async caller trying
		 * to examine the contents.
		 */
		os_atomic_or(&flipflop[i].gen, 1, relaxed);

		flipflop[i].calend = tmp;

		/*
		 * Increment the generation count to clear the low bit to
		 * signal completion.  If a caller compares the generation
		 * count after taking a copy while in progress, the count
		 * will be off by two.
		 */
		os_atomic_inc(&flipflop[i].gen, relaxed);
	}
}

#endif  /* CONFIG_DTRACE */

/*
 * Scheduler clock - returns current time in nanosec units.
 * This is default implementation.
 * Architectures and sub-architectures can override this.
 */
notrace unsigned long long __weak sched_clock(void)
{
	return (unsigned long long)(jiffies - INITIAL_JIFFIES)
					* (NSEC_PER_SEC / HZ);
}
EXPORT_SYMBOL_GPL(sched_clock);

static DEFINE_STATIC_KEY_FALSE(sched_clock_running);

#ifdef CONFIG_HAVE_UNSTABLE_SCHED_CLOCK
/*
 * We must start with !__sched_clock_stable because the unstable -> stable
 * transition is accurate, while the stable -> unstable transition is not.
 *
 * Similarly we start with __sched_clock_stable_early, thereby assuming we
 * will become stable, such that there's only a single 1 -> 0 transition.
 */
static DEFINE_STATIC_KEY_FALSE(__sched_clock_stable);
static int __sched_clock_stable_early = 1;

/*
 * We want: ktime_get_ns() + __gtod_offset == sched_clock() + __sched_clock_offset
 */
__read_mostly u64 __sched_clock_offset;
static __read_mostly u64 __gtod_offset;

struct sched_clock_data {
	u64			tick_raw;
	u64			tick_gtod;
	u64			clock;
};

static DEFINE_PER_CPU_SHARED_ALIGNED(struct sched_clock_data, sched_clock_data);

static __always_inline struct sched_clock_data *this_scd(void)
{
	return this_cpu_ptr(&sched_clock_data);
}

notrace static inline struct sched_clock_data *cpu_sdc(int cpu)
{
	return &per_cpu(sched_clock_data, cpu);
}

notrace int sched_clock_stable(void)
{
	return static_branch_likely(&__sched_clock_stable);
}

notrace static void __scd_stamp(struct sched_clock_data *scd)
{
	scd->tick_gtod = ktime_get_ns();
	scd->tick_raw = sched_clock();
}

notrace static void __set_sched_clock_stable(void)
{
	struct sched_clock_data *scd;

	/*
	 * Since we're still unstable and the tick is already running, we have
	 * to disable IRQs in order to get a consistent scd->tick* reading.
	 */
	local_irq_disable();
	scd = this_scd();
	/*
	 * Attempt to make the (initial) unstable->stable transition continuous.
	 */
	__sched_clock_offset = (scd->tick_gtod + __gtod_offset) - (scd->tick_raw);
	local_irq_enable();

	printk(KERN_INFO "sched_clock: Marking stable (%lld, %lld)->(%lld, %lld)\n",
			scd->tick_gtod, __gtod_offset,
			scd->tick_raw,  __sched_clock_offset);

	static_branch_enable(&__sched_clock_stable);
	tick_dep_clear(TICK_DEP_BIT_CLOCK_UNSTABLE);
}

/*
 * If we ever get here, we're screwed, because we found out -- typically after
 * the fact -- that TSC wasn't good. This means all our clocksources (including
 * ktime) could have reported wrong values.
 *
 * What we do here is an attempt to fix up and continue sort of where we left
 * off in a coherent manner.
 *
 * The only way to fully avoid random clock jumps is to boot with:
 * "tsc=unstable".
 */
notrace static void __sched_clock_work(struct work_struct *work)
{
	struct sched_clock_data *scd;
	int cpu;

	/* take a current timestamp and set 'now' */
	preempt_disable();
	scd = this_scd();
	__scd_stamp(scd);
	scd->clock = scd->tick_gtod + __gtod_offset;
	preempt_enable();

	/* clone to all CPUs */
	for_each_possible_cpu(cpu)
		per_cpu(sched_clock_data, cpu) = *scd;

	printk(KERN_WARNING "TSC found unstable after boot, most likely due to broken BIOS. Use 'tsc=unstable'.\n");
	printk(KERN_INFO "sched_clock: Marking unstable (%lld, %lld)<-(%lld, %lld)\n",
			scd->tick_gtod, __gtod_offset,
			scd->tick_raw,  __sched_clock_offset);

	disable_sched_clock_irqtime();
	static_branch_disable(&__sched_clock_stable);
}

static DECLARE_WORK(sched_clock_work, __sched_clock_work);

notrace static void __clear_sched_clock_stable(void)
{
	if (!sched_clock_stable())
		return;

	tick_dep_set(TICK_DEP_BIT_CLOCK_UNSTABLE);
	schedule_work(&sched_clock_work);
}

notrace void clear_sched_clock_stable(void)
{
	__sched_clock_stable_early = 0;

	smp_mb(); /* matches sched_clock_init_late() */

	if (static_key_count(&sched_clock_running.key) == 2)
		__clear_sched_clock_stable();
}

notrace static void __sched_clock_gtod_offset(void)
{
	struct sched_clock_data *scd = this_scd();

	__scd_stamp(scd);
	__gtod_offset = (scd->tick_raw + __sched_clock_offset) - scd->tick_gtod;
}

void __init sched_clock_init(void)
{
	/*
	 * Set __gtod_offset such that once we mark sched_clock_running,
	 * sched_clock_tick() continues where sched_clock() left off.
	 *
	 * Even if TSC is buggered, we're still UP at this point so it
	 * can't really be out of sync.
	 */
	local_irq_disable();
	__sched_clock_gtod_offset();
	local_irq_enable();

	static_branch_inc(&sched_clock_running);
}
/*
 * We run this as late_initcall() such that it runs after all built-in drivers,
 * notably: acpi_processor and intel_idle, which can mark the TSC as unstable.
 */
static int __init sched_clock_init_late(void)
{
	static_branch_inc(&sched_clock_running);
	/*
	 * Ensure that it is impossible to not do a static_key update.
	 *
	 * Either {set,clear}_sched_clock_stable() must see sched_clock_running
	 * and do the update, or we must see their __sched_clock_stable_early
	 * and do the update, or both.
	 */
	smp_mb(); /* matches {set,clear}_sched_clock_stable() */

	if (__sched_clock_stable_early)
		__set_sched_clock_stable();
	else
		disable_sched_clock_irqtime();  /* disable if clock unstable. */

	return 0;
}
late_initcall(sched_clock_init_late);

/*
 * min, max except they take wrapping into account
 */

static __always_inline u64 wrap_min(u64 x, u64 y)
{
	return (s64)(x - y) < 0 ? x : y;
}

static __always_inline u64 wrap_max(u64 x, u64 y)
{
	return (s64)(x - y) > 0 ? x : y;
}

/*
 * update the percpu scd from the raw @now value
 *
 *  - filter out backward motion
 *  - use the GTOD tick value to create a window to filter crazy TSC values
 */
static __always_inline u64 sched_clock_local(struct sched_clock_data *scd)
{
	u64 now, clock, old_clock, min_clock, max_clock, gtod;
	s64 delta;

again:
	now = sched_clock_noinstr();
	delta = now - scd->tick_raw;
	if (unlikely(delta < 0))
		delta = 0;

	old_clock = scd->clock;

	/*
	 * scd->clock = clamp(scd->tick_gtod + delta,
	 *		      max(scd->tick_gtod, scd->clock),
	 *		      scd->tick_gtod + TICK_NSEC);
	 */

	gtod = scd->tick_gtod + __gtod_offset;
	clock = gtod + delta;
	min_clock = wrap_max(gtod, old_clock);
	max_clock = wrap_max(old_clock, gtod + TICK_NSEC);

	clock = wrap_max(clock, min_clock);
	clock = wrap_min(clock, max_clock);

	if (!raw_try_cmpxchg64(&scd->clock, &old_clock, clock))
		goto again;

	return clock;
}

noinstr u64 local_clock_noinstr(void)
{
	u64 clock;

	if (static_branch_likely(&__sched_clock_stable))
		return sched_clock_noinstr() + __sched_clock_offset;

	if (!static_branch_likely(&sched_clock_running))
		return sched_clock_noinstr();

	clock = sched_clock_local(this_scd());

	return clock;
}

u64 local_clock(void)
{
	u64 now;
	preempt_disable_notrace();
	now = local_clock_noinstr();
	preempt_enable_notrace();
	return now;
}
EXPORT_SYMBOL_GPL(local_clock);

static notrace u64 sched_clock_remote(struct sched_clock_data *scd)
{
	struct sched_clock_data *my_scd = this_scd();
	u64 this_clock, remote_clock;
	u64 *ptr, old_val, val;

#if BITS_PER_LONG != 64
again:
	/*
	 * Careful here: The local and the remote clock values need to
	 * be read out atomic as we need to compare the values and
	 * then update either the local or the remote side. So the
	 * cmpxchg64 below only protects one readout.
	 *
	 * We must reread via sched_clock_local() in the retry case on
	 * 32-bit kernels as an NMI could use sched_clock_local() via the
	 * tracer and hit between the readout of
	 * the low 32-bit and the high 32-bit portion.
	 */
	this_clock = sched_clock_local(my_scd);
	/*
	 * We must enforce atomic readout on 32-bit, otherwise the
	 * update on the remote CPU can hit in between the readout of
	 * the low 32-bit and the high 32-bit portion.
	 */
	remote_clock = cmpxchg64(&scd->clock, 0, 0);
#else
	/*
	 * On 64-bit kernels the read of [my]scd->clock is atomic versus the
	 * update, so we can avoid the above 32-bit dance.
	 */
	sched_clock_local(my_scd);
again:
	this_clock = my_scd->clock;
	remote_clock = scd->clock;
#endif

	/*
	 * Use the opportunity that we have both locks
	 * taken to couple the two clocks: we take the
	 * larger time as the latest time for both
	 * runqueues. (this creates monotonic movement)
	 */
	if (likely((s64)(remote_clock - this_clock) < 0)) {
		ptr = &scd->clock;
		old_val = remote_clock;
		val = this_clock;
	} else {
		/*
		 * Should be rare, but possible:
		 */
		ptr = &my_scd->clock;
		old_val = this_clock;
		val = remote_clock;
	}

	if (!try_cmpxchg64(ptr, &old_val, val))
		goto again;

	return val;
}

/*
 * Similar to cpu_clock(), but requires local IRQs to be disabled.
 *
 * See cpu_clock().
 */
notrace u64 sched_clock_cpu(int cpu)
{
	struct sched_clock_data *scd;
	u64 clock;

	if (sched_clock_stable())
		return sched_clock() + __sched_clock_offset;

	if (!static_branch_likely(&sched_clock_running))
		return sched_clock();

	preempt_disable_notrace();
	scd = cpu_sdc(cpu);

	if (cpu != smp_processor_id())
		clock = sched_clock_remote(scd);
	else
		clock = sched_clock_local(scd);
	preempt_enable_notrace();

	return clock;
}
EXPORT_SYMBOL_GPL(sched_clock_cpu);

notrace void sched_clock_tick(void)
{
	struct sched_clock_data *scd;

	if (sched_clock_stable())
		return;

	if (!static_branch_likely(&sched_clock_running))
		return;

	lockdep_assert_irqs_disabled();

	scd = this_scd();
	__scd_stamp(scd);
	sched_clock_local(scd);
}

notrace void sched_clock_tick_stable(void)
{
	if (!sched_clock_stable())
		return;

	/*
	 * Called under watchdog_lock.
	 *
	 * The watchdog just found this TSC to (still) be stable, so now is a
	 * good moment to update our __gtod_offset. Because once we find the
	 * TSC to be unstable, any computation will be computing crap.
	 */
	local_irq_disable();
	__sched_clock_gtod_offset();
	local_irq_enable();
}

/*
 * We are going deep-idle (IRQs are disabled):
 */
notrace void sched_clock_idle_sleep_event(void)
{
	sched_clock_cpu(smp_processor_id());
}
EXPORT_SYMBOL_GPL(sched_clock_idle_sleep_event);

/*
 * We just idled; resync with ktime.
 */
notrace void sched_clock_idle_wakeup_event(void)
{
	unsigned long flags;

	if (sched_clock_stable())
		return;

	if (unlikely(timekeeping_suspended))
		return;

	local_irq_save(flags);
	sched_clock_tick();
	local_irq_restore(flags);
}
EXPORT_SYMBOL_GPL(sched_clock_idle_wakeup_event);

#else /* !CONFIG_HAVE_UNSTABLE_SCHED_CLOCK: */

void __init sched_clock_init(void)
{
	static_branch_inc(&sched_clock_running);
	local_irq_disable();
	generic_sched_clock_init();
	local_irq_enable();
}

notrace u64 sched_clock_cpu(int cpu)
{
	if (!static_branch_likely(&sched_clock_running))
		return 0;

	return sched_clock();
}

#endif /* !CONFIG_HAVE_UNSTABLE_SCHED_CLOCK */

/*
 * Running clock - returns the time that has elapsed while a guest has been
 * running.
 * On a guest this value should be local_clock minus the time the guest was
 * suspended by the hypervisor (for any reason).
 * On bare metal this function should return the same as local_clock.
 * Architectures and sub-architectures can override this.
 */
notrace u64 __weak running_clock(void)
{
	return local_clock();
}
struct  alarm {
	struct  alarm   *al_next;               /* next alarm in chain */
	struct  alarm   *al_prev;               /* previous alarm in chain */
	int                             al_status;              /* alarm status */
	mach_timespec_t al_time;                /* alarm time */
	struct {                                /* message alarm data */
		int                             type;           /* alarm type */
		ipc_port_t              port;           /* alarm port */
		mach_msg_type_name_t
		    port_type;                                  /* alarm port type */
		struct  clock   *clock;         /* alarm clock */
		void                    *data;          /* alarm data */
	} al_alrm;
#define al_type         al_alrm.type
#define al_port         al_alrm.port
#define al_port_type    al_alrm.port_type
#define al_clock        al_alrm.clock
#define al_data         al_alrm.data
	long                    al_seqno;               /* alarm sequence number */
};
typedef struct alarm    alarm_data_t;

/* alarm status */
#define ALARM_FREE      0               /* alarm is on free list */
#define ALARM_SLEEP     1               /* active clock_sleep() */
#define ALARM_CLOCK     2               /* active clock_alarm() */
#define ALARM_DONE      4               /* alarm has expired */

/* local data declarations */
decl_simple_lock_data(static, alarm_lock);       /* alarm synchronization */
/* zone for user alarms */
static KALLOC_TYPE_DEFINE(alarm_zone, struct alarm, KT_DEFAULT);
static struct   alarm           *alrmfree;              /* alarm free list pointer */
static struct   alarm           *alrmdone;              /* alarm done list pointer */
static struct   alarm           *alrmlist;
static long                     alrm_seqno;             /* uniquely identifies alarms */
static thread_call_data_t       alarm_done_call;
static timer_call_data_t        alarm_expire_timer;

extern  struct clock    clock_list[];
extern  int             clock_count;

static void             post_alarm(
	alarm_t                 alarm);

static void             set_alarm(
	mach_timespec_t *alarm_time);

static int              check_time(
	alarm_type_t    alarm_type,
	mach_timespec_t *alarm_time,
	mach_timespec_t *clock_time);

static void             alarm_done(void);

static void             alarm_expire(void);

static kern_return_t    clock_sleep_internal(
	clock_t                         clock,
	sleep_type_t            sleep_type,
	mach_timespec_t         *sleep_time);

int             rtclock_init(void);

kern_return_t   rtclock_gettime(
	mach_timespec_t                 *cur_time);

kern_return_t   rtclock_getattr(
	clock_flavor_t                  flavor,
	clock_attr_t                    attr,
	mach_msg_type_number_t  *count);

SECURITY_READ_ONLY_EARLY(struct clock_ops) sysclk_ops = {
	.c_config   = NULL,
	.c_init     = rtclock_init,
	.c_gettime  = rtclock_gettime,
	.c_getattr  = rtclock_getattr,
};

kern_return_t   calend_gettime(
	mach_timespec_t                 *cur_time);

kern_return_t   calend_getattr(
	clock_flavor_t                  flavor,
	clock_attr_t                    attr,
	mach_msg_type_number_t  *count);

SECURITY_READ_ONLY_EARLY(struct clock_ops) calend_ops = {
	.c_config   = NULL,
	.c_init     = NULL,
	.c_gettime  = calend_gettime,
	.c_getattr  = calend_getattr,
};

/*
 * List of clock devices.
 */
SECURITY_READ_ONLY_LATE(struct clock) clock_list[] = {
	[SYSTEM_CLOCK] = {
		.cl_ops     = &sysclk_ops,
		.cl_service = IPC_PORT_NULL,
	},
	[CALENDAR_CLOCK] = {
		.cl_ops     = &calend_ops,
		.cl_service = IPC_PORT_NULL,
	},
};
int     clock_count = sizeof(clock_list) / sizeof(clock_list[0]);

/*
 *	Macros to lock/unlock clock system.
 */
#define LOCK_ALARM(s)                   \
	s = splclock();                 \
	simple_lock(&alarm_lock, LCK_GRP_NULL);

#define UNLOCK_ALARM(s)                 \
	simple_unlock(&alarm_lock);     \
	splx(s);

void
clock_oldconfig(void)
{
	clock_t                 clock;
	int     i;

	simple_lock_init(&alarm_lock, 0);
	thread_call_setup(&alarm_done_call, (thread_call_func_t)alarm_done, NULL);
	timer_call_setup(&alarm_expire_timer, (timer_call_func_t)alarm_expire, NULL);

	/*
	 * Configure clock devices.
	 */
	for (i = 0; i < clock_count; i++) {
		clock = &clock_list[i];
		if (clock->cl_ops && clock->cl_ops->c_config) {
			if ((*clock->cl_ops->c_config)() == 0) {
				clock->cl_ops = NULL;
			}
		}
	}

	/* start alarm sequence numbers at 0 */
	alrm_seqno = 0;
}

void
clock_oldinit(void)
{
	clock_t                 clock;
	int     i;

	/*
	 * Initialize basic clock structures.
	 */
	for (i = 0; i < clock_count; i++) {
		clock = &clock_list[i];
		if (clock->cl_ops && clock->cl_ops->c_init) {
			(*clock->cl_ops->c_init)();
		}
	}
}

/*
 * Initialize the clock ipc service facility.
 */
void
clock_service_create(void)
{
	/*
	 * Initialize ipc clock services.
	 */
	for (int i = 0; i < clock_count; i++) {
		clock_t clock = &clock_list[i];
		if (clock->cl_ops) {
			ipc_clock_init(clock);
		}
	}
}

/*
 * Get the service port on a clock.
 */
kern_return_t
host_get_clock_service(
	host_t                  host,
	clock_id_t              clock_id,
	clock_t                 *clock)         /* OUT */
{
	if (host == HOST_NULL || clock_id < 0 || clock_id >= clock_count) {
		*clock = CLOCK_NULL;
		return KERN_INVALID_ARGUMENT;
	}

	*clock = &clock_list[clock_id];
	if ((*clock)->cl_ops == 0) {
		return KERN_FAILURE;
	}
	return KERN_SUCCESS;
}

/*
 * Get the current clock time.
 */
kern_return_t
clock_get_time(
	clock_t                 clock,
	mach_timespec_t *cur_time)      /* OUT */
{
	if (clock == CLOCK_NULL) {
		return KERN_INVALID_ARGUMENT;
	}
	return (*clock->cl_ops->c_gettime)(cur_time);
}

kern_return_t
rtclock_gettime(
	mach_timespec_t         *time)  /* OUT */
{
	clock_sec_t             secs;
	clock_nsec_t    nsecs;

	clock_get_system_nanotime(&secs, &nsecs);
	time->tv_sec = (unsigned int)secs;
	time->tv_nsec = nsecs;

	return KERN_SUCCESS;
}

kern_return_t
calend_gettime(
	mach_timespec_t         *time)  /* OUT */
{
	clock_sec_t             secs;
	clock_nsec_t    nsecs;

	clock_get_calendar_nanotime(&secs, &nsecs);
	time->tv_sec = (unsigned int)secs;
	time->tv_nsec = nsecs;

	return KERN_SUCCESS;
}

/*
 * Get clock attributes.
 */
kern_return_t
clock_get_attributes(
	clock_t                                 clock,
	clock_flavor_t                  flavor,
	clock_attr_t                    attr,           /* OUT */
	mach_msg_type_number_t  *count)         /* IN/OUT */
{
	if (clock == CLOCK_NULL) {
		return KERN_INVALID_ARGUMENT;
	}
	if (clock->cl_ops->c_getattr) {
		return clock->cl_ops->c_getattr(flavor, attr, count);
	}
	return KERN_FAILURE;
}

kern_return_t
rtclock_getattr(
	clock_flavor_t                  flavor,
	clock_attr_t                    attr,           /* OUT */
	mach_msg_type_number_t  *count)         /* IN/OUT */
{
	if (*count != 1) {
		return KERN_FAILURE;
	}

	switch (flavor) {
	case CLOCK_GET_TIME_RES:        /* >0 res */
	case CLOCK_ALARM_CURRES:        /* =0 no alarm */
	case CLOCK_ALARM_MINRES:
	case CLOCK_ALARM_MAXRES:
		*(clock_res_t *) attr = NSEC_PER_SEC / 100;
		break;

	default:
		return KERN_INVALID_VALUE;
	}

	return KERN_SUCCESS;
}

kern_return_t
calend_getattr(
	clock_flavor_t                  flavor,
	clock_attr_t                    attr,           /* OUT */
	mach_msg_type_number_t  *count)         /* IN/OUT */
{
	if (*count != 1) {
		return KERN_FAILURE;
	}

	switch (flavor) {
	case CLOCK_GET_TIME_RES:        /* >0 res */
		*(clock_res_t *) attr = NSEC_PER_SEC / 100;
		break;

	case CLOCK_ALARM_CURRES:        /* =0 no alarm */
	case CLOCK_ALARM_MINRES:
	case CLOCK_ALARM_MAXRES:
		*(clock_res_t *) attr = 0;
		break;

	default:
		return KERN_INVALID_VALUE;
	}

	return KERN_SUCCESS;
}

/*
 * Setup a clock alarm.
 */
kern_return_t
clock_alarm(
	clock_t                                 clock,
	alarm_type_t                    alarm_type,
	mach_timespec_t                 alarm_time,
	ipc_port_t                              alarm_port,
	mach_msg_type_name_t    alarm_port_type)
{
	alarm_t                                 alarm;
	mach_timespec_t                 clock_time;
	int                                             chkstat;
	kern_return_t                   reply_code;
	spl_t                                   s;

	if (clock == CLOCK_NULL) {
		return KERN_INVALID_ARGUMENT;
	}
	if (clock != &clock_list[SYSTEM_CLOCK]) {
		return KERN_FAILURE;
	}
	if (IP_VALID(alarm_port) == 0) {
		return KERN_INVALID_CAPABILITY;
	}

	/*
	 * Check alarm parameters. If parameters are invalid,
	 * send alarm message immediately.
	 */
	(*clock->cl_ops->c_gettime)(&clock_time);
	chkstat = check_time(alarm_type, &alarm_time, &clock_time);
	if (chkstat <= 0) {
		reply_code = (chkstat < 0 ? KERN_INVALID_VALUE : KERN_SUCCESS);
		clock_alarm_reply(alarm_port, alarm_port_type,
		    reply_code, alarm_type, clock_time);
		return KERN_SUCCESS;
	}

	/*
	 * Get alarm and add to clock alarm list.
	 */

	LOCK_ALARM(s);
	if ((alarm = alrmfree) == 0) {
		UNLOCK_ALARM(s);
		alarm = zalloc_flags(alarm_zone, Z_WAITOK | Z_NOFAIL);
		LOCK_ALARM(s);
	} else {
		alrmfree = alarm->al_next;
	}

	alarm->al_status = ALARM_CLOCK;
	alarm->al_time = alarm_time;
	alarm->al_type = alarm_type;
	alarm->al_port = alarm_port;
	alarm->al_port_type = alarm_port_type;
	alarm->al_clock = clock;
	alarm->al_seqno = alrm_seqno++;
	post_alarm(alarm);
	UNLOCK_ALARM(s);

	return KERN_SUCCESS;
}

/*
 * Sleep on a clock. System trap. User-level libmach clock_sleep
 * interface call takes a mach_timespec_t sleep_time argument which it
 * converts to sleep_sec and sleep_nsec arguments which are then
 * passed to clock_sleep_trap.
 */
kern_return_t
clock_sleep_trap(
	struct clock_sleep_trap_args *args)
{
	mach_port_name_t        clock_name = args->clock_name;
	sleep_type_t            sleep_type = args->sleep_type;
	int                                     sleep_sec = args->sleep_sec;
	int                                     sleep_nsec = args->sleep_nsec;
	mach_vm_address_t       wakeup_time_addr = args->wakeup_time;
	clock_t                         clock;
	mach_timespec_t         swtime = {};
	kern_return_t           rvalue;

	/*
	 * Convert the trap parameters.
	 */
	if (clock_name == MACH_PORT_NULL) {
		clock = &clock_list[SYSTEM_CLOCK];
	} else {
		clock = port_name_to_clock(clock_name);
	}

	swtime.tv_sec  = sleep_sec;
	swtime.tv_nsec = sleep_nsec;

	/*
	 * Call the actual clock_sleep routine.
	 */
	rvalue = clock_sleep_internal(clock, sleep_type, &swtime);

	/*
	 * Return current time as wakeup time.
	 */
	if (rvalue != KERN_INVALID_ARGUMENT && rvalue != KERN_FAILURE) {
		copyout((char *)&swtime, wakeup_time_addr, sizeof(mach_timespec_t));
	}
	return rvalue;
}

static kern_return_t
clock_sleep_internal(
	clock_t                         clock,
	sleep_type_t            sleep_type,
	mach_timespec_t         *sleep_time)
{
	alarm_t                         alarm;
	mach_timespec_t         clock_time;
	kern_return_t           rvalue;
	int                                     chkstat;
	spl_t                           s;

	if (clock == CLOCK_NULL) {
		return KERN_INVALID_ARGUMENT;
	}

	if (clock != &clock_list[SYSTEM_CLOCK]) {
		return KERN_FAILURE;
	}

	/*
	 * Check sleep parameters. If parameters are invalid
	 * return an error, otherwise post alarm request.
	 */
	(*clock->cl_ops->c_gettime)(&clock_time);

	chkstat = check_time(sleep_type, sleep_time, &clock_time);
	if (chkstat < 0) {
		return KERN_INVALID_VALUE;
	}
	rvalue = KERN_SUCCESS;
	if (chkstat > 0) {
		wait_result_t wait_result;

		/*
		 * Get alarm and add to clock alarm list.
		 */

		LOCK_ALARM(s);
		if ((alarm = alrmfree) == 0) {
			UNLOCK_ALARM(s);
			alarm = zalloc_flags(alarm_zone, Z_WAITOK | Z_NOFAIL);
			LOCK_ALARM(s);
		} else {
			alrmfree = alarm->al_next;
		}

		/*
		 * Wait for alarm to occur.
		 */
		wait_result = assert_wait((event_t)alarm, THREAD_ABORTSAFE);
		if (wait_result == THREAD_WAITING) {
			alarm->al_time = *sleep_time;
			alarm->al_status = ALARM_SLEEP;
			post_alarm(alarm);
			UNLOCK_ALARM(s);

			wait_result = thread_block(THREAD_CONTINUE_NULL);

			/*
			 * Note if alarm expired normally or whether it
			 * was aborted. If aborted, delete alarm from
			 * clock alarm list. Return alarm to free list.
			 */
			LOCK_ALARM(s);
			if (alarm->al_status != ALARM_DONE) {
				assert(wait_result != THREAD_AWAKENED);
				if (((alarm->al_prev)->al_next = alarm->al_next) != NULL) {
					(alarm->al_next)->al_prev = alarm->al_prev;
				}
				rvalue = KERN_ABORTED;
			}
			*sleep_time = alarm->al_time;
			alarm->al_status = ALARM_FREE;
		} else {
			assert(wait_result == THREAD_INTERRUPTED);
			assert(alarm->al_status == ALARM_FREE);
			rvalue = KERN_ABORTED;
		}
		alarm->al_next = alrmfree;
		alrmfree = alarm;
		UNLOCK_ALARM(s);
	} else {
		*sleep_time = clock_time;
	}

	return rvalue;
}

/*
 * Service clock alarm expirations.
 */
static void
alarm_expire(void)
{
	clock_t                         clock;
	alarm_t alrm1;
	alarm_t alrm2;
	mach_timespec_t         clock_time;
	mach_timespec_t         *alarm_time;
	spl_t                           s;

	clock = &clock_list[SYSTEM_CLOCK];
	(*clock->cl_ops->c_gettime)(&clock_time);

	/*
	 * Update clock alarm list. Alarms that are due are moved
	 * to the alarmdone list to be serviced by a thread callout.
	 */
	LOCK_ALARM(s);
	alrm1 = (alarm_t)&alrmlist;
	while ((alrm2 = alrm1->al_next) != NULL) {
		alarm_time = &alrm2->al_time;
		if (CMP_MACH_TIMESPEC(alarm_time, &clock_time) > 0) {
			break;
		}

		/*
		 * Alarm has expired, so remove it from the
		 * clock alarm list.
		 */
		if ((alrm1->al_next = alrm2->al_next) != NULL) {
			(alrm1->al_next)->al_prev = alrm1;
		}

		/*
		 * If a clock_sleep() alarm, wakeup the thread
		 * which issued the clock_sleep() call.
		 */
		if (alrm2->al_status == ALARM_SLEEP) {
			alrm2->al_next = NULL;
			alrm2->al_status = ALARM_DONE;
			alrm2->al_time = clock_time;
			thread_wakeup((event_t)alrm2);
		}
		/*
		 * If a clock_alarm() alarm, place the alarm on
		 * the alarm done list and schedule the alarm
		 * delivery mechanism.
		 */
		else {
			assert(alrm2->al_status == ALARM_CLOCK);
			if ((alrm2->al_next = alrmdone) != NULL) {
				alrmdone->al_prev = alrm2;
			} else {
				thread_call_enter(&alarm_done_call);
			}
			alrm2->al_prev = (alarm_t)&alrmdone;
			alrmdone = alrm2;
			alrm2->al_status = ALARM_DONE;
			alrm2->al_time = clock_time;
		}
	}

	/*
	 * Setup to expire for the next pending alarm.
	 */
	if (alrm2) {
		set_alarm(alarm_time);
	}
	UNLOCK_ALARM(s);
}

static void
alarm_done(void)
{
	alarm_t alrm;
	kern_return_t           code;
	spl_t                           s;

	LOCK_ALARM(s);
	while ((alrm = alrmdone) != NULL) {
		if ((alrmdone = alrm->al_next) != NULL) {
			alrmdone->al_prev = (alarm_t)&alrmdone;
		}
		UNLOCK_ALARM(s);

		code = (alrm->al_status == ALARM_DONE? KERN_SUCCESS: KERN_ABORTED);
		if (alrm->al_port != IP_NULL) {
			/* Deliver message to designated port */
			if (IP_VALID(alrm->al_port)) {
				clock_alarm_reply(alrm->al_port, alrm->al_port_type, code,
				    alrm->al_type, alrm->al_time);
			}

			LOCK_ALARM(s);
			alrm->al_status = ALARM_FREE;
			alrm->al_next = alrmfree;
			alrmfree = alrm;
		} else {
			panic("clock_alarm_deliver");
		}
	}

	UNLOCK_ALARM(s);
}

/*
 * Post an alarm on the active alarm list.
 *
 * Always called from within a LOCK_ALARM() code section.
 */
static void
post_alarm(
	alarm_t                         alarm)
{
	alarm_t alrm1, alrm2;
	mach_timespec_t         *alarm_time;
	mach_timespec_t         *queue_time;

	/*
	 * Traverse alarm list until queue time is greater
	 * than alarm time, then insert alarm.
	 */
	alarm_time = &alarm->al_time;
	alrm1 = (alarm_t)&alrmlist;
	while ((alrm2 = alrm1->al_next) != NULL) {
		queue_time = &alrm2->al_time;
		if (CMP_MACH_TIMESPEC(queue_time, alarm_time) > 0) {
			break;
		}
		alrm1 = alrm2;
	}
	alrm1->al_next = alarm;
	alarm->al_next = alrm2;
	alarm->al_prev = alrm1;
	if (alrm2) {
		alrm2->al_prev  = alarm;
	}

	/*
	 * If the inserted alarm is the 'earliest' alarm,
	 * reset the device layer alarm time accordingly.
	 */
	if (alrmlist == alarm) {
		set_alarm(alarm_time);
	}
}

static void
set_alarm(
	mach_timespec_t         *alarm_time)
{
	uint64_t        abstime;

	nanotime_to_absolutetime(alarm_time->tv_sec, alarm_time->tv_nsec, &abstime);
	timer_call_enter_with_leeway(&alarm_expire_timer, NULL, abstime, 0, TIMER_CALL_USER_NORMAL, FALSE);
}

/*
 * Check the validity of 'alarm_time' and 'alarm_type'. If either
 * argument is invalid, return a negative value. If the 'alarm_time'
 * is now, return a 0 value. If the 'alarm_time' is in the future,
 * return a positive value.
 */
static int
check_time(
	alarm_type_t            alarm_type,
	mach_timespec_t         *alarm_time,
	mach_timespec_t         *clock_time)
{
	int                                     result;

	if (BAD_ALRMTYPE(alarm_type)) {
		return -1;
	}
	if (BAD_MACH_TIMESPEC(alarm_time)) {
		return -1;
	}
	if ((alarm_type & ALRMTYPE) == TIME_RELATIVE) {
		ADD_MACH_TIMESPEC(alarm_time, clock_time);
	}

	result = CMP_MACH_TIMESPEC(alarm_time, clock_time);

	return (result >= 0)? result: 0;
}

#ifndef __LP64__

mach_timespec_t
clock_get_system_value(void)
{
	clock_t                         clock = &clock_list[SYSTEM_CLOCK];
	mach_timespec_t         value;

	(void) (*clock->cl_ops->c_gettime)(&value);

	return value;
}

mach_timespec_t
clock_get_calendar_value(void)
{
	clock_t                         clock = &clock_list[CALENDAR_CLOCK];
	mach_timespec_t         value = MACH_TIMESPEC_ZERO;

	(void) (*clock->cl_ops->c_gettime)(&value);

	return value;
}

#endif  /* __LP64__ */

static struct alarm_base {
	spinlock_t		lock;
	struct timerqueue_head	timerqueue;
	ktime_t			(*get_ktime)(void);
	void			(*get_timespec)(struct timespec64 *tp);
	clockid_t		base_clockid;
} alarm_bases[ALARM_NUMTYPE];

#if defined(CONFIG_POSIX_TIMERS) || defined(CONFIG_RTC_CLASS)
/* freezer information to handle clock_nanosleep triggered wakeups */
static enum alarmtimer_type freezer_alarmtype;
static ktime_t freezer_expires;
static ktime_t freezer_delta;
static DEFINE_SPINLOCK(freezer_delta_lock);
#endif

#ifdef CONFIG_RTC_CLASS
/* rtc timer and device for setting alarm wakeups at suspend */
static struct rtc_timer		rtctimer;
static struct rtc_device	*rtcdev;
static DEFINE_SPINLOCK(rtcdev_lock);

/**
 * alarmtimer_get_rtcdev - Return selected rtcdevice
 *
 * This function returns the rtc device to use for wakealarms.
 */
struct rtc_device *alarmtimer_get_rtcdev(void)
{
	struct rtc_device *ret;

	guard(spinlock_irqsave)(&rtcdev_lock);
	ret = rtcdev;

	return ret;
}
EXPORT_SYMBOL_GPL(alarmtimer_get_rtcdev);

static int alarmtimer_rtc_add_device(struct device *dev)
{
	struct rtc_device *rtc = to_rtc_device(dev);
	struct platform_device *pdev;
	int ret = 0;

	if (rtcdev)
		return -EBUSY;

	if (!test_bit(RTC_FEATURE_ALARM, rtc->features))
		return -1;
	if (!device_may_wakeup(rtc->dev.parent))
		return -1;

	pdev = platform_device_register_data(dev, "alarmtimer",
					     PLATFORM_DEVID_AUTO, NULL, 0);
	if (!IS_ERR(pdev))
		device_init_wakeup(&pdev->dev, true);

	scoped_guard(spinlock_irqsave, &rtcdev_lock) {
		if (!IS_ERR(pdev) && !rtcdev && try_module_get(rtc->owner)) {
			rtcdev = rtc;
			/* hold a reference so it doesn't go away */
			get_device(dev);
			pdev = NULL;
		} else {
			ret = -1;
		}
	}

	platform_device_unregister(pdev);
	return ret;
}

static inline void alarmtimer_rtc_timer_init(void)
{
	rtc_timer_init(&rtctimer, NULL, NULL);
}

static struct class_interface alarmtimer_rtc_interface = {
	.add_dev = &alarmtimer_rtc_add_device,
};

static int alarmtimer_rtc_interface_setup(void)
{
	alarmtimer_rtc_interface.class = &rtc_class;
	return class_interface_register(&alarmtimer_rtc_interface);
}
static void alarmtimer_rtc_interface_remove(void)
{
	class_interface_unregister(&alarmtimer_rtc_interface);
}
#else
static inline int alarmtimer_rtc_interface_setup(void) { return 0; }
static inline void alarmtimer_rtc_interface_remove(void) { }
static inline void alarmtimer_rtc_timer_init(void) { }
#endif

/**
 * alarmtimer_enqueue - Adds an alarm timer to an alarm_base timerqueue
 * @base: pointer to the base where the timer is being run
 * @alarm: pointer to alarm being enqueued.
 *
 * Adds alarm to a alarm_base timerqueue
 *
 * Must hold base->lock when calling.
 */
static void alarmtimer_enqueue(struct alarm_base *base, struct alarm *alarm)
{
	if (alarm->state & ALARMTIMER_STATE_ENQUEUED)
		timerqueue_del(&base->timerqueue, &alarm->node);

	timerqueue_add(&base->timerqueue, &alarm->node);
	alarm->state |= ALARMTIMER_STATE_ENQUEUED;
}

/**
 * alarmtimer_dequeue - Removes an alarm timer from an alarm_base timerqueue
 * @base: pointer to the base where the timer is running
 * @alarm: pointer to alarm being removed
 *
 * Removes alarm to a alarm_base timerqueue
 *
 * Must hold base->lock when calling.
 */
static void alarmtimer_dequeue(struct alarm_base *base, struct alarm *alarm)
{
	if (!(alarm->state & ALARMTIMER_STATE_ENQUEUED))
		return;

	timerqueue_del(&base->timerqueue, &alarm->node);
	alarm->state &= ~ALARMTIMER_STATE_ENQUEUED;
}


/**
 * alarmtimer_fired - Handles alarm hrtimer being fired.
 * @timer: pointer to hrtimer being run
 *
 * When a alarm timer fires, this runs through the timerqueue to
 * see which alarms expired, and runs those. If there are more alarm
 * timers queued for the future, we set the hrtimer to fire when
 * the next future alarm timer expires.
 */
static enum hrtimer_restart alarmtimer_fired(struct hrtimer *timer)
{
	struct alarm *alarm = container_of(timer, struct alarm, timer);
	struct alarm_base *base = &alarm_bases[alarm->type];

	scoped_guard(spinlock_irqsave, &base->lock)
		alarmtimer_dequeue(base, alarm);

	if (alarm->function)
		alarm->function(alarm, base->get_ktime());

	trace_alarmtimer_fired(alarm, base->get_ktime());
	return HRTIMER_NORESTART;
}

ktime_t alarm_expires_remaining(const struct alarm *alarm)
{
	struct alarm_base *base = &alarm_bases[alarm->type];
	return ktime_sub(alarm->node.expires, base->get_ktime());
}
EXPORT_SYMBOL_GPL(alarm_expires_remaining);

#ifdef CONFIG_RTC_CLASS
/**
 * alarmtimer_suspend - Suspend time callback
 * @dev: unused
 *
 * When we are going into suspend, we look through the bases
 * to see which is the soonest timer to expire. We then
 * set an rtc timer to fire that far into the future, which
 * will wake us from suspend.
 */
static int alarmtimer_suspend(struct device *dev)
{
	ktime_t min, now, expires;
	struct rtc_device *rtc;
	struct rtc_time tm;
	int i, ret, type;

	scoped_guard(spinlock_irqsave, &freezer_delta_lock) {
		min = freezer_delta;
		expires = freezer_expires;
		type = freezer_alarmtype;
		freezer_delta = 0;
	}

	rtc = alarmtimer_get_rtcdev();
	/* If we have no rtcdev, just return */
	if (!rtc)
		return 0;

	/* Find the soonest timer to expire*/
	for (i = 0; i < ALARM_NUMTYPE; i++) {
		struct alarm_base *base = &alarm_bases[i];
		struct timerqueue_node *next;
		ktime_t delta;

		scoped_guard(spinlock_irqsave, &base->lock)
			next = timerqueue_getnext(&base->timerqueue);
		if (!next)
			continue;
		delta = ktime_sub(next->expires, base->get_ktime());
		if (!min || (delta < min)) {
			expires = next->expires;
			min = delta;
			type = i;
		}
	}
	if (min == 0)
		return 0;

	if (ktime_to_ns(min) < 2 * NSEC_PER_SEC) {
		pm_wakeup_event(dev, 2 * MSEC_PER_SEC);
		return -EBUSY;
	}

	trace_alarmtimer_suspend(expires, type);

	/* Setup an rtc timer to fire that far in the future */
	rtc_timer_cancel(rtc, &rtctimer);
	rtc_read_time(rtc, &tm);
	now = rtc_tm_to_ktime(tm);

	/*
	 * If the RTC alarm timer only supports a limited time offset, set the
	 * alarm time to the maximum supported value.
	 * The system may wake up earlier (possibly much earlier) than expected
	 * when the alarmtimer runs. This is the best the kernel can do if
	 * the alarmtimer exceeds the time that the rtc device can be programmed
	 * for.
	 */
	min = rtc_bound_alarmtime(rtc, min);

	now = ktime_add(now, min);

	/* Set alarm, if in the past reject suspend briefly to handle */
	ret = rtc_timer_start(rtc, &rtctimer, now, 0);
	if (ret < 0)
		pm_wakeup_event(dev, MSEC_PER_SEC);
	return ret;
}

static int alarmtimer_resume(struct device *dev)
{
	struct rtc_device *rtc;

	rtc = alarmtimer_get_rtcdev();
	if (rtc)
		rtc_timer_cancel(rtc, &rtctimer);
	return 0;
}

#else
static int alarmtimer_suspend(struct device *dev)
{
	return 0;
}

static int alarmtimer_resume(struct device *dev)
{
	return 0;
}
#endif

static void
__alarm_init(struct alarm *alarm, enum alarmtimer_type type,
	     void (*function)(struct alarm *, ktime_t))
{
	timerqueue_init(&alarm->node);
	alarm->function = function;
	alarm->type = type;
	alarm->state = ALARMTIMER_STATE_INACTIVE;
}

/**
 * alarm_init - Initialize an alarm structure
 * @alarm: ptr to alarm to be initialized
 * @type: the type of the alarm
 * @function: callback that is run when the alarm fires
 */
void alarm_init(struct alarm *alarm, enum alarmtimer_type type,
		void (*function)(struct alarm *, ktime_t))
{
	hrtimer_setup(&alarm->timer, alarmtimer_fired, alarm_bases[type].base_clockid,
		      HRTIMER_MODE_ABS);
	__alarm_init(alarm, type, function);
}
EXPORT_SYMBOL_GPL(alarm_init);

/**
 * alarm_start - Sets an absolute alarm to fire
 * @alarm: ptr to alarm to set
 * @start: time to run the alarm
 */
void alarm_start(struct alarm *alarm, ktime_t start)
{
	struct alarm_base *base = &alarm_bases[alarm->type];

	scoped_guard(spinlock_irqsave, &base->lock) {
		alarm->node.expires = start;
		alarmtimer_enqueue(base, alarm);
		hrtimer_start(&alarm->timer, alarm->node.expires, HRTIMER_MODE_ABS);
	}

	trace_alarmtimer_start(alarm, base->get_ktime());
}
EXPORT_SYMBOL_GPL(alarm_start);

/**
 * alarm_start_relative - Sets a relative alarm to fire
 * @alarm: ptr to alarm to set
 * @start: time relative to now to run the alarm
 */
void alarm_start_relative(struct alarm *alarm, ktime_t start)
{
	struct alarm_base *base = &alarm_bases[alarm->type];

	start = ktime_add_safe(start, base->get_ktime());
	alarm_start(alarm, start);
}
EXPORT_SYMBOL_GPL(alarm_start_relative);

void alarm_restart(struct alarm *alarm)
{
	struct alarm_base *base = &alarm_bases[alarm->type];

	guard(spinlock_irqsave)(&base->lock);
	hrtimer_set_expires(&alarm->timer, alarm->node.expires);
	hrtimer_restart(&alarm->timer);
	alarmtimer_enqueue(base, alarm);
}
EXPORT_SYMBOL_GPL(alarm_restart);

/**
 * alarm_try_to_cancel - Tries to cancel an alarm timer
 * @alarm: ptr to alarm to be canceled
 *
 * Returns 1 if the timer was canceled, 0 if it was not running,
 * and -1 if the callback was running
 */
int alarm_try_to_cancel(struct alarm *alarm)
{
	struct alarm_base *base = &alarm_bases[alarm->type];
	int ret;

	scoped_guard(spinlock_irqsave, &base->lock) {
		ret = hrtimer_try_to_cancel(&alarm->timer);
		if (ret >= 0)
			alarmtimer_dequeue(base, alarm);
	}

	trace_alarmtimer_cancel(alarm, base->get_ktime());
	return ret;
}
EXPORT_SYMBOL_GPL(alarm_try_to_cancel);


/**
 * alarm_cancel - Spins trying to cancel an alarm timer until it is done
 * @alarm: ptr to alarm to be canceled
 *
 * Returns 1 if the timer was canceled, 0 if it was not active.
 */
int alarm_cancel(struct alarm *alarm)
{
	for (;;) {
		int ret = alarm_try_to_cancel(alarm);
		if (ret >= 0)
			return ret;
		hrtimer_cancel_wait_running(&alarm->timer);
	}
}
EXPORT_SYMBOL_GPL(alarm_cancel);


u64 alarm_forward(struct alarm *alarm, ktime_t now, ktime_t interval)
{
	u64 overrun = 1;
	ktime_t delta;

	delta = ktime_sub(now, alarm->node.expires);

	if (delta < 0)
		return 0;

	if (unlikely(delta >= interval)) {
		s64 incr = ktime_to_ns(interval);

		overrun = ktime_divns(delta, incr);

		alarm->node.expires = ktime_add_ns(alarm->node.expires,
							incr*overrun);

		if (alarm->node.expires > now)
			return overrun;
		/*
		 * This (and the ktime_add() below) is the
		 * correction for exact:
		 */
		overrun++;
	}

	alarm->node.expires = ktime_add_safe(alarm->node.expires, interval);
	return overrun;
}
EXPORT_SYMBOL_GPL(alarm_forward);

u64 alarm_forward_now(struct alarm *alarm, ktime_t interval)
{
	struct alarm_base *base = &alarm_bases[alarm->type];

	return alarm_forward(alarm, base->get_ktime(), interval);
}
EXPORT_SYMBOL_GPL(alarm_forward_now);

#ifdef CONFIG_POSIX_TIMERS

static void alarmtimer_freezerset(ktime_t absexp, enum alarmtimer_type type)
{
	struct alarm_base *base;
	ktime_t delta;

	switch(type) {
	case ALARM_REALTIME:
		base = &alarm_bases[ALARM_REALTIME];
		type = ALARM_REALTIME_FREEZER;
		break;
	case ALARM_BOOTTIME:
		base = &alarm_bases[ALARM_BOOTTIME];
		type = ALARM_BOOTTIME_FREEZER;
		break;
	default:
		WARN_ONCE(1, "Invalid alarm type: %d\n", type);
		return;
	}

	delta = ktime_sub(absexp, base->get_ktime());

	guard(spinlock_irqsave)(&freezer_delta_lock);
	if (!freezer_delta || (delta < freezer_delta)) {
		freezer_delta = delta;
		freezer_expires = absexp;
		freezer_alarmtype = type;
	}
}

/**
 * clock2alarm - helper that converts from clockid to alarmtypes
 * @clockid: clockid.
 */
static enum alarmtimer_type clock2alarm(clockid_t clockid)
{
	if (clockid == CLOCK_REALTIME_ALARM)
		return ALARM_REALTIME;

	WARN_ON_ONCE(clockid != CLOCK_BOOTTIME_ALARM);
	return ALARM_BOOTTIME;
}

/**
 * alarm_handle_timer - Callback for posix timers
 * @alarm: alarm that fired
 * @now: time at the timer expiration
 *
 * Posix timer callback for expired alarm timers.
 *
 * Return: whether the timer is to be restarted
 */
static void alarm_handle_timer(struct alarm *alarm, ktime_t now)
{
	struct k_itimer *ptr = container_of(alarm, struct k_itimer, it.alarm.alarmtimer);

	guard(spinlock_irqsave)(&ptr->it_lock);
	posix_timer_queue_signal(ptr);
}

/**
 * alarm_timer_rearm - Posix timer callback for rearming timer
 * @timr:	Pointer to the posixtimer data struct
 */
static void alarm_timer_rearm(struct k_itimer *timr)
{
	struct alarm *alarm = &timr->it.alarm.alarmtimer;

	timr->it_overrun += alarm_forward_now(alarm, timr->it_interval);
	alarm_start(alarm, alarm->node.expires);
}

/**
 * alarm_timer_forward - Posix timer callback for forwarding timer
 * @timr:	Pointer to the posixtimer data struct
 * @now:	Current time to forward the timer against
 */
static s64 alarm_timer_forward(struct k_itimer *timr, ktime_t now)
{
	struct alarm *alarm = &timr->it.alarm.alarmtimer;

	return alarm_forward(alarm, timr->it_interval, now);
}

/**
 * alarm_timer_remaining - Posix timer callback to retrieve remaining time
 * @timr:	Pointer to the posixtimer data struct
 * @now:	Current time to calculate against
 */
static ktime_t alarm_timer_remaining(struct k_itimer *timr, ktime_t now)
{
	struct alarm *alarm = &timr->it.alarm.alarmtimer;

	return ktime_sub(alarm->node.expires, now);
}

/**
 * alarm_timer_try_to_cancel - Posix timer callback to cancel a timer
 * @timr:	Pointer to the posixtimer data struct
 */
static int alarm_timer_try_to_cancel(struct k_itimer *timr)
{
	return alarm_try_to_cancel(&timr->it.alarm.alarmtimer);
}

/**
 * alarm_timer_wait_running - Posix timer callback to wait for a timer
 * @timr:	Pointer to the posixtimer data struct
 *
 * Called from the core code when timer cancel detected that the callback
 * is running. @timr is unlocked and rcu read lock is held to prevent it
 * from being freed.
 */
static void alarm_timer_wait_running(struct k_itimer *timr)
{
	hrtimer_cancel_wait_running(&timr->it.alarm.alarmtimer.timer);
}

/**
 * alarm_timer_arm - Posix timer callback to arm a timer
 * @timr:	Pointer to the posixtimer data struct
 * @expires:	The new expiry time
 * @absolute:	Expiry value is absolute time
 * @sigev_none:	Posix timer does not deliver signals
 */
static void alarm_timer_arm(struct k_itimer *timr, ktime_t expires,
			    bool absolute, bool sigev_none)
{
	struct alarm *alarm = &timr->it.alarm.alarmtimer;
	struct alarm_base *base = &alarm_bases[alarm->type];

	if (!absolute)
		expires = ktime_add_safe(expires, base->get_ktime());
	if (sigev_none)
		alarm->node.expires = expires;
	else
		alarm_start(&timr->it.alarm.alarmtimer, expires);
}

/**
 * alarm_clock_getres - posix getres interface
 * @which_clock: clockid
 * @tp: timespec to fill
 *
 * Returns the granularity of underlying alarm base clock
 */
static int alarm_clock_getres(const clockid_t which_clock, struct timespec64 *tp)
{
	if (!alarmtimer_get_rtcdev())
		return -EINVAL;

	tp->tv_sec = 0;
	tp->tv_nsec = hrtimer_resolution;
	return 0;
}

/**
 * alarm_clock_get_timespec - posix clock_get_timespec interface
 * @which_clock: clockid
 * @tp: timespec to fill.
 *
 * Provides the underlying alarm base time in a tasks time namespace.
 */
static int alarm_clock_get_timespec(clockid_t which_clock, struct timespec64 *tp)
{
	struct alarm_base *base = &alarm_bases[clock2alarm(which_clock)];

	if (!alarmtimer_get_rtcdev())
		return -EINVAL;

	base->get_timespec(tp);

	return 0;
}

/**
 * alarm_clock_get_ktime - posix clock_get_ktime interface
 * @which_clock: clockid
 *
 * Provides the underlying alarm base time in the root namespace.
 */
static ktime_t alarm_clock_get_ktime(clockid_t which_clock)
{
	struct alarm_base *base = &alarm_bases[clock2alarm(which_clock)];

	if (!alarmtimer_get_rtcdev())
		return -EINVAL;

	return base->get_ktime();
}

/**
 * alarm_timer_create - posix timer_create interface
 * @new_timer: k_itimer pointer to manage
 *
 * Initializes the k_itimer structure.
 */
static int alarm_timer_create(struct k_itimer *new_timer)
{
	enum  alarmtimer_type type;

	if (!alarmtimer_get_rtcdev())
		return -EOPNOTSUPP;

	if (!capable(CAP_WAKE_ALARM))
		return -EPERM;

	type = clock2alarm(new_timer->it_clock);
	alarm_init(&new_timer->it.alarm.alarmtimer, type, alarm_handle_timer);
	return 0;
}

/**
 * alarmtimer_nsleep_wakeup - Wakeup function for alarm_timer_nsleep
 * @alarm: ptr to alarm that fired
 * @now: time at the timer expiration
 *
 * Wakes up the task that set the alarmtimer
 */
static void alarmtimer_nsleep_wakeup(struct alarm *alarm, ktime_t now)
{
	struct task_struct *task = alarm->data;

	alarm->data = NULL;
	if (task)
		wake_up_process(task);
}

/**
 * alarmtimer_do_nsleep - Internal alarmtimer nsleep implementation
 * @alarm: ptr to alarmtimer
 * @absexp: absolute expiration time
 * @type: alarm type (BOOTTIME/REALTIME).
 *
 * Sets the alarm timer and sleeps until it is fired or interrupted.
 */
static int alarmtimer_do_nsleep(struct alarm *alarm, ktime_t absexp,
				enum alarmtimer_type type)
{
	struct restart_block *restart;
	alarm->data = (void *)current;
	do {
		set_current_state(TASK_INTERRUPTIBLE);
		alarm_start(alarm, absexp);
		if (likely(alarm->data))
			schedule();

		alarm_cancel(alarm);
	} while (alarm->data && !signal_pending(current));

	__set_current_state(TASK_RUNNING);

	destroy_hrtimer_on_stack(&alarm->timer);

	if (!alarm->data)
		return 0;

	if (freezing(current))
		alarmtimer_freezerset(absexp, type);
	restart = &current->restart_block;
	if (restart->nanosleep.type != TT_NONE) {
		struct timespec64 rmt;
		ktime_t rem;

		rem = ktime_sub(absexp, alarm_bases[type].get_ktime());

		if (rem <= 0)
			return 0;
		rmt = ktime_to_timespec64(rem);

		return nanosleep_copyout(restart, &rmt);
	}
	return -ERESTART_RESTARTBLOCK;
}

static void
alarm_init_on_stack(struct alarm *alarm, enum alarmtimer_type type,
		    void (*function)(struct alarm *, ktime_t))
{
	hrtimer_setup_on_stack(&alarm->timer, alarmtimer_fired, alarm_bases[type].base_clockid,
			       HRTIMER_MODE_ABS);
	__alarm_init(alarm, type, function);
}

/**
 * alarm_timer_nsleep_restart - restartblock alarmtimer nsleep
 * @restart: ptr to restart block
 *
 * Handles restarted clock_nanosleep calls
 */
static long __sched alarm_timer_nsleep_restart(struct restart_block *restart)
{
	enum  alarmtimer_type type = restart->nanosleep.clockid;
	ktime_t exp = restart->nanosleep.expires;
	struct alarm alarm;

	alarm_init_on_stack(&alarm, type, alarmtimer_nsleep_wakeup);

	return alarmtimer_do_nsleep(&alarm, exp, type);
}

/**
 * alarm_timer_nsleep - alarmtimer nanosleep
 * @which_clock: clockid
 * @flags: determines abstime or relative
 * @tsreq: requested sleep time (abs or rel)
 *
 * Handles clock_nanosleep calls against _ALARM clockids
 */
static int alarm_timer_nsleep(const clockid_t which_clock, int flags,
			      const struct timespec64 *tsreq)
{
	enum  alarmtimer_type type = clock2alarm(which_clock);
	struct restart_block *restart = &current->restart_block;
	struct alarm alarm;
	ktime_t exp;
	int ret;

	if (!alarmtimer_get_rtcdev())
		return -EOPNOTSUPP;

	if (flags & ~TIMER_ABSTIME)
		return -EINVAL;

	if (!capable(CAP_WAKE_ALARM))
		return -EPERM;

	alarm_init_on_stack(&alarm, type, alarmtimer_nsleep_wakeup);

	exp = timespec64_to_ktime(*tsreq);
	/* Convert (if necessary) to absolute time */
	if (flags != TIMER_ABSTIME) {
		ktime_t now = alarm_bases[type].get_ktime();

		exp = ktime_add_safe(now, exp);
	} else {
		exp = timens_ktime_to_host(which_clock, exp);
	}

	ret = alarmtimer_do_nsleep(&alarm, exp, type);
	if (ret != -ERESTART_RESTARTBLOCK)
		return ret;

	/* abs timers don't set remaining time or restart */
	if (flags == TIMER_ABSTIME)
		return -ERESTARTNOHAND;

	restart->nanosleep.clockid = type;
	restart->nanosleep.expires = exp;
	set_restart_fn(restart, alarm_timer_nsleep_restart);
	return ret;
}

const struct k_clock alarm_clock = {
	.clock_getres		= alarm_clock_getres,
	.clock_get_ktime	= alarm_clock_get_ktime,
	.clock_get_timespec	= alarm_clock_get_timespec,
	.timer_create		= alarm_timer_create,
	.timer_set		= common_timer_set,
	.timer_del		= common_timer_del,
	.timer_get		= common_timer_get,
	.timer_arm		= alarm_timer_arm,
	.timer_rearm		= alarm_timer_rearm,
	.timer_forward		= alarm_timer_forward,
	.timer_remaining	= alarm_timer_remaining,
	.timer_try_to_cancel	= alarm_timer_try_to_cancel,
	.timer_wait_running	= alarm_timer_wait_running,
	.nsleep			= alarm_timer_nsleep,
};
#endif /* CONFIG_POSIX_TIMERS */


/* Suspend hook structures */
static const struct dev_pm_ops alarmtimer_pm_ops = {
	.suspend = alarmtimer_suspend,
	.resume = alarmtimer_resume,
};

static struct platform_driver alarmtimer_driver = {
	.driver = {
		.name = "alarmtimer",
		.pm = &alarmtimer_pm_ops,
	}
};

static void get_boottime_timespec(struct timespec64 *tp)
{
	ktime_get_boottime_ts64(tp);
	timens_add_boottime(tp);
}

/**
 * alarmtimer_init - Initialize alarm timer code
 *
 * This function initializes the alarm bases and registers
 * the posix clock ids.
 */
static int __init alarmtimer_init(void)
{
	int error;
	int i;

	alarmtimer_rtc_timer_init();

	/* Initialize alarm bases */
	alarm_bases[ALARM_REALTIME].base_clockid = CLOCK_REALTIME;
	alarm_bases[ALARM_REALTIME].get_ktime = &ktime_get_real;
	alarm_bases[ALARM_REALTIME].get_timespec = ktime_get_real_ts64;
	alarm_bases[ALARM_BOOTTIME].base_clockid = CLOCK_BOOTTIME;
	alarm_bases[ALARM_BOOTTIME].get_ktime = &ktime_get_boottime;
	alarm_bases[ALARM_BOOTTIME].get_timespec = get_boottime_timespec;
	for (i = 0; i < ALARM_NUMTYPE; i++) {
		timerqueue_init_head(&alarm_bases[i].timerqueue);
		spin_lock_init(&alarm_bases[i].lock);
	}

	error = alarmtimer_rtc_interface_setup();
	if (error)
		return error;

	error = platform_driver_register(&alarmtimer_driver);
	if (error)
		goto out_if;

	return 0;
out_if:
	alarmtimer_rtc_interface_remove();
	return error;
}
device_initcall(alarmtimer_init);

static LIST_HEAD(clockevent_devices);
static LIST_HEAD(clockevents_released);
/* Protection for the above */
static DEFINE_RAW_SPINLOCK(clockevents_lock);
/* Protection for unbind operations */
static DEFINE_MUTEX(clockevents_mutex);

struct ce_unbind {
	struct clock_event_device *ce;
	int res;
};

static u64 cev_delta2ns(unsigned long latch, struct clock_event_device *evt,
			bool ismax)
{
	u64 clc = (u64) latch << evt->shift;
	u64 rnd;

	if (WARN_ON(!evt->mult))
		evt->mult = 1;
	rnd = (u64) evt->mult - 1;

	/*
	 * Upper bound sanity check. If the backwards conversion is
	 * not equal latch, we know that the above shift overflowed.
	 */
	if ((clc >> evt->shift) != (u64)latch)
		clc = ~0ULL;

	/*
	 * Scaled math oddities:
	 *
	 * For mult <= (1 << shift) we can safely add mult - 1 to
	 * prevent integer rounding loss. So the backwards conversion
	 * from nsec to device ticks will be correct.
	 *
	 * For mult > (1 << shift), i.e. device frequency is > 1GHz we
	 * need to be careful. Adding mult - 1 will result in a value
	 * which when converted back to device ticks can be larger
	 * than latch by up to (mult - 1) >> shift. For the min_delta
	 * calculation we still want to apply this in order to stay
	 * above the minimum device ticks limit. For the upper limit
	 * we would end up with a latch value larger than the upper
	 * limit of the device, so we omit the add to stay below the
	 * device upper boundary.
	 *
	 * Also omit the add if it would overflow the u64 boundary.
	 */
	if ((~0ULL - clc > rnd) &&
	    (!ismax || evt->mult <= (1ULL << evt->shift)))
		clc += rnd;

	do_div(clc, evt->mult);

	/* Deltas less than 1usec are pointless noise */
	return clc > 1000 ? clc : 1000;
}

/**
 * clockevent_delta2ns - Convert a latch value (device ticks) to nanoseconds
 * @latch:	value to convert
 * @evt:	pointer to clock event device descriptor
 *
 * Math helper, returns latch value converted to nanoseconds (bound checked)
 */
u64 clockevent_delta2ns(unsigned long latch, struct clock_event_device *evt)
{
	return cev_delta2ns(latch, evt, false);
}
EXPORT_SYMBOL_GPL(clockevent_delta2ns);

static int __clockevents_switch_state(struct clock_event_device *dev,
				      enum clock_event_state state)
{
	if (dev->features & CLOCK_EVT_FEAT_DUMMY)
		return 0;

	/* Transition with new state-specific callbacks */
	switch (state) {
	case CLOCK_EVT_STATE_DETACHED:
		/* The clockevent device is getting replaced. Shut it down. */

	case CLOCK_EVT_STATE_SHUTDOWN:
		if (dev->set_state_shutdown)
			return dev->set_state_shutdown(dev);
		return 0;

	case CLOCK_EVT_STATE_PERIODIC:
		/* Core internal bug */
		if (!(dev->features & CLOCK_EVT_FEAT_PERIODIC))
			return -ENOSYS;
		if (dev->set_state_periodic)
			return dev->set_state_periodic(dev);
		return 0;

	case CLOCK_EVT_STATE_ONESHOT:
		/* Core internal bug */
		if (!(dev->features & CLOCK_EVT_FEAT_ONESHOT))
			return -ENOSYS;
		if (dev->set_state_oneshot)
			return dev->set_state_oneshot(dev);
		return 0;

	case CLOCK_EVT_STATE_ONESHOT_STOPPED:
		/* Core internal bug */
		if (WARN_ONCE(!clockevent_state_oneshot(dev),
			      "Current state: %d\n",
			      clockevent_get_state(dev)))
			return -EINVAL;

		if (dev->set_state_oneshot_stopped)
			return dev->set_state_oneshot_stopped(dev);
		else
			return -ENOSYS;

	default:
		return -ENOSYS;
	}
}

/**
 * clockevents_switch_state - set the operating state of a clock event device
 * @dev:	device to modify
 * @state:	new state
 *
 * Must be called with interrupts disabled !
 */
void clockevents_switch_state(struct clock_event_device *dev,
			      enum clock_event_state state)
{
	if (clockevent_get_state(dev) != state) {
		if (__clockevents_switch_state(dev, state))
			return;

		clockevent_set_state(dev, state);

		/*
		 * A nsec2cyc multiplicator of 0 is invalid and we'd crash
		 * on it, so fix it up and emit a warning:
		 */
		if (clockevent_state_oneshot(dev)) {
			if (WARN_ON(!dev->mult))
				dev->mult = 1;
		}
	}
}

/**
 * clockevents_shutdown - shutdown the device and clear next_event
 * @dev:	device to shutdown
 */
void clockevents_shutdown(struct clock_event_device *dev)
{
	clockevents_switch_state(dev, CLOCK_EVT_STATE_SHUTDOWN);
	dev->next_event = KTIME_MAX;
}

/**
 * clockevents_tick_resume -	Resume the tick device before using it again
 * @dev:			device to resume
 */
int clockevents_tick_resume(struct clock_event_device *dev)
{
	int ret = 0;

	if (dev->tick_resume)
		ret = dev->tick_resume(dev);

	return ret;
}

#ifdef CONFIG_GENERIC_CLOCKEVENTS_MIN_ADJUST

/* Limit min_delta to a jiffy */
#define MIN_DELTA_LIMIT		(NSEC_PER_SEC / HZ)

/**
 * clockevents_increase_min_delta - raise minimum delta of a clock event device
 * @dev:       device to increase the minimum delta
 *
 * Returns 0 on success, -ETIME when the minimum delta reached the limit.
 */
static int clockevents_increase_min_delta(struct clock_event_device *dev)
{
	/* Nothing to do if we already reached the limit */
	if (dev->min_delta_ns >= MIN_DELTA_LIMIT) {
		printk_deferred(KERN_WARNING
				"CE: Reprogramming failure. Giving up\n");
		dev->next_event = KTIME_MAX;
		return -ETIME;
	}

	if (dev->min_delta_ns < 5000)
		dev->min_delta_ns = 5000;
	else
		dev->min_delta_ns += dev->min_delta_ns >> 1;

	if (dev->min_delta_ns > MIN_DELTA_LIMIT)
		dev->min_delta_ns = MIN_DELTA_LIMIT;

	printk_deferred(KERN_WARNING
			"CE: %s increased min_delta_ns to %llu nsec\n",
			dev->name ? dev->name : "?",
			(unsigned long long) dev->min_delta_ns);
	return 0;
}

/**
 * clockevents_program_min_delta - Set clock event device to the minimum delay.
 * @dev:	device to program
 *
 * Returns 0 on success, -ETIME when the retry loop failed.
 */
static int clockevents_program_min_delta(struct clock_event_device *dev)
{
	unsigned long long clc;
	int64_t delta;
	int i;

	for (i = 0;;) {
		delta = dev->min_delta_ns;
		dev->next_event = ktime_add_ns(ktime_get(), delta);

		if (clockevent_state_shutdown(dev))
			return 0;

		dev->retries++;
		clc = ((unsigned long long) delta * dev->mult) >> dev->shift;
		if (dev->set_next_event((unsigned long) clc, dev) == 0)
			return 0;

		if (++i > 2) {
			/*
			 * We tried 3 times to program the device with the
			 * given min_delta_ns. Try to increase the minimum
			 * delta, if that fails as well get out of here.
			 */
			if (clockevents_increase_min_delta(dev))
				return -ETIME;
			i = 0;
		}
	}
}

#else  /* CONFIG_GENERIC_CLOCKEVENTS_MIN_ADJUST */

/**
 * clockevents_program_min_delta - Set clock event device to the minimum delay.
 * @dev:	device to program
 *
 * Returns 0 on success, -ETIME when the retry loop failed.
 */
static int clockevents_program_min_delta(struct clock_event_device *dev)
{
	unsigned long long clc;
	int64_t delta = 0;
	int i;

	for (i = 0; i < 10; i++) {
		delta += dev->min_delta_ns;
		dev->next_event = ktime_add_ns(ktime_get(), delta);

		if (clockevent_state_shutdown(dev))
			return 0;

		dev->retries++;
		clc = ((unsigned long long) delta * dev->mult) >> dev->shift;
		if (dev->set_next_event((unsigned long) clc, dev) == 0)
			return 0;
	}
	return -ETIME;
}

#endif /* CONFIG_GENERIC_CLOCKEVENTS_MIN_ADJUST */

/**
 * clockevents_program_event - Reprogram the clock event device.
 * @dev:	device to program
 * @expires:	absolute expiry time (monotonic clock)
 * @force:	program minimum delay if expires can not be set
 *
 * Returns 0 on success, -ETIME when the event is in the past.
 */
int clockevents_program_event(struct clock_event_device *dev, ktime_t expires,
			      bool force)
{
	unsigned long long clc;
	int64_t delta;
	int rc;

	if (WARN_ON_ONCE(expires < 0))
		return -ETIME;

	dev->next_event = expires;

	if (clockevent_state_shutdown(dev))
		return 0;

	/* We must be in ONESHOT state here */
	WARN_ONCE(!clockevent_state_oneshot(dev), "Current state: %d\n",
		  clockevent_get_state(dev));

	/* Shortcut for clockevent devices that can deal with ktime. */
	if (dev->features & CLOCK_EVT_FEAT_KTIME)
		return dev->set_next_ktime(expires, dev);

	delta = ktime_to_ns(ktime_sub(expires, ktime_get()));
	if (delta <= 0)
		return force ? clockevents_program_min_delta(dev) : -ETIME;

	delta = min(delta, (int64_t) dev->max_delta_ns);
	delta = max(delta, (int64_t) dev->min_delta_ns);

	clc = ((unsigned long long) delta * dev->mult) >> dev->shift;
	rc = dev->set_next_event((unsigned long) clc, dev);

	return (rc && force) ? clockevents_program_min_delta(dev) : rc;
}

/*
 * Called after a clockevent has been added which might
 * have replaced a current regular or broadcast device. A
 * released normal device might be a suitable replacement
 * for the current broadcast device. Similarly a released
 * broadcast device might be a suitable replacement for a
 * normal device.
 */
static void clockevents_notify_released(void)
{
	struct clock_event_device *dev;

	/*
	 * Keep iterating as long as tick_check_new_device()
	 * replaces a device.
	 */
	while (!list_empty(&clockevents_released)) {
		dev = list_entry(clockevents_released.next,
				 struct clock_event_device, list);
		list_move(&dev->list, &clockevent_devices);
		tick_check_new_device(dev);
	}
}

/*
 * Try to install a replacement clock event device
 */
static int clockevents_replace(struct clock_event_device *ced)
{
	struct clock_event_device *dev, *newdev = NULL;

	list_for_each_entry(dev, &clockevent_devices, list) {
		if (dev == ced || !clockevent_state_detached(dev))
			continue;

		if (!tick_check_replacement(newdev, dev))
			continue;

		if (!try_module_get(dev->owner))
			continue;

		if (newdev)
			module_put(newdev->owner);
		newdev = dev;
	}
	if (newdev) {
		tick_install_replacement(newdev);
		list_del_init(&ced->list);
	}
	return newdev ? 0 : -EBUSY;
}

/*
 * Called with clockevents_mutex and clockevents_lock held
 */
static int __clockevents_try_unbind(struct clock_event_device *ced, int cpu)
{
	/* Fast track. Device is unused */
	if (clockevent_state_detached(ced)) {
		list_del_init(&ced->list);
		return 0;
	}

	return ced == per_cpu(tick_cpu_device, cpu).evtdev ? -EAGAIN : -EBUSY;
}

/*
 * SMP function call to unbind a device
 */
static void __clockevents_unbind(void *arg)
{
	struct ce_unbind *cu = arg;
	int res;

	raw_spin_lock(&clockevents_lock);
	res = __clockevents_try_unbind(cu->ce, smp_processor_id());
	if (res == -EAGAIN)
		res = clockevents_replace(cu->ce);
	cu->res = res;
	raw_spin_unlock(&clockevents_lock);
}

/*
 * Issues smp function call to unbind a per cpu device. Called with
 * clockevents_mutex held.
 */
static int clockevents_unbind(struct clock_event_device *ced, int cpu)
{
	struct ce_unbind cu = { .ce = ced, .res = -ENODEV };

	smp_call_function_single(cpu, __clockevents_unbind, &cu, 1);
	return cu.res;
}

/*
 * Unbind a clockevents device.
 */
int clockevents_unbind_device(struct clock_event_device *ced, int cpu)
{
	int ret;

	mutex_lock(&clockevents_mutex);
	ret = clockevents_unbind(ced, cpu);
	mutex_unlock(&clockevents_mutex);
	return ret;
}
EXPORT_SYMBOL_GPL(clockevents_unbind_device);

/**
 * clockevents_register_device - register a clock event device
 * @dev:	device to register
 */
void clockevents_register_device(struct clock_event_device *dev)
{
	unsigned long flags;

	/* Initialize state to DETACHED */
	clockevent_set_state(dev, CLOCK_EVT_STATE_DETACHED);

	if (!dev->cpumask) {
		WARN_ON(num_possible_cpus() > 1);
		dev->cpumask = cpumask_of(smp_processor_id());
	}

	if (dev->cpumask == cpu_all_mask) {
		WARN(1, "%s cpumask == cpu_all_mask, using cpu_possible_mask instead\n",
		     dev->name);
		dev->cpumask = cpu_possible_mask;
	}

	raw_spin_lock_irqsave(&clockevents_lock, flags);

	list_add(&dev->list, &clockevent_devices);
	tick_check_new_device(dev);
	clockevents_notify_released();

	raw_spin_unlock_irqrestore(&clockevents_lock, flags);
}
EXPORT_SYMBOL_GPL(clockevents_register_device);

static void clockevents_config(struct clock_event_device *dev, u32 freq)
{
	u64 sec;

	if (!(dev->features & CLOCK_EVT_FEAT_ONESHOT))
		return;

	/*
	 * Calculate the maximum number of seconds we can sleep. Limit
	 * to 10 minutes for hardware which can program more than
	 * 32bit ticks so we still get reasonable conversion values.
	 */
	sec = dev->max_delta_ticks;
	do_div(sec, freq);
	if (!sec)
		sec = 1;
	else if (sec > 600 && dev->max_delta_ticks > UINT_MAX)
		sec = 600;

	clockevents_calc_mult_shift(dev, freq, sec);
	dev->min_delta_ns = cev_delta2ns(dev->min_delta_ticks, dev, false);
	dev->max_delta_ns = cev_delta2ns(dev->max_delta_ticks, dev, true);
}

/**
 * clockevents_config_and_register - Configure and register a clock event device
 * @dev:	device to register
 * @freq:	The clock frequency
 * @min_delta:	The minimum clock ticks to program in oneshot mode
 * @max_delta:	The maximum clock ticks to program in oneshot mode
 *
 * min/max_delta can be 0 for devices which do not support oneshot mode.
 */
void clockevents_config_and_register(struct clock_event_device *dev,
				     u32 freq, unsigned long min_delta,
				     unsigned long max_delta)
{
	dev->min_delta_ticks = min_delta;
	dev->max_delta_ticks = max_delta;
	clockevents_config(dev, freq);
	clockevents_register_device(dev);
}
EXPORT_SYMBOL_GPL(clockevents_config_and_register);

int __clockevents_update_freq(struct clock_event_device *dev, u32 freq)
{
	clockevents_config(dev, freq);

	if (clockevent_state_oneshot(dev))
		return clockevents_program_event(dev, dev->next_event, false);

	if (clockevent_state_periodic(dev))
		return __clockevents_switch_state(dev, CLOCK_EVT_STATE_PERIODIC);

	return 0;
}

/**
 * clockevents_update_freq - Update frequency and reprogram a clock event device.
 * @dev:	device to modify
 * @freq:	new device frequency
 *
 * Reconfigure and reprogram a clock event device in oneshot
 * mode. Must be called on the cpu for which the device delivers per
 * cpu timer events. If called for the broadcast device the core takes
 * care of serialization.
 *
 * Returns 0 on success, -ETIME when the event is in the past.
 */
int clockevents_update_freq(struct clock_event_device *dev, u32 freq)
{
	unsigned long flags;
	int ret;

	local_irq_save(flags);
	ret = tick_broadcast_update_freq(dev, freq);
	if (ret == -ENODEV)
		ret = __clockevents_update_freq(dev, freq);
	local_irq_restore(flags);
	return ret;
}

/*
 * Noop handler when we shut down an event device
 */
void clockevents_handle_noop(struct clock_event_device *dev)
{
}

/**
 * clockevents_exchange_device - release and request clock devices
 * @old:	device to release (can be NULL)
 * @new:	device to request (can be NULL)
 *
 * Called from various tick functions with clockevents_lock held and
 * interrupts disabled.
 */
void clockevents_exchange_device(struct clock_event_device *old,
				 struct clock_event_device *new)
{
	/*
	 * Caller releases a clock event device. We queue it into the
	 * released list and do a notify add later.
	 */
	if (old) {
		module_put(old->owner);
		clockevents_switch_state(old, CLOCK_EVT_STATE_DETACHED);
		list_move(&old->list, &clockevents_released);
	}

	if (new) {
		BUG_ON(!clockevent_state_detached(new));
		clockevents_shutdown(new);
	}
}

/**
 * clockevents_suspend - suspend clock devices
 */
void clockevents_suspend(void)
{
	struct clock_event_device *dev;

	list_for_each_entry_reverse(dev, &clockevent_devices, list)
		if (dev->suspend && !clockevent_state_detached(dev))
			dev->suspend(dev);
}

/**
 * clockevents_resume - resume clock devices
 */
void clockevents_resume(void)
{
	struct clock_event_device *dev;

	list_for_each_entry(dev, &clockevent_devices, list)
		if (dev->resume && !clockevent_state_detached(dev))
			dev->resume(dev);
}

#ifdef CONFIG_HOTPLUG_CPU

/**
 * tick_offline_cpu - Shutdown all clock events related
 *                    to this CPU and take it out of the
 *                    broadcast mechanism.
 * @cpu:	The outgoing CPU
 *
 * Called by the dying CPU during teardown.
 */
void tick_offline_cpu(unsigned int cpu)
{
	struct clock_event_device *dev, *tmp;

	raw_spin_lock(&clockevents_lock);

	tick_broadcast_offline(cpu);
	tick_shutdown();

	/*
	 * Unregister the clock event devices which were
	 * released above.
	 */
	list_for_each_entry_safe(dev, tmp, &clockevents_released, list)
		list_del(&dev->list);

	/*
	 * Now check whether the CPU has left unused per cpu devices
	 */
	list_for_each_entry_safe(dev, tmp, &clockevent_devices, list) {
		if (cpumask_test_cpu(cpu, dev->cpumask) &&
		    cpumask_weight(dev->cpumask) == 1 &&
		    !tick_is_broadcast_device(dev)) {
			BUG_ON(!clockevent_state_detached(dev));
			list_del(&dev->list);
		}
	}

	raw_spin_unlock(&clockevents_lock);
}
#endif
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("Clocksource watchdog unit test");
MODULE_AUTHOR("Paul E. McKenney <paulmck@kernel.org>");

static int holdoff = IS_BUILTIN(CONFIG_TEST_CLOCKSOURCE_WATCHDOG) ? 10 : 0;
module_param(holdoff, int, 0444);
MODULE_PARM_DESC(holdoff, "Time to wait to start test (s).");

/* Watchdog kthread's task_struct pointer for debug purposes. */
static struct task_struct *wdtest_task;

static u64 wdtest_jiffies_read(struct clocksource *cs)
{
	return (u64)jiffies;
}

static struct clocksource clocksource_wdtest_jiffies = {
	.name			= "wdtest-jiffies",
	.rating			= 1, /* lowest valid rating*/
	.uncertainty_margin	= TICK_NSEC,
	.read			= wdtest_jiffies_read,
	.mask			= CLOCKSOURCE_MASK(32),
	.flags			= CLOCK_SOURCE_MUST_VERIFY,
	.mult			= TICK_NSEC << JIFFIES_SHIFT, /* details above */
	.shift			= JIFFIES_SHIFT,
	.max_cycles		= 10,
};

static int wdtest_ktime_read_ndelays;
static bool wdtest_ktime_read_fuzz;

static u64 wdtest_ktime_read(struct clocksource *cs)
{
	int wkrn = READ_ONCE(wdtest_ktime_read_ndelays);
	static int sign = 1;
	u64 ret;

	if (wkrn) {
		udelay(cs->uncertainty_margin / 250);
		WRITE_ONCE(wdtest_ktime_read_ndelays, wkrn - 1);
	}
	ret = ktime_get_real_fast_ns();
	if (READ_ONCE(wdtest_ktime_read_fuzz)) {
		sign = -sign;
		ret = ret + sign * 100 * NSEC_PER_MSEC;
	}
	return ret;
}

static void wdtest_ktime_cs_mark_unstable(struct clocksource *cs)
{
	pr_info("--- Marking %s unstable due to clocksource watchdog.\n", cs->name);
}

#define KTIME_FLAGS (CLOCK_SOURCE_IS_CONTINUOUS | \
		     CLOCK_SOURCE_VALID_FOR_HRES | \
		     CLOCK_SOURCE_MUST_VERIFY | \
		     CLOCK_SOURCE_VERIFY_PERCPU)

static struct clocksource clocksource_wdtest_ktime = {
	.name			= "wdtest-ktime",
	.rating			= 300,
	.read			= wdtest_ktime_read,
	.mask			= CLOCKSOURCE_MASK(64),
	.flags			= KTIME_FLAGS,
	.mark_unstable		= wdtest_ktime_cs_mark_unstable,
	.list			= LIST_HEAD_INIT(clocksource_wdtest_ktime.list),
};

/* Reset the clocksource if needed. */
static void wdtest_ktime_clocksource_reset(void)
{
	if (clocksource_wdtest_ktime.flags & CLOCK_SOURCE_UNSTABLE) {
		clocksource_unregister(&clocksource_wdtest_ktime);
		clocksource_wdtest_ktime.flags = KTIME_FLAGS;
		schedule_timeout_uninterruptible(HZ / 10);
		clocksource_register_khz(&clocksource_wdtest_ktime, 1000 * 1000);
	}
}

/* Run the specified series of watchdog tests. */
static int wdtest_func(void *arg)
{
	unsigned long j1, j2;
	int i, max_retries;
	char *s;

	schedule_timeout_uninterruptible(holdoff * HZ);

	/*
	 * Verify that jiffies-like clocksources get the manually
	 * specified uncertainty margin.
	 */
	pr_info("--- Verify jiffies-like uncertainty margin.\n");
	__clocksource_register(&clocksource_wdtest_jiffies);
	WARN_ON_ONCE(clocksource_wdtest_jiffies.uncertainty_margin != TICK_NSEC);

	j1 = clocksource_wdtest_jiffies.read(&clocksource_wdtest_jiffies);
	schedule_timeout_uninterruptible(HZ);
	j2 = clocksource_wdtest_jiffies.read(&clocksource_wdtest_jiffies);
	WARN_ON_ONCE(j1 == j2);

	clocksource_unregister(&clocksource_wdtest_jiffies);

	/*
	 * Verify that tsc-like clocksources are assigned a reasonable
	 * uncertainty margin.
	 */
	pr_info("--- Verify tsc-like uncertainty margin.\n");
	clocksource_register_khz(&clocksource_wdtest_ktime, 1000 * 1000);
	WARN_ON_ONCE(clocksource_wdtest_ktime.uncertainty_margin < NSEC_PER_USEC);

	j1 = clocksource_wdtest_ktime.read(&clocksource_wdtest_ktime);
	udelay(1);
	j2 = clocksource_wdtest_ktime.read(&clocksource_wdtest_ktime);
	pr_info("--- tsc-like times: %lu - %lu = %lu.\n", j2, j1, j2 - j1);
	WARN_ONCE(time_before(j2, j1 + NSEC_PER_USEC),
		  "Expected at least 1000ns, got %lu.\n", j2 - j1);

	/* Verify tsc-like stability with various numbers of errors injected. */
	max_retries = clocksource_get_max_watchdog_retry();
	for (i = 0; i <= max_retries + 1; i++) {
		if (i <= 1 && i < max_retries)
			s = "";
		else if (i <= max_retries)
			s = ", expect message";
		else
			s = ", expect clock skew";
		pr_info("--- Watchdog with %dx error injection, %d retries%s.\n", i, max_retries, s);
		WRITE_ONCE(wdtest_ktime_read_ndelays, i);
		schedule_timeout_uninterruptible(2 * HZ);
		WARN_ON_ONCE(READ_ONCE(wdtest_ktime_read_ndelays));
		WARN_ON_ONCE((i <= max_retries) !=
			     !(clocksource_wdtest_ktime.flags & CLOCK_SOURCE_UNSTABLE));
		wdtest_ktime_clocksource_reset();
	}

	/* Verify tsc-like stability with clock-value-fuzz error injection. */
	pr_info("--- Watchdog clock-value-fuzz error injection, expect clock skew and per-CPU mismatches.\n");
	WRITE_ONCE(wdtest_ktime_read_fuzz, true);
	schedule_timeout_uninterruptible(2 * HZ);
	WARN_ON_ONCE(!(clocksource_wdtest_ktime.flags & CLOCK_SOURCE_UNSTABLE));
	clocksource_verify_percpu(&clocksource_wdtest_ktime);
	WRITE_ONCE(wdtest_ktime_read_fuzz, false);

	clocksource_unregister(&clocksource_wdtest_ktime);

	pr_info("--- Done with test.\n");
	return 0;
}

static void wdtest_print_module_parms(void)
{
	pr_alert("--- holdoff=%d\n", holdoff);
}

/* Cleanup function. */
static void clocksource_wdtest_cleanup(void)
{
}

static int __init clocksource_wdtest_init(void)
{
	int ret = 0;

	wdtest_print_module_parms();

	/* Create watchdog-test task. */
	wdtest_task = kthread_run(wdtest_func, NULL, "wdtest");
	if (IS_ERR(wdtest_task)) {
		ret = PTR_ERR(wdtest_task);
		pr_warn("%s: Failed to create wdtest kthread.\n", __func__);
		wdtest_task = NULL;
		return ret;
	}

	return 0;
}

module_init(clocksource_wdtest_init);
module_exit(clocksource_wdtest_cleanup);

static void clocksource_enqueue(struct clocksource *cs);

static noinline u64 cycles_to_nsec_safe(struct clocksource *cs, u64 start, u64 end)
{
	u64 delta = clocksource_delta(end, start, cs->mask, cs->max_raw_delta);

	if (likely(delta < cs->max_cycles))
		return clocksource_cyc2ns(delta, cs->mult, cs->shift);

	return mul_u64_u32_shr(delta, cs->mult, cs->shift);
}

/**
 * clocks_calc_mult_shift - calculate mult/shift factors for scaled math of clocks
 * @mult:	pointer to mult variable
 * @shift:	pointer to shift variable
 * @from:	frequency to convert from
 * @to:		frequency to convert to
 * @maxsec:	guaranteed runtime conversion range in seconds
 *
 * The function evaluates the shift/mult pair for the scaled math
 * operations of clocksources and clockevents.
 *
 * @to and @from are frequency values in HZ. For clock sources @to is
 * NSEC_PER_SEC == 1GHz and @from is the counter frequency. For clock
 * event @to is the counter frequency and @from is NSEC_PER_SEC.
 *
 * The @maxsec conversion range argument controls the time frame in
 * seconds which must be covered by the runtime conversion with the
 * calculated mult and shift factors. This guarantees that no 64bit
 * overflow happens when the input value of the conversion is
 * multiplied with the calculated mult factor. Larger ranges may
 * reduce the conversion accuracy by choosing smaller mult and shift
 * factors.
 */
void
clocks_calc_mult_shift(u32 *mult, u32 *shift, u32 from, u32 to, u32 maxsec)
{
	u64 tmp;
	u32 sft, sftacc= 32;

	/*
	 * Calculate the shift factor which is limiting the conversion
	 * range:
	 */
	tmp = ((u64)maxsec * from) >> 32;
	while (tmp) {
		tmp >>=1;
		sftacc--;
	}

	/*
	 * Find the conversion shift/mult pair which has the best
	 * accuracy and fits the maxsec conversion range:
	 */
	for (sft = 32; sft > 0; sft--) {
		tmp = (u64) to << sft;
		tmp += from / 2;
		do_div(tmp, from);
		if ((tmp >> sftacc) == 0)
			break;
	}
	*mult = tmp;
	*shift = sft;
}
EXPORT_SYMBOL_GPL(clocks_calc_mult_shift);

/*[Clocksource internal variables]---------
 * curr_clocksource:
 *	currently selected clocksource.
 * suspend_clocksource:
 *	used to calculate the suspend time.
 * clocksource_list:
 *	linked list with the registered clocksources
 * clocksource_mutex:
 *	protects manipulations to curr_clocksource and the clocksource_list
 * override_name:
 *	Name of the user-specified clocksource.
 */
static struct clocksource *curr_clocksource;
static struct clocksource *suspend_clocksource;
static LIST_HEAD(clocksource_list);
static DEFINE_MUTEX(clocksource_mutex);
static char override_name[CS_NAME_LEN];
static int finished_booting;
static u64 suspend_start;

/*
 * Interval: 0.5sec.
 */
#define WATCHDOG_INTERVAL (HZ >> 1)
#define WATCHDOG_INTERVAL_MAX_NS ((2 * WATCHDOG_INTERVAL) * (NSEC_PER_SEC / HZ))

/*
 * Threshold: 0.0312s, when doubled: 0.0625s.
 */
#define WATCHDOG_THRESHOLD (NSEC_PER_SEC >> 5)

/*
 * Maximum permissible delay between two readouts of the watchdog
 * clocksource surrounding a read of the clocksource being validated.
 * This delay could be due to SMIs, NMIs, or to VCPU preemptions.  Used as
 * a lower bound for cs->uncertainty_margin values when registering clocks.
 *
 * The default of 500 parts per million is based on NTP's limits.
 * If a clocksource is good enough for NTP, it is good enough for us!
 *
 * In other words, by default, even if a clocksource is extremely
 * precise (for example, with a sub-nanosecond period), the maximum
 * permissible skew between the clocksource watchdog and the clocksource
 * under test is not permitted to go below the 500ppm minimum defined
 * by MAX_SKEW_USEC.  This 500ppm minimum may be overridden using the
 * CLOCKSOURCE_WATCHDOG_MAX_SKEW_US Kconfig option.
 */
#ifdef CONFIG_CLOCKSOURCE_WATCHDOG_MAX_SKEW_US
#define MAX_SKEW_USEC	CONFIG_CLOCKSOURCE_WATCHDOG_MAX_SKEW_US
#else
#define MAX_SKEW_USEC	(125 * WATCHDOG_INTERVAL / HZ)
#endif

/*
 * Default for maximum permissible skew when cs->uncertainty_margin is
 * not specified, and the lower bound even when cs->uncertainty_margin
 * is specified.  This is also the default that is used when registering
 * clocks with unspecified cs->uncertainty_margin, so this macro is used
 * even in CONFIG_CLOCKSOURCE_WATCHDOG=n kernels.
 */
#define WATCHDOG_MAX_SKEW (MAX_SKEW_USEC * NSEC_PER_USEC)

#ifdef CONFIG_CLOCKSOURCE_WATCHDOG
static void clocksource_watchdog_work(struct work_struct *work);
static void clocksource_select(void);

static LIST_HEAD(watchdog_list);
static struct clocksource *watchdog;
static struct timer_list watchdog_timer;
static DECLARE_WORK(watchdog_work, clocksource_watchdog_work);
static DEFINE_SPINLOCK(watchdog_lock);
static int watchdog_running;
static atomic_t watchdog_reset_pending;
static int64_t watchdog_max_interval;

static inline void clocksource_watchdog_lock(unsigned long *flags)
{
	spin_lock_irqsave(&watchdog_lock, *flags);
}

static inline void clocksource_watchdog_unlock(unsigned long *flags)
{
	spin_unlock_irqrestore(&watchdog_lock, *flags);
}

static int clocksource_watchdog_kthread(void *data);

static void clocksource_watchdog_work(struct work_struct *work)
{
	/*
	 * We cannot directly run clocksource_watchdog_kthread() here, because
	 * clocksource_select() calls timekeeping_notify() which uses
	 * stop_machine(). One cannot use stop_machine() from a workqueue() due
	 * lock inversions wrt CPU hotplug.
	 *
	 * Also, we only ever run this work once or twice during the lifetime
	 * of the kernel, so there is no point in creating a more permanent
	 * kthread for this.
	 *
	 * If kthread_run fails the next watchdog scan over the
	 * watchdog_list will find the unstable clock again.
	 */
	kthread_run(clocksource_watchdog_kthread, NULL, "kwatchdog");
}

static void clocksource_change_rating(struct clocksource *cs, int rating)
{
	list_del(&cs->list);
	cs->rating = rating;
	clocksource_enqueue(cs);
}

static void __clocksource_unstable(struct clocksource *cs)
{
	cs->flags &= ~(CLOCK_SOURCE_VALID_FOR_HRES | CLOCK_SOURCE_WATCHDOG);
	cs->flags |= CLOCK_SOURCE_UNSTABLE;

	/*
	 * If the clocksource is registered clocksource_watchdog_kthread() will
	 * re-rate and re-select.
	 */
	if (list_empty(&cs->list)) {
		cs->rating = 0;
		return;
	}

	if (cs->mark_unstable)
		cs->mark_unstable(cs);

	/* kick clocksource_watchdog_kthread() */
	if (finished_booting)
		schedule_work(&watchdog_work);
}

/**
 * clocksource_mark_unstable - mark clocksource unstable via watchdog
 * @cs:		clocksource to be marked unstable
 *
 * This function is called by the x86 TSC code to mark clocksources as unstable;
 * it defers demotion and re-selection to a kthread.
 */
void clocksource_mark_unstable(struct clocksource *cs)
{
	unsigned long flags;

	spin_lock_irqsave(&watchdog_lock, flags);
	if (!(cs->flags & CLOCK_SOURCE_UNSTABLE)) {
		if (!list_empty(&cs->list) && list_empty(&cs->wd_list))
			list_add(&cs->wd_list, &watchdog_list);
		__clocksource_unstable(cs);
	}
	spin_unlock_irqrestore(&watchdog_lock, flags);
}

static int verify_n_cpus = 8;
module_param(verify_n_cpus, int, 0644);

enum wd_read_status {
	WD_READ_SUCCESS,
	WD_READ_UNSTABLE,
	WD_READ_SKIP
};

static enum wd_read_status cs_watchdog_read(struct clocksource *cs, u64 *csnow, u64 *wdnow)
{
	int64_t md = watchdog->uncertainty_margin;
	unsigned int nretries, max_retries;
	int64_t wd_delay, wd_seq_delay;
	u64 wd_end, wd_end2;

	max_retries = clocksource_get_max_watchdog_retry();
	for (nretries = 0; nretries <= max_retries; nretries++) {
		local_irq_disable();
		*wdnow = watchdog->read(watchdog);
		*csnow = cs->read(cs);
		wd_end = watchdog->read(watchdog);
		wd_end2 = watchdog->read(watchdog);
		local_irq_enable();

		wd_delay = cycles_to_nsec_safe(watchdog, *wdnow, wd_end);
		if (wd_delay <= md + cs->uncertainty_margin) {
			if (nretries > 1 && nretries >= max_retries) {
				pr_warn("timekeeping watchdog on CPU%d: %s retried %d times before success\n",
					smp_processor_id(), watchdog->name, nretries);
			}
			return WD_READ_SUCCESS;
		}

		/*
		 * Now compute delay in consecutive watchdog read to see if
		 * there is too much external interferences that cause
		 * significant delay in reading both clocksource and watchdog.
		 *
		 * If consecutive WD read-back delay > md, report
		 * system busy, reinit the watchdog and skip the current
		 * watchdog test.
		 */
		wd_seq_delay = cycles_to_nsec_safe(watchdog, wd_end, wd_end2);
		if (wd_seq_delay > md)
			goto skip_test;
	}

	pr_warn("timekeeping watchdog on CPU%d: wd-%s-wd excessive read-back delay of %lldns vs. limit of %ldns, wd-wd read-back delay only %lldns, attempt %d, marking %s unstable\n",
		smp_processor_id(), cs->name, wd_delay, WATCHDOG_MAX_SKEW, wd_seq_delay, nretries, cs->name);
	return WD_READ_UNSTABLE;

skip_test:
	pr_info("timekeeping watchdog on CPU%d: %s wd-wd read-back delay of %lldns\n",
		smp_processor_id(), watchdog->name, wd_seq_delay);
	pr_info("wd-%s-wd read-back delay of %lldns, clock-skew test skipped!\n",
		cs->name, wd_delay);
	return WD_READ_SKIP;
}

static u64 csnow_mid;
static cpumask_t cpus_ahead;
static cpumask_t cpus_behind;
static cpumask_t cpus_chosen;

static void clocksource_verify_choose_cpus(void)
{
	int cpu, i, n = verify_n_cpus;

	if (n < 0 || n >= num_online_cpus()) {
		/* Check all of the CPUs. */
		cpumask_copy(&cpus_chosen, cpu_online_mask);
		cpumask_clear_cpu(smp_processor_id(), &cpus_chosen);
		return;
	}

	/* If no checking desired, or no other CPU to check, leave. */
	cpumask_clear(&cpus_chosen);
	if (n == 0 || num_online_cpus() <= 1)
		return;

	/* Make sure to select at least one CPU other than the current CPU. */
	cpu = cpumask_any_but(cpu_online_mask, smp_processor_id());
	if (WARN_ON_ONCE(cpu >= nr_cpu_ids))
		return;
	cpumask_set_cpu(cpu, &cpus_chosen);

	/* Force a sane value for the boot parameter. */
	if (n > nr_cpu_ids)
		n = nr_cpu_ids;

	/*
	 * Randomly select the specified number of CPUs.  If the same
	 * CPU is selected multiple times, that CPU is checked only once,
	 * and no replacement CPU is selected.  This gracefully handles
	 * situations where verify_n_cpus is greater than the number of
	 * CPUs that are currently online.
	 */
	for (i = 1; i < n; i++) {
		cpu = cpumask_random(cpu_online_mask);
		if (!WARN_ON_ONCE(cpu >= nr_cpu_ids))
			cpumask_set_cpu(cpu, &cpus_chosen);
	}

	/* Don't verify ourselves. */
	cpumask_clear_cpu(smp_processor_id(), &cpus_chosen);
}

static void clocksource_verify_one_cpu(void *csin)
{
	struct clocksource *cs = (struct clocksource *)csin;

	csnow_mid = cs->read(cs);
}

void clocksource_verify_percpu(struct clocksource *cs)
{
	int64_t cs_nsec, cs_nsec_max = 0, cs_nsec_min = LLONG_MAX;
	u64 csnow_begin, csnow_end;
	int cpu, testcpu;
	s64 delta;

	if (verify_n_cpus == 0)
		return;
	cpumask_clear(&cpus_ahead);
	cpumask_clear(&cpus_behind);
	cpus_read_lock();
	migrate_disable();
	clocksource_verify_choose_cpus();
	if (cpumask_empty(&cpus_chosen)) {
		migrate_enable();
		cpus_read_unlock();
		pr_warn("Not enough CPUs to check clocksource '%s'.\n", cs->name);
		return;
	}
	testcpu = smp_processor_id();
	pr_info("Checking clocksource %s synchronization from CPU %d to CPUs %*pbl.\n",
		cs->name, testcpu, cpumask_pr_args(&cpus_chosen));
	preempt_disable();
	for_each_cpu(cpu, &cpus_chosen) {
		if (cpu == testcpu)
			continue;
		csnow_begin = cs->read(cs);
		smp_call_function_single(cpu, clocksource_verify_one_cpu, cs, 1);
		csnow_end = cs->read(cs);
		delta = (s64)((csnow_mid - csnow_begin) & cs->mask);
		if (delta < 0)
			cpumask_set_cpu(cpu, &cpus_behind);
		delta = (csnow_end - csnow_mid) & cs->mask;
		if (delta < 0)
			cpumask_set_cpu(cpu, &cpus_ahead);
		cs_nsec = cycles_to_nsec_safe(cs, csnow_begin, csnow_end);
		if (cs_nsec > cs_nsec_max)
			cs_nsec_max = cs_nsec;
		if (cs_nsec < cs_nsec_min)
			cs_nsec_min = cs_nsec;
	}
	preempt_enable();
	migrate_enable();
	cpus_read_unlock();
	if (!cpumask_empty(&cpus_ahead))
		pr_warn("        CPUs %*pbl ahead of CPU %d for clocksource %s.\n",
			cpumask_pr_args(&cpus_ahead), testcpu, cs->name);
	if (!cpumask_empty(&cpus_behind))
		pr_warn("        CPUs %*pbl behind CPU %d for clocksource %s.\n",
			cpumask_pr_args(&cpus_behind), testcpu, cs->name);
	pr_info("        CPU %d check durations %lldns - %lldns for clocksource %s.\n",
		testcpu, cs_nsec_min, cs_nsec_max, cs->name);
}
EXPORT_SYMBOL_GPL(clocksource_verify_percpu);

static inline void clocksource_reset_watchdog(void)
{
	struct clocksource *cs;

	list_for_each_entry(cs, &watchdog_list, wd_list)
		cs->flags &= ~CLOCK_SOURCE_WATCHDOG;
}


static void clocksource_watchdog(struct timer_list *unused)
{
	int64_t wd_nsec, cs_nsec, interval;
	u64 csnow, wdnow, cslast, wdlast;
	int next_cpu, reset_pending;
	struct clocksource *cs;
	enum wd_read_status read_ret;
	unsigned long extra_wait = 0;
	u32 md;

	spin_lock(&watchdog_lock);
	if (!watchdog_running)
		goto out;

	reset_pending = atomic_read(&watchdog_reset_pending);

	list_for_each_entry(cs, &watchdog_list, wd_list) {

		/* Clocksource already marked unstable? */
		if (cs->flags & CLOCK_SOURCE_UNSTABLE) {
			if (finished_booting)
				schedule_work(&watchdog_work);
			continue;
		}

		read_ret = cs_watchdog_read(cs, &csnow, &wdnow);

		if (read_ret == WD_READ_UNSTABLE) {
			/* Clock readout unreliable, so give it up. */
			__clocksource_unstable(cs);
			continue;
		}

		/*
		 * When WD_READ_SKIP is returned, it means the system is likely
		 * under very heavy load, where the latency of reading
		 * watchdog/clocksource is very big, and affect the accuracy of
		 * watchdog check. So give system some space and suspend the
		 * watchdog check for 5 minutes.
		 */
		if (read_ret == WD_READ_SKIP) {
			/*
			 * As the watchdog timer will be suspended, and
			 * cs->last could keep unchanged for 5 minutes, reset
			 * the counters.
			 */
			clocksource_reset_watchdog();
			extra_wait = HZ * 300;
			break;
		}

		/* Clocksource initialized ? */
		if (!(cs->flags & CLOCK_SOURCE_WATCHDOG) ||
		    atomic_read(&watchdog_reset_pending)) {
			cs->flags |= CLOCK_SOURCE_WATCHDOG;
			cs->wd_last = wdnow;
			cs->cs_last = csnow;
			continue;
		}

		wd_nsec = cycles_to_nsec_safe(watchdog, cs->wd_last, wdnow);
		cs_nsec = cycles_to_nsec_safe(cs, cs->cs_last, csnow);
		wdlast = cs->wd_last; /* save these in case we print them */
		cslast = cs->cs_last;
		cs->cs_last = csnow;
		cs->wd_last = wdnow;

		if (atomic_read(&watchdog_reset_pending))
			continue;

		/*
		 * The processing of timer softirqs can get delayed (usually
		 * on account of ksoftirqd not getting to run in a timely
		 * manner), which causes the watchdog interval to stretch.
		 * Skew detection may fail for longer watchdog intervals
		 * on account of fixed margins being used.
		 * Some clocksources, e.g. acpi_pm, cannot tolerate
		 * watchdog intervals longer than a few seconds.
		 */
		interval = max(cs_nsec, wd_nsec);
		if (unlikely(interval > WATCHDOG_INTERVAL_MAX_NS)) {
			if (system_state > SYSTEM_SCHEDULING &&
			    interval > 2 * watchdog_max_interval) {
				watchdog_max_interval = interval;
				pr_warn("Long readout interval, skipping watchdog check: cs_nsec: %lld wd_nsec: %lld\n",
					cs_nsec, wd_nsec);
			}
			watchdog_timer.expires = jiffies;
			continue;
		}

		/* Check the deviation from the watchdog clocksource. */
		md = cs->uncertainty_margin + watchdog->uncertainty_margin;
		if (abs(cs_nsec - wd_nsec) > md) {
			s64 cs_wd_msec;
			s64 wd_msec;
			u32 wd_rem;

			pr_warn("timekeeping watchdog on CPU%d: Marking clocksource '%s' as unstable because the skew is too large:\n",
				smp_processor_id(), cs->name);
			pr_warn("                      '%s' wd_nsec: %lld wd_now: %llx wd_last: %llx mask: %llx\n",
				watchdog->name, wd_nsec, wdnow, wdlast, watchdog->mask);
			pr_warn("                      '%s' cs_nsec: %lld cs_now: %llx cs_last: %llx mask: %llx\n",
				cs->name, cs_nsec, csnow, cslast, cs->mask);
			cs_wd_msec = div_s64_rem(cs_nsec - wd_nsec, 1000 * 1000, &wd_rem);
			wd_msec = div_s64_rem(wd_nsec, 1000 * 1000, &wd_rem);
			pr_warn("                      Clocksource '%s' skewed %lld ns (%lld ms) over watchdog '%s' interval of %lld ns (%lld ms)\n",
				cs->name, cs_nsec - wd_nsec, cs_wd_msec, watchdog->name, wd_nsec, wd_msec);
			if (curr_clocksource == cs)
				pr_warn("                      '%s' is current clocksource.\n", cs->name);
			else if (curr_clocksource)
				pr_warn("                      '%s' (not '%s') is current clocksource.\n", curr_clocksource->name, cs->name);
			else
				pr_warn("                      No current clocksource.\n");
			__clocksource_unstable(cs);
			continue;
		}

		if (cs == curr_clocksource && cs->tick_stable)
			cs->tick_stable(cs);

		if (!(cs->flags & CLOCK_SOURCE_VALID_FOR_HRES) &&
		    (cs->flags & CLOCK_SOURCE_IS_CONTINUOUS) &&
		    (watchdog->flags & CLOCK_SOURCE_IS_CONTINUOUS)) {
			/* Mark it valid for high-res. */
			cs->flags |= CLOCK_SOURCE_VALID_FOR_HRES;

			/*
			 * clocksource_done_booting() will sort it if
			 * finished_booting is not set yet.
			 */
			if (!finished_booting)
				continue;

			/*
			 * If this is not the current clocksource let
			 * the watchdog thread reselect it. Due to the
			 * change to high res this clocksource might
			 * be preferred now. If it is the current
			 * clocksource let the tick code know about
			 * that change.
			 */
			if (cs != curr_clocksource) {
				cs->flags |= CLOCK_SOURCE_RESELECT;
				schedule_work(&watchdog_work);
			} else {
				tick_clock_notify();
			}
		}
	}

	/*
	 * We only clear the watchdog_reset_pending, when we did a
	 * full cycle through all clocksources.
	 */
	if (reset_pending)
		atomic_dec(&watchdog_reset_pending);

	/*
	 * Cycle through CPUs to check if the CPUs stay synchronized
	 * to each other.
	 */
	next_cpu = cpumask_next_wrap(raw_smp_processor_id(), cpu_online_mask);

	/*
	 * Arm timer if not already pending: could race with concurrent
	 * pair clocksource_stop_watchdog() clocksource_start_watchdog().
	 */
	if (!timer_pending(&watchdog_timer)) {
		watchdog_timer.expires += WATCHDOG_INTERVAL + extra_wait;
		add_timer_on(&watchdog_timer, next_cpu);
	}
out:
	spin_unlock(&watchdog_lock);
}

static inline void clocksource_start_watchdog(void)
{
	if (watchdog_running || !watchdog || list_empty(&watchdog_list))
		return;
	timer_setup(&watchdog_timer, clocksource_watchdog, 0);
	watchdog_timer.expires = jiffies + WATCHDOG_INTERVAL;
	add_timer_on(&watchdog_timer, cpumask_first(cpu_online_mask));
	watchdog_running = 1;
}

static inline void clocksource_stop_watchdog(void)
{
	if (!watchdog_running || (watchdog && !list_empty(&watchdog_list)))
		return;
	timer_delete(&watchdog_timer);
	watchdog_running = 0;
}

static void clocksource_resume_watchdog(void)
{
	atomic_inc(&watchdog_reset_pending);
}

static void clocksource_enqueue_watchdog(struct clocksource *cs)
{
	INIT_LIST_HEAD(&cs->wd_list);

	if (cs->flags & CLOCK_SOURCE_MUST_VERIFY) {
		/* cs is a clocksource to be watched. */
		list_add(&cs->wd_list, &watchdog_list);
		cs->flags &= ~CLOCK_SOURCE_WATCHDOG;
	} else {
		/* cs is a watchdog. */
		if (cs->flags & CLOCK_SOURCE_IS_CONTINUOUS)
			cs->flags |= CLOCK_SOURCE_VALID_FOR_HRES;
	}
}

static void clocksource_select_watchdog(bool fallback)
{
	struct clocksource *cs, *old_wd;
	unsigned long flags;

	spin_lock_irqsave(&watchdog_lock, flags);
	/* save current watchdog */
	old_wd = watchdog;
	if (fallback)
		watchdog = NULL;

	list_for_each_entry(cs, &clocksource_list, list) {
		/* cs is a clocksource to be watched. */
		if (cs->flags & CLOCK_SOURCE_MUST_VERIFY)
			continue;

		/* Skip current if we were requested for a fallback. */
		if (fallback && cs == old_wd)
			continue;

		/* Pick the best watchdog. */
		if (!watchdog || cs->rating > watchdog->rating)
			watchdog = cs;
	}
	/* If we failed to find a fallback restore the old one. */
	if (!watchdog)
		watchdog = old_wd;

	/* If we changed the watchdog we need to reset cycles. */
	if (watchdog != old_wd)
		clocksource_reset_watchdog();

	/* Check if the watchdog timer needs to be started. */
	clocksource_start_watchdog();
	spin_unlock_irqrestore(&watchdog_lock, flags);
}

static void clocksource_dequeue_watchdog(struct clocksource *cs)
{
	if (cs != watchdog) {
		if (cs->flags & CLOCK_SOURCE_MUST_VERIFY) {
			/* cs is a watched clocksource. */
			list_del_init(&cs->wd_list);
			/* Check if the watchdog timer needs to be stopped. */
			clocksource_stop_watchdog();
		}
	}
}

static int __clocksource_watchdog_kthread(void)
{
	struct clocksource *cs, *tmp;
	unsigned long flags;
	int select = 0;

	/* Do any required per-CPU skew verification. */
	if (curr_clocksource &&
	    curr_clocksource->flags & CLOCK_SOURCE_UNSTABLE &&
	    curr_clocksource->flags & CLOCK_SOURCE_VERIFY_PERCPU)
		clocksource_verify_percpu(curr_clocksource);

	spin_lock_irqsave(&watchdog_lock, flags);
	list_for_each_entry_safe(cs, tmp, &watchdog_list, wd_list) {
		if (cs->flags & CLOCK_SOURCE_UNSTABLE) {
			list_del_init(&cs->wd_list);
			clocksource_change_rating(cs, 0);
			select = 1;
		}
		if (cs->flags & CLOCK_SOURCE_RESELECT) {
			cs->flags &= ~CLOCK_SOURCE_RESELECT;
			select = 1;
		}
	}
	/* Check if the watchdog timer needs to be stopped. */
	clocksource_stop_watchdog();
	spin_unlock_irqrestore(&watchdog_lock, flags);

	return select;
}

static int clocksource_watchdog_kthread(void *data)
{
	mutex_lock(&clocksource_mutex);
	if (__clocksource_watchdog_kthread())
		clocksource_select();
	mutex_unlock(&clocksource_mutex);
	return 0;
}

static bool clocksource_is_watchdog(struct clocksource *cs)
{
	return cs == watchdog;
}

#else /* CONFIG_CLOCKSOURCE_WATCHDOG */

static void clocksource_enqueue_watchdog(struct clocksource *cs)
{
	if (cs->flags & CLOCK_SOURCE_IS_CONTINUOUS)
		cs->flags |= CLOCK_SOURCE_VALID_FOR_HRES;
}

static void clocksource_select_watchdog(bool fallback) { }
static inline void clocksource_dequeue_watchdog(struct clocksource *cs) { }
static inline void clocksource_resume_watchdog(void) { }
static inline int __clocksource_watchdog_kthread(void) { return 0; }
static bool clocksource_is_watchdog(struct clocksource *cs) { return false; }
void clocksource_mark_unstable(struct clocksource *cs) { }

static inline void clocksource_watchdog_lock(unsigned long *flags) { }
static inline void clocksource_watchdog_unlock(unsigned long *flags) { }

#endif /* CONFIG_CLOCKSOURCE_WATCHDOG */

static bool clocksource_is_suspend(struct clocksource *cs)
{
	return cs == suspend_clocksource;
}

static void __clocksource_suspend_select(struct clocksource *cs)
{
	/*
	 * Skip the clocksource which will be stopped in suspend state.
	 */
	if (!(cs->flags & CLOCK_SOURCE_SUSPEND_NONSTOP))
		return;

	/*
	 * The nonstop clocksource can be selected as the suspend clocksource to
	 * calculate the suspend time, so it should not supply suspend/resume
	 * interfaces to suspend the nonstop clocksource when system suspends.
	 */
	if (cs->suspend || cs->resume) {
		pr_warn("Nonstop clocksource %s should not supply suspend/resume interfaces\n",
			cs->name);
	}

	/* Pick the best rating. */
	if (!suspend_clocksource || cs->rating > suspend_clocksource->rating)
		suspend_clocksource = cs;
}

/**
 * clocksource_suspend_select - Select the best clocksource for suspend timing
 * @fallback:	if select a fallback clocksource
 */
static void clocksource_suspend_select(bool fallback)
{
	struct clocksource *cs, *old_suspend;

	old_suspend = suspend_clocksource;
	if (fallback)
		suspend_clocksource = NULL;

	list_for_each_entry(cs, &clocksource_list, list) {
		/* Skip current if we were requested for a fallback. */
		if (fallback && cs == old_suspend)
			continue;

		__clocksource_suspend_select(cs);
	}
}

/**
 * clocksource_start_suspend_timing - Start measuring the suspend timing
 * @cs:			current clocksource from timekeeping
 * @start_cycles:	current cycles from timekeeping
 *
 * This function will save the start cycle values of suspend timer to calculate
 * the suspend time when resuming system.
 *
 * This function is called late in the suspend process from timekeeping_suspend(),
 * that means processes are frozen, non-boot cpus and interrupts are disabled
 * now. It is therefore possible to start the suspend timer without taking the
 * clocksource mutex.
 */
void clocksource_start_suspend_timing(struct clocksource *cs, u64 start_cycles)
{
	if (!suspend_clocksource)
		return;

	/*
	 * If current clocksource is the suspend timer, we should use the
	 * tkr_mono.cycle_last value as suspend_start to avoid same reading
	 * from suspend timer.
	 */
	if (clocksource_is_suspend(cs)) {
		suspend_start = start_cycles;
		return;
	}

	if (suspend_clocksource->enable &&
	    suspend_clocksource->enable(suspend_clocksource)) {
		pr_warn_once("Failed to enable the non-suspend-able clocksource.\n");
		return;
	}

	suspend_start = suspend_clocksource->read(suspend_clocksource);
}

/**
 * clocksource_stop_suspend_timing - Stop measuring the suspend timing
 * @cs:		current clocksource from timekeeping
 * @cycle_now:	current cycles from timekeeping
 *
 * This function will calculate the suspend time from suspend timer.
 *
 * Returns nanoseconds since suspend started, 0 if no usable suspend clocksource.
 *
 * This function is called early in the resume process from timekeeping_resume(),
 * that means there is only one cpu, no processes are running and the interrupts
 * are disabled. It is therefore possible to stop the suspend timer without
 * taking the clocksource mutex.
 */
u64 clocksource_stop_suspend_timing(struct clocksource *cs, u64 cycle_now)
{
	u64 now, nsec = 0;

	if (!suspend_clocksource)
		return 0;

	/*
	 * If current clocksource is the suspend timer, we should use the
	 * tkr_mono.cycle_last value from timekeeping as current cycle to
	 * avoid same reading from suspend timer.
	 */
	if (clocksource_is_suspend(cs))
		now = cycle_now;
	else
		now = suspend_clocksource->read(suspend_clocksource);

	if (now > suspend_start)
		nsec = cycles_to_nsec_safe(suspend_clocksource, suspend_start, now);

	/*
	 * Disable the suspend timer to save power if current clocksource is
	 * not the suspend timer.
	 */
	if (!clocksource_is_suspend(cs) && suspend_clocksource->disable)
		suspend_clocksource->disable(suspend_clocksource);

	return nsec;
}

/**
 * clocksource_suspend - suspend the clocksource(s)
 */
void clocksource_suspend(void)
{
	struct clocksource *cs;

	list_for_each_entry_reverse(cs, &clocksource_list, list)
		if (cs->suspend)
			cs->suspend(cs);
}

/**
 * clocksource_resume - resume the clocksource(s)
 */
void clocksource_resume(void)
{
	struct clocksource *cs;

	list_for_each_entry(cs, &clocksource_list, list)
		if (cs->resume)
			cs->resume(cs);

	clocksource_resume_watchdog();
}

/**
 * clocksource_touch_watchdog - Update watchdog
 *
 * Update the watchdog after exception contexts such as kgdb so as not
 * to incorrectly trip the watchdog. This might fail when the kernel
 * was stopped in code which holds watchdog_lock.
 */
void clocksource_touch_watchdog(void)
{
	clocksource_resume_watchdog();
}

/**
 * clocksource_max_adjustment- Returns max adjustment amount
 * @cs:         Pointer to clocksource
 *
 */
static u32 clocksource_max_adjustment(struct clocksource *cs)
{
	u64 ret;
	/*
	 * We won't try to correct for more than 11% adjustments (110,000 ppm),
	 */
	ret = (u64)cs->mult * 11;
	do_div(ret,100);
	return (u32)ret;
}

/**
 * clocks_calc_max_nsecs - Returns maximum nanoseconds that can be converted
 * @mult:	cycle to nanosecond multiplier
 * @shift:	cycle to nanosecond divisor (power of two)
 * @maxadj:	maximum adjustment value to mult (~11%)
 * @mask:	bitmask for two's complement subtraction of non 64 bit counters
 * @max_cyc:	maximum cycle value before potential overflow (does not include
 *		any safety margin)
 *
 * NOTE: This function includes a safety margin of 50%, in other words, we
 * return half the number of nanoseconds the hardware counter can technically
 * cover. This is done so that we can potentially detect problems caused by
 * delayed timers or bad hardware, which might result in time intervals that
 * are larger than what the math used can handle without overflows.
 */
u64 clocks_calc_max_nsecs(u32 mult, u32 shift, u32 maxadj, u64 mask, u64 *max_cyc)
{
	u64 max_nsecs, max_cycles;

	/*
	 * Calculate the maximum number of cycles that we can pass to the
	 * cyc2ns() function without overflowing a 64-bit result.
	 */
	max_cycles = ULLONG_MAX;
	do_div(max_cycles, mult+maxadj);

	/*
	 * The actual maximum number of cycles we can defer the clocksource is
	 * determined by the minimum of max_cycles and mask.
	 * Note: Here we subtract the maxadj to make sure we don't sleep for
	 * too long if there's a large negative adjustment.
	 */
	max_cycles = min(max_cycles, mask);
	max_nsecs = clocksource_cyc2ns(max_cycles, mult - maxadj, shift);

	/* return the max_cycles value as well if requested */
	if (max_cyc)
		*max_cyc = max_cycles;

	/* Return 50% of the actual maximum, so we can detect bad values */
	max_nsecs >>= 1;

	return max_nsecs;
}

/**
 * clocksource_update_max_deferment - Updates the clocksource max_idle_ns & max_cycles
 * @cs:         Pointer to clocksource to be updated
 *
 */
static inline void clocksource_update_max_deferment(struct clocksource *cs)
{
	cs->max_idle_ns = clocks_calc_max_nsecs(cs->mult, cs->shift,
						cs->maxadj, cs->mask,
						&cs->max_cycles);

	/*
	 * Threshold for detecting negative motion in clocksource_delta().
	 *
	 * Allow for 0.875 of the counter width so that overly long idle
	 * sleeps, which go slightly over mask/2, do not trigger the
	 * negative motion detection.
	 */
	cs->max_raw_delta = (cs->mask >> 1) + (cs->mask >> 2) + (cs->mask >> 3);
}

static struct clocksource *clocksource_find_best(bool oneshot, bool skipcur)
{
	struct clocksource *cs;

	if (!finished_booting || list_empty(&clocksource_list))
		return NULL;

	/*
	 * We pick the clocksource with the highest rating. If oneshot
	 * mode is active, we pick the highres valid clocksource with
	 * the best rating.
	 */
	list_for_each_entry(cs, &clocksource_list, list) {
		if (skipcur && cs == curr_clocksource)
			continue;
		if (oneshot && !(cs->flags & CLOCK_SOURCE_VALID_FOR_HRES))
			continue;
		return cs;
	}
	return NULL;
}

static void __clocksource_select(bool skipcur)
{
	bool oneshot = tick_oneshot_mode_active();
	struct clocksource *best, *cs;

	/* Find the best suitable clocksource */
	best = clocksource_find_best(oneshot, skipcur);
	if (!best)
		return;

	if (!strlen(override_name))
		goto found;

	/* Check for the override clocksource. */
	list_for_each_entry(cs, &clocksource_list, list) {
		if (skipcur && cs == curr_clocksource)
			continue;
		if (strcmp(cs->name, override_name) != 0)
			continue;
		/*
		 * Check to make sure we don't switch to a non-highres
		 * capable clocksource if the tick code is in oneshot
		 * mode (highres or nohz)
		 */
		if (!(cs->flags & CLOCK_SOURCE_VALID_FOR_HRES) && oneshot) {
			/* Override clocksource cannot be used. */
			if (cs->flags & CLOCK_SOURCE_UNSTABLE) {
				pr_warn("Override clocksource %s is unstable and not HRT compatible - cannot switch while in HRT/NOHZ mode\n",
					cs->name);
				override_name[0] = 0;
			} else {
				/*
				 * The override cannot be currently verified.
				 * Deferring to let the watchdog check.
				 */
				pr_info("Override clocksource %s is not currently HRT compatible - deferring\n",
					cs->name);
			}
		} else
			/* Override clocksource can be used. */
			best = cs;
		break;
	}

found:
	if (curr_clocksource != best && !timekeeping_notify(best)) {
		pr_info("Switched to clocksource %s\n", best->name);
		curr_clocksource = best;
	}
}

/**
 * clocksource_select - Select the best clocksource available
 *
 * Private function. Must hold clocksource_mutex when called.
 *
 * Select the clocksource with the best rating, or the clocksource,
 * which is selected by userspace override.
 */
static void clocksource_select(void)
{
	__clocksource_select(false);
}

static void clocksource_select_fallback(void)
{
	__clocksource_select(true);
}

/*
 * clocksource_done_booting - Called near the end of core bootup
 *
 * Hack to avoid lots of clocksource churn at boot time.
 * We use fs_initcall because we want this to start before
 * device_initcall but after subsys_initcall.
 */
static int __init clocksource_done_booting(void)
{
	mutex_lock(&clocksource_mutex);
	curr_clocksource = clocksource_default_clock();
	finished_booting = 1;
	/*
	 * Run the watchdog first to eliminate unstable clock sources
	 */
	__clocksource_watchdog_kthread();
	clocksource_select();
	mutex_unlock(&clocksource_mutex);
	return 0;
}
fs_initcall(clocksource_done_booting);

/*
 * Enqueue the clocksource sorted by rating
 */
static void clocksource_enqueue(struct clocksource *cs)
{
	struct list_head *entry = &clocksource_list;
	struct clocksource *tmp;

	list_for_each_entry(tmp, &clocksource_list, list) {
		/* Keep track of the place, where to insert */
		if (tmp->rating < cs->rating)
			break;
		entry = &tmp->list;
	}
	list_add(&cs->list, entry);
}

/**
 * __clocksource_update_freq_scale - Used update clocksource with new freq
 * @cs:		clocksource to be registered
 * @scale:	Scale factor multiplied against freq to get clocksource hz
 * @freq:	clocksource frequency (cycles per second) divided by scale
 *
 * This should only be called from the clocksource->enable() method.
 *
 * This *SHOULD NOT* be called directly! Please use the
 * __clocksource_update_freq_hz() or __clocksource_update_freq_khz() helper
 * functions.
 */
void __clocksource_update_freq_scale(struct clocksource *cs, u32 scale, u32 freq)
{
	u64 sec;

	/*
	 * Default clocksources are *special* and self-define their mult/shift.
	 * But, you're not special, so you should specify a freq value.
	 */
	if (freq) {
		/*
		 * Calc the maximum number of seconds which we can run before
		 * wrapping around. For clocksources which have a mask > 32-bit
		 * we need to limit the max sleep time to have a good
		 * conversion precision. 10 minutes is still a reasonable
		 * amount. That results in a shift value of 24 for a
		 * clocksource with mask >= 40-bit and f >= 4GHz. That maps to
		 * ~ 0.06ppm granularity for NTP.
		 */
		sec = cs->mask;
		do_div(sec, freq);
		do_div(sec, scale);
		if (!sec)
			sec = 1;
		else if (sec > 600 && cs->mask > UINT_MAX)
			sec = 600;

		clocks_calc_mult_shift(&cs->mult, &cs->shift, freq,
				       NSEC_PER_SEC / scale, sec * scale);
	}

	/*
	 * If the uncertainty margin is not specified, calculate it.  If
	 * both scale and freq are non-zero, calculate the clock period, but
	 * bound below at 2*WATCHDOG_MAX_SKEW, that is, 500ppm by default.
	 * However, if either of scale or freq is zero, be very conservative
	 * and take the tens-of-milliseconds WATCHDOG_THRESHOLD value
	 * for the uncertainty margin.  Allow stupidly small uncertainty
	 * margins to be specified by the caller for testing purposes,
	 * but warn to discourage production use of this capability.
	 *
	 * Bottom line:  The sum of the uncertainty margins of the
	 * watchdog clocksource and the clocksource under test will be at
	 * least 500ppm by default.  For more information, please see the
	 * comment preceding CONFIG_CLOCKSOURCE_WATCHDOG_MAX_SKEW_US above.
	 */
	if (scale && freq && !cs->uncertainty_margin) {
		cs->uncertainty_margin = NSEC_PER_SEC / (scale * freq);
		if (cs->uncertainty_margin < 2 * WATCHDOG_MAX_SKEW)
			cs->uncertainty_margin = 2 * WATCHDOG_MAX_SKEW;
	} else if (!cs->uncertainty_margin) {
		cs->uncertainty_margin = WATCHDOG_THRESHOLD;
	}
	WARN_ON_ONCE(cs->uncertainty_margin < 2 * WATCHDOG_MAX_SKEW);

	/*
	 * Ensure clocksources that have large 'mult' values don't overflow
	 * when adjusted.
	 */
	cs->maxadj = clocksource_max_adjustment(cs);
	while (freq && ((cs->mult + cs->maxadj < cs->mult)
		|| (cs->mult - cs->maxadj > cs->mult))) {
		cs->mult >>= 1;
		cs->shift--;
		cs->maxadj = clocksource_max_adjustment(cs);
	}

	/*
	 * Only warn for *special* clocksources that self-define
	 * their mult/shift values and don't specify a freq.
	 */
	WARN_ONCE(cs->mult + cs->maxadj < cs->mult,
		"timekeeping: Clocksource %s might overflow on 11%% adjustment\n",
		cs->name);

	clocksource_update_max_deferment(cs);

	pr_info("%s: mask: 0x%llx max_cycles: 0x%llx, max_idle_ns: %lld ns\n",
		cs->name, cs->mask, cs->max_cycles, cs->max_idle_ns);
}
EXPORT_SYMBOL_GPL(__clocksource_update_freq_scale);

/**
 * __clocksource_register_scale - Used to install new clocksources
 * @cs:		clocksource to be registered
 * @scale:	Scale factor multiplied against freq to get clocksource hz
 * @freq:	clocksource frequency (cycles per second) divided by scale
 *
 * Returns -EBUSY if registration fails, zero otherwise.
 *
 * This *SHOULD NOT* be called directly! Please use the
 * clocksource_register_hz() or clocksource_register_khz helper functions.
 */
int __clocksource_register_scale(struct clocksource *cs, u32 scale, u32 freq)
{
	unsigned long flags;

	clocksource_arch_init(cs);

	if (WARN_ON_ONCE((unsigned int)cs->id >= CSID_MAX))
		cs->id = CSID_GENERIC;
	if (cs->vdso_clock_mode < 0 ||
	    cs->vdso_clock_mode >= VDSO_CLOCKMODE_MAX) {
		pr_warn("clocksource %s registered with invalid VDSO mode %d. Disabling VDSO support.\n",
			cs->name, cs->vdso_clock_mode);
		cs->vdso_clock_mode = VDSO_CLOCKMODE_NONE;
	}

	/* Initialize mult/shift and max_idle_ns */
	__clocksource_update_freq_scale(cs, scale, freq);

	/* Add clocksource to the clocksource list */
	mutex_lock(&clocksource_mutex);

	clocksource_watchdog_lock(&flags);
	clocksource_enqueue(cs);
	clocksource_enqueue_watchdog(cs);
	clocksource_watchdog_unlock(&flags);

	clocksource_select();
	clocksource_select_watchdog(false);
	__clocksource_suspend_select(cs);
	mutex_unlock(&clocksource_mutex);
	return 0;
}
EXPORT_SYMBOL_GPL(__clocksource_register_scale);

/*
 * Unbind clocksource @cs. Called with clocksource_mutex held
 */
static int clocksource_unbind(struct clocksource *cs)
{
	unsigned long flags;

	if (clocksource_is_watchdog(cs)) {
		/* Select and try to install a replacement watchdog. */
		clocksource_select_watchdog(true);
		if (clocksource_is_watchdog(cs))
			return -EBUSY;
	}

	if (cs == curr_clocksource) {
		/* Select and try to install a replacement clock source */
		clocksource_select_fallback();
		if (curr_clocksource == cs)
			return -EBUSY;
	}

	if (clocksource_is_suspend(cs)) {
		/*
		 * Select and try to install a replacement suspend clocksource.
		 * If no replacement suspend clocksource, we will just let the
		 * clocksource go and have no suspend clocksource.
		 */
		clocksource_suspend_select(true);
	}

	clocksource_watchdog_lock(&flags);
	clocksource_dequeue_watchdog(cs);
	list_del_init(&cs->list);
	clocksource_watchdog_unlock(&flags);

	return 0;
}

/**
 * clocksource_unregister - remove a registered clocksource
 * @cs:	clocksource to be unregistered
 */
int clocksource_unregister(struct clocksource *cs)
{
	int ret = 0;

	mutex_lock(&clocksource_mutex);
	if (!list_empty(&cs->list))
		ret = clocksource_unbind(cs);
	mutex_unlock(&clocksource_mutex);
	return ret;
}
EXPORT_SYMBOL(clocksource_unregister);

#ifdef CONFIG_SYSFS
/**
 * current_clocksource_show - sysfs interface for current clocksource
 * @dev:	unused
 * @attr:	unused
 * @buf:	char buffer to be filled with clocksource list
 *
 * Provides sysfs interface for listing current clocksource.
 */
static ssize_t current_clocksource_show(struct device *dev,
					struct device_attribute *attr,
					char *buf)
{
	ssize_t count = 0;

	mutex_lock(&clocksource_mutex);
	count = sysfs_emit(buf, "%s\n", curr_clocksource->name);
	mutex_unlock(&clocksource_mutex);

	return count;
}

ssize_t sysfs_get_uname(const char *buf, char *dst, size_t cnt)
{
	size_t ret = cnt;

	/* strings from sysfs write are not 0 terminated! */
	if (!cnt || cnt >= CS_NAME_LEN)
		return -EINVAL;

	/* strip of \n: */
	if (buf[cnt-1] == '\n')
		cnt--;
	if (cnt > 0)
		memcpy(dst, buf, cnt);
	dst[cnt] = 0;
	return ret;
}

/**
 * current_clocksource_store - interface for manually overriding clocksource
 * @dev:	unused
 * @attr:	unused
 * @buf:	name of override clocksource
 * @count:	length of buffer
 *
 * Takes input from sysfs interface for manually overriding the default
 * clocksource selection.
 */
static ssize_t current_clocksource_store(struct device *dev,
					 struct device_attribute *attr,
					 const char *buf, size_t count)
{
	ssize_t ret;

	mutex_lock(&clocksource_mutex);

	ret = sysfs_get_uname(buf, override_name, count);
	if (ret >= 0)
		clocksource_select();

	mutex_unlock(&clocksource_mutex);

	return ret;
}
static DEVICE_ATTR_RW(current_clocksource);

/**
 * unbind_clocksource_store - interface for manually unbinding clocksource
 * @dev:	unused
 * @attr:	unused
 * @buf:	unused
 * @count:	length of buffer
 *
 * Takes input from sysfs interface for manually unbinding a clocksource.
 */
static ssize_t unbind_clocksource_store(struct device *dev,
					struct device_attribute *attr,
					const char *buf, size_t count)
{
	struct clocksource *cs;
	char name[CS_NAME_LEN];
	ssize_t ret;

	ret = sysfs_get_uname(buf, name, count);
	if (ret < 0)
		return ret;

	ret = -ENODEV;
	mutex_lock(&clocksource_mutex);
	list_for_each_entry(cs, &clocksource_list, list) {
		if (strcmp(cs->name, name))
			continue;
		ret = clocksource_unbind(cs);
		break;
	}
	mutex_unlock(&clocksource_mutex);

	return ret ? ret : count;
}
static DEVICE_ATTR_WO(unbind_clocksource);

/**
 * available_clocksource_show - sysfs interface for listing clocksource
 * @dev:	unused
 * @attr:	unused
 * @buf:	char buffer to be filled with clocksource list
 *
 * Provides sysfs interface for listing registered clocksources
 */
static ssize_t available_clocksource_show(struct device *dev,
					  struct device_attribute *attr,
					  char *buf)
{
	struct clocksource *src;
	ssize_t count = 0;

	mutex_lock(&clocksource_mutex);
	list_for_each_entry(src, &clocksource_list, list) {
		/*
		 * Don't show non-HRES clocksource if the tick code is
		 * in one shot mode (highres=on or nohz=on)
		 */
		if (!tick_oneshot_mode_active() ||
		    (src->flags & CLOCK_SOURCE_VALID_FOR_HRES))
			count += snprintf(buf + count,
				  max((ssize_t)PAGE_SIZE - count, (ssize_t)0),
				  "%s ", src->name);
	}
	mutex_unlock(&clocksource_mutex);

	count += snprintf(buf + count,
			  max((ssize_t)PAGE_SIZE - count, (ssize_t)0), "\n");

	return count;
}
static DEVICE_ATTR_RO(available_clocksource);

static struct attribute *clocksource_attrs[] = {
	&dev_attr_current_clocksource.attr,
	&dev_attr_unbind_clocksource.attr,
	&dev_attr_available_clocksource.attr,
	NULL
};
ATTRIBUTE_GROUPS(clocksource);

static const struct bus_type clocksource_subsys = {
	.name = "clocksource",
	.dev_name = "clocksource",
};

static struct device device_clocksource = {
	.id	= 0,
	.bus	= &clocksource_subsys,
	.groups	= clocksource_groups,
};

static int __init init_clocksource_sysfs(void)
{
	int error = subsys_system_register(&clocksource_subsys, NULL);

	if (!error)
		error = device_register(&device_clocksource);

	return error;
}

device_initcall(init_clocksource_sysfs);
#endif /* CONFIG_SYSFS */

/**
 * boot_override_clocksource - boot clock override
 * @str:	override name
 *
 * Takes a clocksource= boot argument and uses it
 * as the clocksource override name.
 */
static int __init boot_override_clocksource(char* str)
{
	mutex_lock(&clocksource_mutex);
	if (str)
		strscpy(override_name, str);
	mutex_unlock(&clocksource_mutex);
	return 1;
}

__setup("clocksource=", boot_override_clocksource);

/**
 * boot_override_clock - Compatibility layer for deprecated boot option
 * @str:	override name
 *
 * DEPRECATED! Takes a clock= boot argument and uses it
 * as the clocksource override name
 */
static int __init boot_override_clock(char* str)
{
	if (!strcmp(str, "pmtmr")) {
		pr_warn("clock=pmtmr is deprecated - use clocksource=acpi_pm\n");
		return boot_override_clocksource("acpi_pm");
	}
	pr_warn("clock= boot option is deprecated - use clocksource=xyz\n");
	return boot_override_clocksource(str);
}

__setup("clock=", boot_override_clock);
