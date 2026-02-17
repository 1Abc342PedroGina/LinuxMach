/* SPDX License Indentifier:GPL-2.0 */
/*
 * Mach Operating System
 * Copyright (c) 1991,1990,1989,1988,1987 Carnegie Mellon University
 * All Rights Reserved.
 *
 * Permission to use, copy, modify and distribute this software and its
 * documentation is hereby granted, provided that both the copyright
 * notice and this permission notice appear in all copies of the
 * software, derivative works or modified versions, and any portions
 * thereof, and that both notices appear in supporting documentation.
 *
 * CARNEGIE MELLON ALLOWS FREE USE OF THIS SOFTWARE IN ITS "AS IS"
 * CONDITION.  CARNEGIE MELLON DISCLAIMS ANY LIABILITY OF ANY KIND FOR
 * ANY DAMAGES WHATSOEVER RESULTING FROM THE USE OF THIS SOFTWARE.
 *
 * Carnegie Mellon requests users of this software to return to
 *
 *  Software Distribution Coordinator  or  Software.Distribution@CS.CMU.EDU
 *  School of Computer Science
 *  Carnegie Mellon University
 *  Pittsburgh PA 15213-3890
 *
 * any improvements or extensions that they make and grant Carnegie Mellon
 * the rights to redistribute these changes.
 */
#include <linux/irq-entry-common.h>
#include <linux/resume_user_mode.h>
#include <linux/highmem.h>
#include <linux/jump_label.h>
#include <linux/kmsan.h>
#include <linux/livepatch.h>
#include <linux/tick.h>
#include <kern/ast.h>
#include <kern/counter.h>
#include <kern/misc_protos.h>
#include <kern/queue.h>
#include <kern/sched_prim.h>
#include <kern/thread.h>
#include <kern/processor.h>
#include <kern/restartable.h>
#include <kern/spl.h>
#include <kern/sfi.h>
#if CONFIG_TELEMETRY
#include <kern/telemetry.h>
#endif
#include <kern/waitq.h>
#include <kern/ledger.h>
#include <kern/machine.h>
#include <kern/kpc.h>
#include <kperf/kperf.h>
#include <mach/policy.h>
#include <security/mac_mach_internal.h> // for MACF AST hook
#include <stdatomic.h>

#if CONFIG_ARCADE
#include <kern/arcade.h>
#endif

static inline __attribute__((always_inline)) void handle_user_asts_interrupts_enabled(ast_t reasons, thread_t thread, task_t task);
static inline __attribute__((always_inline)) void assert_thread_return_to_user(thread_t thread);

static void __attribute__((noinline, noreturn, disable_tail_calls))
thread_preempted(__unused void* parameter, __unused wait_result_t result)
{
	/*
	 * We've been scheduled again after a userspace preemption,
	 * try again to return to userspace.
	 */
	thread_exception_return();
}

/*
 * Create a dedicated frame to clarify that this thread has been preempted
 * while running in kernel space.
 */
static void __attribute__((noinline, disable_tail_calls))
thread_preempted_in_kernel(ast_t urgent_reason)
{
	thread_block_reason(THREAD_CONTINUE_NULL, NULL, urgent_reason);

	assert(ml_get_interrupts_enabled() == FALSE);
}

/*
 * AST_URGENT was detected while in kernel mode
 * Called with interrupts disabled, returns the same way
 * Must return to caller
 */
void
ast_taken_kernel(void)
{
	assert(ml_get_interrupts_enabled() == FALSE);

	thread_t thread = current_thread();

	/* Idle threads handle preemption themselves */
	if ((thread->state & TH_IDLE)) {
		ast_off(AST_PREEMPTION);
		return;
	}

	/*
	 * It's possible for this to be called after AST_URGENT
	 * has already been handled, due to races in enable_preemption
	 */
	if (ast_peek(AST_URGENT) != AST_URGENT) {
		return;
	}

	/*
	 * Don't preempt if the thread is already preparing to block.
	 * TODO: the thread can cheese this with clear_wait()
	 */
	if (waitq_wait_possible(thread) == FALSE) {
		/* Consume AST_URGENT or the interrupt will call us again */
		ast_consume(AST_URGENT);
		return;
	}

	/* TODO: Should we csw_check again to notice if conditions have changed? */

	ast_t urgent_reason = ast_consume(AST_PREEMPTION);

	assert(urgent_reason & AST_PREEMPT);

	/* We've decided to try context switching */
	thread_preempted_in_kernel(urgent_reason);
}

/*
 * An AST flag was set while returning to user mode
 * Called with interrupts disabled, returns with interrupts enabled
 * May call continuation instead of returning
 */
void
ast_taken_user(void)
{
	assert(ml_get_interrupts_enabled() == FALSE);

	thread_t thread = current_thread();
	task_t   task   = get_threadtask(thread);

	/* We are about to return to userspace, there must not be a pending wait */
	assert(waitq_wait_possible(thread));
	assert((thread->state & TH_IDLE) == 0);

	/* TODO: Add more 'return to userspace' assertions here */

	/*
	 * If this thread was urgently preempted in userspace,
	 * take the preemption before processing the ASTs.
	 * The trap handler will call us again if we have more ASTs, so it's
	 * safe to block in a continuation here.
	 */
	if (ast_peek(AST_URGENT) == AST_URGENT) {
		ast_t urgent_reason = ast_consume(AST_PREEMPTION);

		assert(urgent_reason & AST_PREEMPT);

		/* TODO: Should we csw_check again to notice if conditions have changed? */

		thread_block_reason(thread_preempted, NULL, urgent_reason);
		/* NOTREACHED */
	}

	/*
	 * AST_KEVENT does not send an IPI when setting the ast for a thread running in parallel
	 * on a different processor. Only the ast bit on the thread will be set.
	 *
	 * Force a propagate for concurrent updates without an IPI.
	 */
	ast_propagate(thread);

	/*
	 * Consume all non-preemption processor ASTs matching reasons
	 * because we're handling them here.
	 *
	 * If one of the AST handlers blocks in a continuation,
	 * we'll reinstate the unserviced thread-level AST flags
	 * from the thread to the processor on context switch.
	 * If one of the AST handlers sets another AST,
	 * the trap handler will call ast_taken_user again.
	 *
	 * We expect the AST handlers not to thread_exception_return
	 * without an ast_propagate or context switch to reinstate
	 * the per-processor ASTs.
	 *
	 * TODO: Why are AST_DTRACE and AST_KPERF not per-thread ASTs?
	 */
	ast_t reasons = ast_consume(AST_PER_THREAD | AST_KPERF | AST_DTRACE);

	ml_set_interrupts_enabled(TRUE);

	handle_user_asts_interrupts_enabled(reasons, thread, task);

	spl_t s = splsched();

#if CONFIG_SCHED_SFI
	/*
	 * SFI is currently a per-processor AST, not a per-thread AST
	 *      TODO: SFI should be a per-thread AST
	 */
	if (ast_consume(AST_SFI) == AST_SFI) {
		sfi_ast(thread);
	}
#endif

	/* We are about to return to userspace, there must not be a pending wait */
	assert(waitq_wait_possible(thread));

	/*
	 * We've handled all per-thread ASTs, time to handle non-urgent preemption.
	 *
	 * We delay reading the preemption bits until now in case the thread
	 * blocks while handling per-thread ASTs.
	 *
	 * If one of the AST handlers had managed to set a new AST bit,
	 * thread_exception_return will call ast_taken again.
	 */
	ast_t preemption_reasons = ast_consume(AST_PREEMPTION);

	if (preemption_reasons & AST_PREEMPT) {
		/* Conditions may have changed from when the AST_PREEMPT was originally set, so re-check. */

		thread_lock(thread);
		preemption_reasons = csw_check(thread, current_processor(), (preemption_reasons & AST_QUANTUM));
		thread_unlock(thread);

#if CONFIG_SCHED_SFI
		/* csw_check might tell us that SFI is needed */
		if (preemption_reasons & AST_SFI) {
			sfi_ast(thread);
		}
#endif

		if (preemption_reasons & AST_PREEMPT) {
			/* switching to a continuation implicitly re-enables interrupts */
			thread_block_reason(thread_preempted, NULL, preemption_reasons);
			/* NOTREACHED */
		}

		/*
		 * We previously had a pending AST_PREEMPT, but csw_check
		 * decided that it should no longer be set, and to keep
		 * executing the current thread instead.
		 * Clear the pending preemption timer as we no longer
		 * have a pending AST_PREEMPT to time out.
		 *
		 * TODO: just do the thread block if we see AST_PREEMPT
		 * to avoid taking the pset lock twice.
		 * To do that thread block needs to be smarter
		 * about not context switching when it's not necessary
		 * e.g. the first-timeslice check for queue has priority
		 */
		clear_pending_nonurgent_preemption(current_processor());
	}

	splx(s);

	/*
	 * Here's a good place to put assertions of things which must be true
	 * upon return to userspace.
	 */
	assert_thread_return_to_user(thread);
}

static inline void
handle_user_asts_interrupts_enabled(ast_t reasons, thread_t thread, task_t task)
{
#if CONFIG_DTRACE
	if (reasons & AST_DTRACE) {
		dtrace_ast();
	}
#endif

#ifdef MACH_BSD
	if (reasons & AST_BSD) {
		thread_ast_clear(thread, AST_BSD);
		bsd_ast(thread);
	}
#endif

#if CONFIG_MACF
	if (reasons & AST_MACF) {
		thread_ast_clear(thread, AST_MACF);
		mac_thread_userret(thread);
	}
#endif

#if CONFIG_ARCADE
	if (reasons & AST_ARCADE) {
		thread_ast_clear(thread, AST_ARCADE);
		arcade_ast(thread);
	}
#endif

	if (reasons & AST_APC) {
		thread_ast_clear(thread, AST_APC);
		thread_apc_ast(thread);
	}

#if HAS_MTE
	if (reasons & AST_SYNTHESIZE_MACH) {
		extern void mte_synthesize_async_tag_check_fault(thread_t thread, vm_map_t map);
		thread_ast_clear(thread, AST_SYNTHESIZE_MACH);
		mte_synthesize_async_tag_check_fault(thread, get_threadtask(thread)->map);
	}
#endif /* HAS_MTE */

	if (reasons & AST_MACH_EXCEPTION) {
		thread_ast_clear(thread, AST_MACH_EXCEPTION);
		mach_exception_ast(thread);
	}

	if (reasons & AST_LEDGER) {
		thread_ast_clear(thread, AST_LEDGER);
		ledger_ast(thread);
	}

	if (reasons & AST_KPERF) {
		thread_ast_clear(thread, AST_KPERF);
#if CONFIG_CPU_COUNTERS
		kpc_thread_ast_handler(thread);
#endif /* CONFIG_CPU_COUNTERS */
		kperf_thread_ast_handler(thread);
		thread->kperf_ast = 0;
	}

	if (reasons & AST_RESET_PCS) {
		thread_ast_clear(thread, AST_RESET_PCS);
		thread_reset_pcs_ast(task, thread);
	}

	if (reasons & AST_KEVENT) {
		thread_ast_clear(thread, AST_KEVENT);
		uint16_t bits = atomic_exchange(&thread->kevent_ast_bits, 0);
		if (bits) {
			kevent_ast(thread, bits);
		}
	}

	if (reasons & AST_PROC_RESOURCE) {
		thread_ast_clear(thread, AST_PROC_RESOURCE);
		task_port_space_ast(task);
#if MACH_BSD
		proc_filedesc_ast(task);
#endif /* MACH_BSD */
	}

#if CONFIG_TELEMETRY
	if (reasons & AST_TELEMETRY_ALL) {
		ast_t telemetry_reasons = reasons & AST_TELEMETRY_ALL;
		thread_ast_clear(thread, AST_TELEMETRY_ALL);
		telemetry_ast(thread, telemetry_reasons);
	}
#endif

#if MACH_ASSERT
	if (reasons & AST_DEBUG_ASSERT) {
		thread_ast_clear(thread, AST_DEBUG_ASSERT);
		thread_debug_return_to_user_ast(thread);
	}
#endif
}

static inline void
assert_thread_return_to_user(thread_t thread)
{
	assert(thread->kern_promotion_schedpri == 0);
	if (thread->rwlock_count > 0) {
		panic("rwlock_count is %d for thread %p, possibly it still holds a rwlock", thread->rwlock_count, thread);
	}
	assert(thread->priority_floor_count == 0);

	assert3u(0, ==, thread->sched_flags &
	    (TH_SFLAG_WAITQ_PROMOTED |
	    TH_SFLAG_RW_PROMOTED |
	    TH_SFLAG_EXEC_PROMOTED |
	    TH_SFLAG_FLOOR_PROMOTED |
	    TH_SFLAG_DEPRESS));

#if CONFIG_EXCLAVES
	assert3u(thread->options & TH_OPT_AOE, ==, 0);
#endif /* CONFIG_EXCLAVES */
}

#define ASYNC_THREAD_ASTS_HANDLED (AST_MACH_EXCEPTION | AST_DTRACE | AST_TELEMETRY_ALL | AST_KPERF | AST_DEBUG_ASSERT)

/*
 * Check if ASTs need to be handled for threads that do work on other threads (currently
 * aio threads).
 * Called and returns with interrupts enabled
 */
void
ast_check_async_thread(void)
{
	thread_t thread = current_thread();
	task_t   task   = get_threadtask(thread);

	assert(ml_get_interrupts_enabled() == TRUE);

	for (;;) {
		spl_t s = splsched();
		ast_t reasons = ast_consume(ASYNC_THREAD_ASTS_HANDLED);
		splx(s);

		if (!(reasons & ASYNC_THREAD_ASTS_HANDLED)) {
			break;
		}

		handle_user_asts_interrupts_enabled(reasons & ASYNC_THREAD_ASTS_HANDLED, thread,
		    task);

		assert_thread_return_to_user(thread);
	}
}

/*
 * Set AST flags on current processor
 * Called at splsched
 */
void
ast_on(ast_t reasons)
{
	ast_t *pending_ast = ast_pending();

	*pending_ast |= reasons;
}

/*
 * Clear AST flags on current processor
 * Called at splsched
 */
void
ast_off(ast_t reasons)
{
	ast_t *pending_ast = ast_pending();

	*pending_ast &= ~reasons;
}

/*
 * Consume the requested subset of the AST flags set on the processor
 * Return the bits that were set
 * Called at splsched
 */
ast_t
ast_consume(ast_t reasons)
{
	ast_t *pending_ast = ast_pending();

	reasons &= *pending_ast;
	*pending_ast &= ~reasons;

	return reasons;
}

/*
 * Read the requested subset of the AST flags set on the processor
 * Return the bits that were set, don't modify the processor
 * Called at splsched
 */
ast_t
ast_peek(ast_t reasons)
{
	ast_t *pending_ast = ast_pending();

	reasons &= *pending_ast;

	return reasons;
}

/*
 * Re-set current processor's per-thread AST flags to those set on thread
 * Called at splsched
 */
void
ast_context(thread_t thread)
{
	ast_t *pending_ast = ast_pending();

	*pending_ast = (*pending_ast & ~AST_PER_THREAD) | thread_ast_get(thread);
}

/*
 * Propagate ASTs set on a thread to the current processor
 * Called at splsched
 */
void
ast_propagate(thread_t thread)
{
	ast_on(thread_ast_get(thread));
}

void
ast_dtrace_on(void)
{
	ast_on(AST_DTRACE);
}
/* Workaround to allow gradual conversion of architecture code */
void __weak arch_do_signal_or_restart(struct pt_regs *regs) { }

#ifdef CONFIG_HAVE_GENERIC_TIF_BITS
#define EXIT_TO_USER_MODE_WORK_LOOP	(EXIT_TO_USER_MODE_WORK & ~_TIF_RSEQ)
#else
#define EXIT_TO_USER_MODE_WORK_LOOP	(EXIT_TO_USER_MODE_WORK)
#endif

/* TIF bits, which prevent a time slice extension. */
#ifdef CONFIG_PREEMPT_RT
/*
 * Since rseq slice ext has a direct correlation to the worst case
 * scheduling latency (schedule is delayed after all), only have it affect
 * LAZY reschedules on PREEMPT_RT for now.
 *
 * However, since this delay is only applicable to userspace, a value
 * for rseq_slice_extension_nsec that is strictly less than the worst case
 * kernel space preempt_disable() region, should mean the scheduling latency
 * is not affected, even for !LAZY.
 *
 * However, since this value depends on the hardware at hand, it cannot be
 * pre-determined in any sensible way. Hence punt on this problem for now.
 */
# define TIF_SLICE_EXT_SCHED	(_TIF_NEED_RESCHED_LAZY)
#else
# define TIF_SLICE_EXT_SCHED	(_TIF_NEED_RESCHED | _TIF_NEED_RESCHED_LAZY)
#endif
#define TIF_SLICE_EXT_DENY	(EXIT_TO_USER_MODE_WORK & ~TIF_SLICE_EXT_SCHED)

static __always_inline unsigned long __exit_to_user_mode_loop(struct pt_regs *regs,
							      unsigned long ti_work)
{
	/*
	 * Before returning to user space ensure that all pending work
	 * items have been completed.
	 */
	while (ti_work & EXIT_TO_USER_MODE_WORK_LOOP) {

		local_irq_enable_exit_to_user(ti_work);

		if (ti_work & (_TIF_NEED_RESCHED | _TIF_NEED_RESCHED_LAZY)) {
			if (!rseq_grant_slice_extension(ti_work & TIF_SLICE_EXT_DENY))
				schedule();
		}

		if (ti_work & _TIF_UPROBE)
			uprobe_notify_resume(regs);

		if (ti_work & _TIF_PATCH_PENDING)
			klp_update_patch_state(current);

		if (ti_work & (_TIF_SIGPENDING | _TIF_NOTIFY_SIGNAL))
			arch_do_signal_or_restart(regs);

		if (ti_work & _TIF_NOTIFY_RESUME)
			resume_user_mode_work(regs);

		/* Architecture specific TIF work */
		arch_exit_to_user_mode_work(regs, ti_work);

		/*
		 * Disable interrupts and reevaluate the work flags as they
		 * might have changed while interrupts and preemption was
		 * enabled above.
		 */
		local_irq_disable_exit_to_user();

		/* Check if any of the above work has queued a deferred wakeup */
		tick_nohz_user_enter_prepare();

		ti_work = read_thread_flags();
	}

	/* Return the latest work state for arch_exit_to_user_mode() */
	return ti_work;
}

/**
 * exit_to_user_mode_loop - do any pending work before leaving to user space
 * @regs:	Pointer to pt_regs on entry stack
 * @ti_work:	TIF work flags as read by the caller
 */
__always_inline unsigned long exit_to_user_mode_loop(struct pt_regs *regs,
						     unsigned long ti_work)
{
	for (;;) {
		ti_work = __exit_to_user_mode_loop(regs, ti_work);

		if (likely(!rseq_exit_to_user_mode_restart(regs, ti_work)))
			return ti_work;
		ti_work = read_thread_flags();
	}
}

noinstr irqentry_state_t irqentry_enter(struct pt_regs *regs)
{
	irqentry_state_t ret = {
		.exit_rcu = false,
	};

	if (user_mode(regs)) {
		irqentry_enter_from_user_mode(regs);
		return ret;
	}

	/*
	 * If this entry hit the idle task invoke ct_irq_enter() whether
	 * RCU is watching or not.
	 *
	 * Interrupts can nest when the first interrupt invokes softirq
	 * processing on return which enables interrupts.
	 *
	 * Scheduler ticks in the idle task can mark quiescent state and
	 * terminate a grace period, if and only if the timer interrupt is
	 * not nested into another interrupt.
	 *
	 * Checking for rcu_is_watching() here would prevent the nesting
	 * interrupt to invoke ct_irq_enter(). If that nested interrupt is
	 * the tick then rcu_flavor_sched_clock_irq() would wrongfully
	 * assume that it is the first interrupt and eventually claim
	 * quiescent state and end grace periods prematurely.
	 *
	 * Unconditionally invoke ct_irq_enter() so RCU state stays
	 * consistent.
	 *
	 * TINY_RCU does not support EQS, so let the compiler eliminate
	 * this part when enabled.
	 */
	if (!IS_ENABLED(CONFIG_TINY_RCU) &&
	    (is_idle_task(current) || arch_in_rcu_eqs())) {
		/*
		 * If RCU is not watching then the same careful
		 * sequence vs. lockdep and tracing is required
		 * as in irqentry_enter_from_user_mode().
		 */
		lockdep_hardirqs_off(CALLER_ADDR0);
		ct_irq_enter();
		instrumentation_begin();
		kmsan_unpoison_entry_regs(regs);
		trace_hardirqs_off_finish();
		instrumentation_end();

		ret.exit_rcu = true;
		return ret;
	}

	/*
	 * If RCU is watching then RCU only wants to check whether it needs
	 * to restart the tick in NOHZ mode. rcu_irq_enter_check_tick()
	 * already contains a warning when RCU is not watching, so no point
	 * in having another one here.
	 */
	lockdep_hardirqs_off(CALLER_ADDR0);
	instrumentation_begin();
	kmsan_unpoison_entry_regs(regs);
	rcu_irq_enter_check_tick();
	trace_hardirqs_off_finish();
	instrumentation_end();

	return ret;
}

/**
 * arch_irqentry_exit_need_resched - Architecture specific need resched function
 *
 * Invoked from raw_irqentry_exit_cond_resched() to check if resched is needed.
 * Defaults return true.
 *
 * The main purpose is to permit arch to avoid preemption of a task from an IRQ.
 */
static inline bool arch_irqentry_exit_need_resched(void);

#ifndef arch_irqentry_exit_need_resched
static inline bool arch_irqentry_exit_need_resched(void) { return true; }
#endif

void raw_irqentry_exit_cond_resched(void)
{
	if (!preempt_count()) {
		/* Sanity check RCU and thread stack */
		rcu_irq_exit_check_preempt();
		if (IS_ENABLED(CONFIG_DEBUG_ENTRY))
			WARN_ON_ONCE(!on_thread_stack());
		if (need_resched() && arch_irqentry_exit_need_resched())
			preempt_schedule_irq();
	}
}
#ifdef CONFIG_PREEMPT_DYNAMIC
#if defined(CONFIG_HAVE_PREEMPT_DYNAMIC_CALL)
DEFINE_STATIC_CALL(irqentry_exit_cond_resched, raw_irqentry_exit_cond_resched);
#elif defined(CONFIG_HAVE_PREEMPT_DYNAMIC_KEY)
DEFINE_STATIC_KEY_TRUE(sk_dynamic_irqentry_exit_cond_resched);
void dynamic_irqentry_exit_cond_resched(void)
{
	if (!static_branch_unlikely(&sk_dynamic_irqentry_exit_cond_resched))
		return;
	raw_irqentry_exit_cond_resched();
}
#endif
#endif

noinstr void irqentry_exit(struct pt_regs *regs, irqentry_state_t state)
{
	lockdep_assert_irqs_disabled();

	/* Check whether this returns to user mode */
	if (user_mode(regs)) {
		irqentry_exit_to_user_mode(regs);
	} else if (!regs_irqs_disabled(regs)) {
		/*
		 * If RCU was not watching on entry this needs to be done
		 * carefully and needs the same ordering of lockdep/tracing
		 * and RCU as the return to user mode path.
		 */
		if (state.exit_rcu) {
			instrumentation_begin();
			/* Tell the tracer that IRET will enable interrupts */
			trace_hardirqs_on_prepare();
			lockdep_hardirqs_on_prepare();
			instrumentation_end();
			ct_irq_exit();
			lockdep_hardirqs_on(CALLER_ADDR0);
			return;
		}

		instrumentation_begin();
		if (IS_ENABLED(CONFIG_PREEMPTION))
			irqentry_exit_cond_resched();

		/* Covers both tracing and lockdep */
		trace_hardirqs_on();
		instrumentation_end();
	} else {
		/*
		 * IRQ flags state is correct already. Just tell RCU if it
		 * was not watching on entry.
		 */
		if (state.exit_rcu)
			ct_irq_exit();
	}
}

irqentry_state_t noinstr irqentry_nmi_enter(struct pt_regs *regs)
{
	irqentry_state_t irq_state;

	irq_state.lockdep = lockdep_hardirqs_enabled();

	__nmi_enter();
	lockdep_hardirqs_off(CALLER_ADDR0);
	lockdep_hardirq_enter();
	ct_nmi_enter();

	instrumentation_begin();
	kmsan_unpoison_entry_regs(regs);
	trace_hardirqs_off_finish();
	ftrace_nmi_enter();
	instrumentation_end();

	return irq_state;
}

void noinstr irqentry_nmi_exit(struct pt_regs *regs, irqentry_state_t irq_state)
{
	instrumentation_begin();
	ftrace_nmi_exit();
	if (irq_state.lockdep) {
		trace_hardirqs_on_prepare();
		lockdep_hardirqs_on_prepare();
	}
	instrumentation_end();

	ct_nmi_exit();
	lockdep_hardirq_exit();
	if (irq_state.lockdep)
		lockdep_hardirqs_on(CALLER_ADDR0);
	__nmi_exit();
}
