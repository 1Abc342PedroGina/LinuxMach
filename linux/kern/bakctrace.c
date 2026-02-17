/* SDPX License Indentifier: GPL-2.0 */
#include <linux/sched/task_stack.h>
#include <linux/sched/debug.h>
#include <linux/sched.h>
#include <linux/kernel.h>
#include <linux/export.h>
#include <linux/kallsyms.h>
#include <linux/stacktrace.h>
#include <linux/interrupt.h>

#include <stddef.h>
#include <stdint.h>

#include <kern/assert.h>
#include <kern/backtrace.h>
#include <kern/cambria_layout.h>
#include <kern/thread.h>
#include <machine/machine_routines.h>
#include <sys/errno.h>
#include <vm/vm_map_xnu.h>

#if defined(__arm64__)
#include <arm/cpu_data.h>
#include <arm/cpu_data_internal.h>
#endif // defined(__arm64__)

#if defined(HAS_APPLE_PAC)
#include <ptrauth.h>
#endif // defined(HAS_APPLE_PAC)

#if HAS_MTE
#include <arm64/mte.h>
#endif // HAS_MTE

#if __x86_64__
static void
_backtrace_packed_out_of_reach(void)
{
	// This symbol is used to replace frames that have been "JIT-ed"
	// or dynamically inserted in the kernel by some kext in a regular
	// VM mapping that might be outside of the filesets.
	//
	// This is an Intel only issue.
}
#endif // __x86_64__

// Pack an address according to a particular packing format.
static size_t
_backtrace_pack_addr(backtrace_pack_t packing, uint8_t *dst, size_t dst_size,
    uintptr_t addr)
{
	switch (packing) {
	case BTP_NONE:
		if (dst_size >= sizeof(addr)) {
			memcpy(dst, &addr, sizeof(addr));
		}
		return sizeof(addr);
	case BTP_KERN_OFFSET_32:;
		uintptr_t addr_delta = addr - vm_kernel_stext;
		int32_t addr_packed = (int32_t)addr_delta;
#if __x86_64__
		if ((uintptr_t)(int32_t)addr_delta != addr_delta) {
			addr = (vm_offset_t)&_backtrace_packed_out_of_reach;
			addr_delta = addr - vm_kernel_stext;
			addr_packed = (int32_t)addr_delta;
		}
#else // __x86_64__
		assert((uintptr_t)(int32_t)addr_delta == addr_delta);
#endif // !__x86_64__
		if (dst_size >= sizeof(addr_packed)) {
			memcpy(dst, &addr_packed, sizeof(addr_packed));
		}
		return sizeof(addr_packed);
	default:
		panic("backtrace: unknown packing format %d", packing);
	}
}

// Since it's only called from threads that we're going to keep executing,
// if there's bad data the system is going to die eventually.  If this function
// is inlined, it doesn't record the frame of the function it's inside (because
// there's no stack frame), so prevent that.
static size_t __attribute__((noinline, not_tail_called))
backtrace_internal(backtrace_pack_t packing, uint8_t *bt,
    size_t btsize, void *start_frame, int64_t addr_offset,
    backtrace_info_t *info_out)
{
	thread_t thread = current_thread();
	uintptr_t *fp;
	size_t size_used = 0;
	uintptr_t top, bottom;
	bool in_valid_stack;
	assert(bt != NULL);
	assert(btsize > 0);

	fp = start_frame;
#if defined(HAS_APPLE_PAC)
	fp = ptrauth_strip(fp, ptrauth_key_frame_pointer);
#endif
	bottom = thread->kernel_stack;
	top = bottom + kernel_stack_size;

#define IN_STK_BOUNDS(__addr) \
	(((uintptr_t)(__addr) >= (uintptr_t)bottom) && \
	((uintptr_t)(__addr) < (uintptr_t)top))

	in_valid_stack = IN_STK_BOUNDS(fp) || ml_addr_in_non_xnu_stack((uintptr_t)fp);

	if (!in_valid_stack) {
		fp = NULL;
	}

	while (fp != NULL && size_used < btsize) {
		uintptr_t *next_fp = (uintptr_t *)*fp;
#if defined(HAS_APPLE_PAC)
		next_fp = ptrauth_strip(next_fp, ptrauth_key_frame_pointer);
#endif
		// Return address is one word higher than frame pointer.
		uintptr_t ret_addr = *(fp + 1);

		// If the frame pointer is 0, backtracing has reached the top of
		// the stack and there is no return address.  Some stacks might not
		// have set this up, so bounds check, as well.
		in_valid_stack = IN_STK_BOUNDS(next_fp) || ml_addr_in_non_xnu_stack((uintptr_t)next_fp);

		if (next_fp == NULL || !in_valid_stack) {
			break;
		}

#if defined(HAS_APPLE_PAC)
		// Return addresses are signed by arm64e ABI, so strip it.
		uintptr_t pc = (uintptr_t)ptrauth_strip((void *)ret_addr,
		    ptrauth_key_return_address);
#else // defined(HAS_APPLE_PAC)
		uintptr_t pc = ret_addr;
#endif // !defined(HAS_APPLE_PAC)
		if (pc == 0) {
			// Once a NULL PC is encountered, ignore the rest of the call stack.
			break;
		}
		pc += addr_offset;
		size_used += _backtrace_pack_addr(packing, bt + size_used,
		    btsize - size_used, pc);

		// Stacks grow down; backtracing should always be moving to higher
		// addresses except when a frame is stitching between two different
		// stacks.
		if (next_fp <= fp) {
			// This check is verbose; it is basically checking whether this
			// thread is switching between the kernel stack and a non-XNU stack
			// (or between one non-XNU stack and another, as there can be more
			// than one). If not, then stop the backtrace as stack switching
			// should be the only reason as to why the next FP would be lower
			// than the current FP.
			if (!ml_addr_in_non_xnu_stack((uintptr_t)fp) &&
			    !ml_addr_in_non_xnu_stack((uintptr_t)next_fp)) {
				break;
			}
		}
		fp = next_fp;
	}

	if (info_out) {
		backtrace_info_t info = BTI_NONE;
#if __LP64__
		info |= BTI_64_BIT;
#endif
		if (fp != NULL && size_used >= btsize) {
			info |= BTI_TRUNCATED;
		}
		*info_out = info;
	}

	return size_used;
#undef IN_STK_BOUNDS
}

static kern_return_t
interrupted_kernel_pc_fp(uintptr_t *pc, uintptr_t *fp)
{
#if defined(__x86_64__)
	x86_saved_state_t *state;
	bool state_64;
	uint64_t cs;

	state = current_cpu_datap()->cpu_int_state;
	if (!state) {
		return KERN_FAILURE;
	}

	state_64 = is_saved_state64(state);

	if (state_64) {
		cs = saved_state64(state)->isf.cs;
	} else {
		cs = saved_state32(state)->cs;
	}
	// Return early if interrupted a thread in user space.
	if ((cs & SEL_PL) == SEL_PL_U) {
		return KERN_FAILURE;
	}

	if (state_64) {
		*pc = saved_state64(state)->isf.rip;
		*fp = saved_state64(state)->rbp;
	} else {
		*pc = saved_state32(state)->eip;
		*fp = saved_state32(state)->ebp;
	}

#elif defined(__arm64__)

	struct arm_saved_state *state;

	state = getCpuDatap()->cpu_int_state;
	if (!state) {
		return KERN_FAILURE;
	}

	// Return early if interrupted a thread in user space.
	if (PSR64_IS_USER(get_saved_state_cpsr(state))) {
		return KERN_FAILURE;
	}

	*pc = ml_get_backtrace_pc(state);
	*fp = get_saved_state_fp(state);

#else // !defined(__arm64__) && !defined(__x86_64__)
#error "unsupported architecture"
#endif // !defined(__arm64__) && !defined(__x86_64__)

	return KERN_SUCCESS;
}

__attribute__((always_inline))
static uintptr_t
_backtrace_preamble(struct backtrace_control *ctl, uintptr_t *start_frame_out)
{
	backtrace_flags_t flags = ctl ? ctl->btc_flags : 0;
	uintptr_t start_frame = ctl ? ctl->btc_frame_addr : 0;
	uintptr_t pc = 0;
	if (flags & BTF_KERN_INTERRUPTED) {
		assert(ml_at_interrupt_context() == TRUE);

		uintptr_t fp;
		kern_return_t kr = interrupted_kernel_pc_fp(&pc, &fp);
		if (kr != KERN_SUCCESS) {
			return 0;
		}
		*start_frame_out = start_frame ?: fp;
	} else if (start_frame == 0) {
		*start_frame_out = (uintptr_t)__builtin_frame_address(0);
	} else {
		*start_frame_out = start_frame;
	}
	return pc;
}

unsigned int __attribute__((noinline))
backtrace(uintptr_t *bt, unsigned int max_frames,
    struct backtrace_control *ctl, backtrace_info_t *info_out)
{
	unsigned int len_adj = 0;
	uintptr_t start_frame = ctl ? ctl->btc_frame_addr : 0;
	uintptr_t pc = _backtrace_preamble(ctl, &start_frame);
	if (pc) {
		bt[0] = pc;
		if (max_frames == 1) {
			return 1;
		}
		bt += 1;
		max_frames -= 1;
		len_adj += 1;
	}

	size_t size = backtrace_internal(BTP_NONE, (uint8_t *)bt,
	    max_frames * sizeof(uintptr_t), (void *)start_frame,
	    ctl ? ctl->btc_addr_offset : 0, info_out);
	// NULL-terminate the list, if space is available.
	unsigned int len = size / sizeof(uintptr_t);
	if (len != max_frames) {
		bt[len] = 0;
	}

	return len + len_adj;
}

// Backtrace the current thread's kernel stack as a packed representation.
size_t
backtrace_packed(backtrace_pack_t packing, uint8_t *bt, size_t btsize,
    struct backtrace_control *ctl,
    backtrace_info_t *info_out)
{
	unsigned int size_adj = 0;
	uintptr_t start_frame = ctl ? ctl->btc_frame_addr : 0;
	uintptr_t pc = _backtrace_preamble(ctl, &start_frame);
	if (pc) {
		size_adj = _backtrace_pack_addr(packing, bt, btsize, pc);
		if (size_adj >= btsize) {
			return size_adj;
		}
		btsize -= size_adj;
	}

	size_t written_size = backtrace_internal(packing, (uint8_t *)bt, btsize,
	    (void *)start_frame, ctl ? ctl->btc_addr_offset : 0, info_out);
	return written_size + size_adj;
}

// Convert an array of addresses to a packed representation.
size_t
backtrace_pack(backtrace_pack_t packing, uint8_t *dst, size_t dst_size,
    const uintptr_t *src, unsigned int src_len)
{
	size_t dst_offset = 0;
	for (unsigned int i = 0; i < src_len; i++) {
		size_t pack_size = _backtrace_pack_addr(packing, dst + dst_offset,
		    dst_size - dst_offset, src[i]);
		if (dst_offset + pack_size >= dst_size) {
			return dst_offset;
		}
		dst_offset += pack_size;
	}
	return dst_offset;
}

// Convert a packed backtrace to an array of addresses.
unsigned int
backtrace_unpack(backtrace_pack_t packing, uintptr_t *dst, unsigned int dst_len,
    const uint8_t *src, size_t src_size)
{
	switch (packing) {
	case BTP_NONE:;
		size_t unpack_size = MIN(dst_len * sizeof(uintptr_t), src_size);
		memmove(dst, src, unpack_size);
		return (unsigned int)(unpack_size / sizeof(uintptr_t));
	case BTP_KERN_OFFSET_32:;
		unsigned int src_len = src_size / sizeof(int32_t);
		unsigned int unpack_len = MIN(src_len, dst_len);
		for (unsigned int i = 0; i < unpack_len; i++) {
			int32_t addr = 0;
			memcpy(&addr, src + i * sizeof(int32_t), sizeof(int32_t));
			dst[i] = vm_kernel_stext + (uintptr_t)addr;
		}
		return unpack_len;
	default:
		panic("backtrace: unknown packing format %d", packing);
	}
}

static errno_t
_backtrace_copyin(void * __unused ctx, void *dst, user_addr_t src, size_t size)
{
#if HAS_MTE
    mte_disable_tag_checking();
#endif // HAS_MTE
	int error = copyin((user_addr_t)src, dst, size);
#if HAS_MTE
	mte_enable_tag_checking();
#endif // HAS_MTE
	return error;
}

errno_t
backtrace_user_copy_error(void *ctx, void *dst, user_addr_t src, size_t size)
{
#pragma unused(ctx, dst, src, size)
	return EFAULT;
}

unsigned int
backtrace_user(uintptr_t *bt, unsigned int max_frames,
    const struct backtrace_control *ctl_in,
    struct backtrace_user_info *info_out)
{
	static const struct backtrace_control ctl_default = {
		.btc_user_copy = _backtrace_copyin,
	};
	const struct backtrace_control *ctl = ctl_in ?: &ctl_default;
	uintptr_t pc = 0, next_fp = 0;
	uintptr_t fp = ctl->btc_frame_addr;
	int64_t addr_offset = ctl ? ctl->btc_addr_offset : 0;
	vm_map_t map = NULL;
	vm_map_switch_context_t switch_ctx;
	bool switched_map = false;
	unsigned int frame_index = 0;
	int error = 0;
	size_t frame_size = 0;
	bool truncated = false;
	bool user_64 = false;
	bool allow_async = true;
	bool has_async = false;
	uintptr_t async_frame_addr = 0;
	unsigned int async_index = 0;

	backtrace_user_copy_fn copy = ctl->btc_user_copy ?: _backtrace_copyin;
	bool custom_copy = copy != _backtrace_copyin;
	void *ctx = ctl->btc_user_copy_context;

	void *thread = ctl->btc_user_thread;
	void *cur_thread = NULL;
	if (thread == NULL) {
		cur_thread = current_thread();
		thread = cur_thread;
	}
	task_t task = get_threadtask(thread);

	assert(task != NULL);
	assert(bt != NULL);
	assert(max_frames > 0);

	if (!custom_copy) {
		bool interrupts_enabled = ml_get_interrupts_enabled();
		assert(interrupts_enabled);
		if (!interrupts_enabled) {
			error = EDEADLK;
			goto out;
		}

		if (cur_thread == NULL) {
			cur_thread = current_thread();
		}
		bool const must_switch_maps = thread != cur_thread;
		if (must_switch_maps) {
			map = get_task_map_reference(task);
			if (map == NULL) {
				error = ENOMEM;
				goto out;
			}
			switched_map = true;
			switch_ctx = vm_map_switch_to(map);
		}
	}

#define SWIFT_ASYNC_FP_BIT (0x1ULL << 60)
#define SWIFT_ASYNC_FP(FP) (((FP) & SWIFT_ASYNC_FP_BIT) != 0)
#define SWIFT_ASYNC_FP_CLEAR(FP) ((FP) & ~SWIFT_ASYNC_FP_BIT)

#if defined(__x86_64__)

	// Don't allow a malformed user stack to copy arbitrary kernel data.
#define INVALID_USER_FP(FP) ((FP) == 0 || !IS_USERADDR64_CANONICAL((FP)))

	x86_saved_state_t *state = get_user_regs(thread);
	if (!state) {
		error = EINVAL;
		goto out;
	}

	user_64 = is_saved_state64(state);
	if (user_64) {
		pc = saved_state64(state)->isf.rip;
		fp = fp != 0 ? fp : saved_state64(state)->rbp;
	} else {
		pc = saved_state32(state)->eip;
		fp = fp != 0 ? fp : saved_state32(state)->ebp;
	}

#elif defined(__arm64__)

	struct arm_saved_state *state = get_user_regs(thread);
	if (!state) {
		error = EINVAL;
		goto out;
	}

	user_64 = is_saved_state64(state);
	pc = get_saved_state_pc(state);
	fp = fp != 0 ? fp : get_saved_state_fp(state);

	// ARM expects stack frames to be aligned to 16 bytes.
#define INVALID_USER_FP(FP) (((FP) & 0x3UL) != 0UL)

#else // defined(__arm64__) || defined(__x86_64__)
#error "unsupported architecture"
#endif // !defined(__arm64__) && !defined(__x86_64__)

	// Only capture the save state PC without a custom frame pointer to walk.
	if (!ctl || ctl->btc_frame_addr == 0) {
		bt[frame_index++] = pc + addr_offset;
	}

	if (frame_index >= max_frames) {
		goto out;
	}

	if (fp == 0) {
		// If the FP is zeroed, then there's no stack to walk, by design.  This
		// happens for workq threads that are being sent back to user space or
		// during boot-strapping operations on other kinds of threads.
		goto out;
	} else if (INVALID_USER_FP(fp)) {
		// Still capture the PC in this case, but mark the stack as truncated
		// and "faulting."  (Using the frame pointer on a call stack would cause
		// an exception.)
		error = EFAULT;
		truncated = true;
		goto out;
	}

	union {
		struct {
			uint64_t fp;
			uint64_t ret;
		} u64;
		struct {
			uint32_t fp;
			uint32_t ret;
		} u32;
	} frame;

	frame_size = 2 * (user_64 ? 8 : 4);

	while (fp != 0 && frame_index < max_frames) {
		error = copy(ctx, (char *)&frame, fp, frame_size);
		if (error) {
			truncated = true;
			goto out;
		}

		// Capture this return address before tripping over any errors finding
		// the next frame to follow.
		uintptr_t ret_addr = user_64 ? frame.u64.ret : frame.u32.ret;
#if defined(HAS_APPLE_PAC)
		// Return addresses are signed by arm64e ABI, so strip off the auth
		// bits.
		bt[frame_index++] = (uintptr_t)ptrauth_strip((void *)ret_addr,
		    ptrauth_key_return_address) + addr_offset;
#else // defined(HAS_APPLE_PAC)
		bt[frame_index++] = ret_addr + addr_offset;
#endif // !defined(HAS_APPLE_PAC)

		// Find the next frame to follow.
		next_fp = user_64 ? frame.u64.fp : frame.u32.fp;
		bool async_frame = allow_async && SWIFT_ASYNC_FP(next_fp);
		// There is no 32-bit ABI for Swift async call stacks.
		if (user_64 && async_frame) {
			async_index = frame_index - 1;
			// The async context pointer is just below the stack frame.
			user_addr_t async_ctx_ptr = fp - 8;
			user_addr_t async_ctx = 0;
			error = copy(ctx, (char *)&async_ctx, async_ctx_ptr,
			    sizeof(async_ctx));
			if (error) {
				goto out;
			}
#if defined(HAS_APPLE_PAC)
			async_frame_addr = (uintptr_t)ptrauth_strip((void *)async_ctx,
			    ptrauth_key_process_dependent_data);
#else // defined(HAS_APPLE_PAC)
			async_frame_addr = (uintptr_t)async_ctx;
#endif // !defined(HAS_APPLE_PAC)
			has_async = true;
			allow_async = false;
		}
		next_fp = SWIFT_ASYNC_FP_CLEAR(next_fp);
#if defined(HAS_APPLE_PAC)
		next_fp = (uintptr_t)ptrauth_strip((void *)next_fp,
		    ptrauth_key_frame_pointer);
#endif // defined(HAS_APPLE_PAC)
		if (INVALID_USER_FP(next_fp)) {
			break;
		}

		// User space stacks generally grow down, but in some cases can jump to a different stack.
		// Skip the check that the frame pointer moves downward here.

		if (next_fp == fp) {
			break;
		}
		fp = next_fp;
	}

out:
	if (switched_map) {
		vm_map_switch_back(switch_ctx);
		vm_map_deallocate(map);
	}

	// NULL-terminate the list, if space is available.
	if (frame_index < max_frames) {
		bt[frame_index] = 0;
	}

	if (info_out) {
		info_out->btui_error = error;
		backtrace_info_t info = user_64 ? BTI_64_BIT : BTI_NONE;
		bool out_of_space = !INVALID_USER_FP(fp) && frame_index == max_frames;
		if (truncated || out_of_space) {
			info |= BTI_TRUNCATED;
		}
		if (out_of_space && error == 0) {
			info_out->btui_next_frame_addr = fp;
		}
		info_out->btui_info = info;
		info_out->btui_async_start_index = async_index;
		info_out->btui_async_frame_addr = async_frame_addr;
	}

	return frame_index;
}

void stack_trace_print(const unsigned long *entries, unsigned int nr_entries,
		       int spaces)
{
	unsigned int i;

	if (WARN_ON(!entries))
		return;

	for (i = 0; i < nr_entries; i++)
		printk("%*c%pS\n", 1 + spaces, ' ', (void *)entries[i]);
}
EXPORT_SYMBOL_GPL(stack_trace_print);

/**
 * stack_trace_snprint - Print the entries in the stack trace into a buffer
 * @buf:	Pointer to the print buffer
 * @size:	Size of the print buffer
 * @entries:	Pointer to storage array
 * @nr_entries:	Number of entries in the storage array
 * @spaces:	Number of leading spaces to print
 *
 * Return: Number of bytes printed.
 */
int stack_trace_snprint(char *buf, size_t size, const unsigned long *entries,
			unsigned int nr_entries, int spaces)
{
	unsigned int generated, i, total = 0;

	if (WARN_ON(!entries))
		return 0;

	for (i = 0; i < nr_entries && size; i++) {
		generated = snprintf(buf, size, "%*c%pS\n", 1 + spaces, ' ',
				     (void *)entries[i]);

		total += generated;
		if (generated >= size) {
			buf += size;
			size = 0;
		} else {
			buf += generated;
			size -= generated;
		}
	}

	return total;
}
EXPORT_SYMBOL_GPL(stack_trace_snprint);

#ifdef CONFIG_ARCH_STACKWALK

struct stacktrace_cookie {
	unsigned long	*store;
	unsigned int	size;
	unsigned int	skip;
	unsigned int	len;
};

static bool stack_trace_consume_entry(void *cookie, unsigned long addr)
{
	struct stacktrace_cookie *c = cookie;

	if (c->len >= c->size)
		return false;

	if (c->skip > 0) {
		c->skip--;
		return true;
	}
	c->store[c->len++] = addr;
	return c->len < c->size;
}

static bool stack_trace_consume_entry_nosched(void *cookie, unsigned long addr)
{
	if (in_sched_functions(addr))
		return true;
	return stack_trace_consume_entry(cookie, addr);
}

/**
 * stack_trace_save - Save a stack trace into a storage array
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored.
 */
unsigned int stack_trace_save(unsigned long *store, unsigned int size,
			      unsigned int skipnr)
{
	stack_trace_consume_fn consume_entry = stack_trace_consume_entry;
	struct stacktrace_cookie c = {
		.store	= store,
		.size	= size,
		.skip	= skipnr + 1,
	};

	arch_stack_walk(consume_entry, &c, current, NULL);
	return c.len;
}
EXPORT_SYMBOL_GPL(stack_trace_save);

/**
 * stack_trace_save_tsk - Save a task stack trace into a storage array
 * @tsk:	The task to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored.
 */
unsigned int stack_trace_save_tsk(struct task_struct *tsk, unsigned long *store,
				  unsigned int size, unsigned int skipnr)
{
	stack_trace_consume_fn consume_entry = stack_trace_consume_entry_nosched;
	struct stacktrace_cookie c = {
		.store	= store,
		.size	= size,
		/* skip this function if they are tracing us */
		.skip	= skipnr + (current == tsk),
	};

	if (!try_get_task_stack(tsk))
		return 0;

	arch_stack_walk(consume_entry, &c, tsk, NULL);
	put_task_stack(tsk);
	return c.len;
}
EXPORT_SYMBOL_GPL(stack_trace_save_tsk);

/**
 * stack_trace_save_regs - Save a stack trace based on pt_regs into a storage array
 * @regs:	Pointer to pt_regs to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored.
 */
unsigned int stack_trace_save_regs(struct pt_regs *regs, unsigned long *store,
				   unsigned int size, unsigned int skipnr)
{
	stack_trace_consume_fn consume_entry = stack_trace_consume_entry;
	struct stacktrace_cookie c = {
		.store	= store,
		.size	= size,
		.skip	= skipnr,
	};

	arch_stack_walk(consume_entry, &c, current, regs);
	return c.len;
}

#ifdef CONFIG_HAVE_RELIABLE_STACKTRACE
/**
 * stack_trace_save_tsk_reliable - Save task stack with verification
 * @tsk:	Pointer to the task to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 *
 * Return:	An error if it detects any unreliable features of the
 *		stack. Otherwise it guarantees that the stack trace is
 *		reliable and returns the number of entries stored.
 *
 * If the task is not 'current', the caller *must* ensure the task is inactive.
 */
int stack_trace_save_tsk_reliable(struct task_struct *tsk, unsigned long *store,
				  unsigned int size)
{
	stack_trace_consume_fn consume_entry = stack_trace_consume_entry;
	struct stacktrace_cookie c = {
		.store	= store,
		.size	= size,
	};
	int ret;

	/*
	 * If the task doesn't have a stack (e.g., a zombie), the stack is
	 * "reliably" empty.
	 */
	if (!try_get_task_stack(tsk))
		return 0;

	ret = arch_stack_walk_reliable(consume_entry, &c, tsk);
	put_task_stack(tsk);
	return ret ? ret : c.len;
}
#endif

#ifdef CONFIG_USER_STACKTRACE_SUPPORT
/**
 * stack_trace_save_user - Save a user space stack trace into a storage array
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 *
 * Return: Number of trace entries stored.
 */
unsigned int stack_trace_save_user(unsigned long *store, unsigned int size)
{
	stack_trace_consume_fn consume_entry = stack_trace_consume_entry;
	struct stacktrace_cookie c = {
		.store	= store,
		.size	= size,
	};

	/* Trace user stack if not a kernel thread */
	if (current->flags & PF_KTHREAD)
		return 0;

	arch_stack_walk_user(consume_entry, &c, task_pt_regs(current));

	return c.len;
}
#endif

#else /* CONFIG_ARCH_STACKWALK */

/*
 * Architectures that do not implement save_stack_trace_*()
 * get these weak aliases and once-per-bootup warnings
 * (whenever this facility is utilized - for example by procfs):
 */
__weak void
save_stack_trace_tsk(struct task_struct *tsk, struct stack_trace *trace)
{
	WARN_ONCE(1, KERN_INFO "save_stack_trace_tsk() not implemented yet.\n");
}

__weak void
save_stack_trace_regs(struct pt_regs *regs, struct stack_trace *trace)
{
	WARN_ONCE(1, KERN_INFO "save_stack_trace_regs() not implemented yet.\n");
}

/**
 * stack_trace_save - Save a stack trace into a storage array
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored
 */
unsigned int stack_trace_save(unsigned long *store, unsigned int size,
			      unsigned int skipnr)
{
	struct stack_trace trace = {
		.entries	= store,
		.max_entries	= size,
		.skip		= skipnr + 1,
	};

	save_stack_trace(&trace);
	return trace.nr_entries;
}
EXPORT_SYMBOL_GPL(stack_trace_save);

/**
 * stack_trace_save_tsk - Save a task stack trace into a storage array
 * @task:	The task to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored
 */
unsigned int stack_trace_save_tsk(struct task_struct *task,
				  unsigned long *store, unsigned int size,
				  unsigned int skipnr)
{
	struct stack_trace trace = {
		.entries	= store,
		.max_entries	= size,
		/* skip this function if they are tracing us */
		.skip	= skipnr + (current == task),
	};

	save_stack_trace_tsk(task, &trace);
	return trace.nr_entries;
}
EXPORT_SYMBOL_GPL(stack_trace_save_tsk);

/**
 * stack_trace_save_regs - Save a stack trace based on pt_regs into a storage array
 * @regs:	Pointer to pt_regs to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 * @skipnr:	Number of entries to skip at the start of the stack trace
 *
 * Return: Number of trace entries stored
 */
unsigned int stack_trace_save_regs(struct pt_regs *regs, unsigned long *store,
				   unsigned int size, unsigned int skipnr)
{
	struct stack_trace trace = {
		.entries	= store,
		.max_entries	= size,
		.skip		= skipnr,
	};

	save_stack_trace_regs(regs, &trace);
	return trace.nr_entries;
}

#ifdef CONFIG_HAVE_RELIABLE_STACKTRACE
/**
 * stack_trace_save_tsk_reliable - Save task stack with verification
 * @tsk:	Pointer to the task to examine
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 *
 * Return:	An error if it detects any unreliable features of the
 *		stack. Otherwise it guarantees that the stack trace is
 *		reliable and returns the number of entries stored.
 *
 * If the task is not 'current', the caller *must* ensure the task is inactive.
 */
int stack_trace_save_tsk_reliable(struct task_struct *tsk, unsigned long *store,
				  unsigned int size)
{
	struct stack_trace trace = {
		.entries	= store,
		.max_entries	= size,
	};
	int ret = save_stack_trace_tsk_reliable(tsk, &trace);

	return ret ? ret : trace.nr_entries;
}
#endif

#ifdef CONFIG_USER_STACKTRACE_SUPPORT
/**
 * stack_trace_save_user - Save a user space stack trace into a storage array
 * @store:	Pointer to storage array
 * @size:	Size of the storage array
 *
 * Return: Number of trace entries stored
 */
unsigned int stack_trace_save_user(unsigned long *store, unsigned int size)
{
	struct stack_trace trace = {
		.entries	= store,
		.max_entries	= size,
	};

	save_stack_trace_user(&trace);
	return trace.nr_entries;
}
#endif /* CONFIG_USER_STACKTRACE_SUPPORT */

#endif /* !CONFIG_ARCH_STACKWALK */

static inline bool in_irqentry_text(unsigned long ptr)
{
	return (ptr >= (unsigned long)&__irqentry_text_start &&
		ptr < (unsigned long)&__irqentry_text_end) ||
		(ptr >= (unsigned long)&__softirqentry_text_start &&
		 ptr < (unsigned long)&__softirqentry_text_end);
}

/**
 * filter_irq_stacks - Find first IRQ stack entry in trace
 * @entries:	Pointer to stack trace array
 * @nr_entries:	Number of entries in the storage array
 *
 * Return: Number of trace entries until IRQ stack starts.
 */
unsigned int filter_irq_stacks(unsigned long *entries, unsigned int nr_entries)
{
	unsigned int i;

	for (i = 0; i < nr_entries; i++) {
		if (in_irqentry_text(entries[i])) {
			/* Include the irqentry function into the stack. */
			return i + 1;
		}
	}
	return nr_entries;
}
EXPORT_SYMBOL_GPL(filter_irq_stacks);
