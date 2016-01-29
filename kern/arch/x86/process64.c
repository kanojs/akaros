#include <arch/arch.h>
#include <trap.h>
#include <process.h>
#include <pmap.h>
#include <smp.h>

#include <string.h>
#include <assert.h>
#include <stdio.h>

static void __attribute__((noreturn)) proc_pop_hwtf(struct hw_trapframe *tf)
{
	/* for both HW and SW, note we pass an offset into the TF, beyond the fs and
	 * gs bases */
	if (x86_hwtf_is_partial(tf)) {
		swap_gs();
	} else {
		write_msr(MSR_GS_BASE, (uint64_t)tf->tf_gsbase);
		write_msr(MSR_FS_BASE, (uint64_t)tf->tf_fsbase);
	}
	asm volatile ("movq %0, %%rsp;          "
	              "popq %%rax;              "
	              "popq %%rbx;              "
	              "popq %%rcx;              "
	              "popq %%rdx;              "
	              "popq %%rbp;              "
	              "popq %%rsi;              "
	              "popq %%rdi;              "
	              "popq %%r8;               "
	              "popq %%r9;               "
	              "popq %%r10;              "
	              "popq %%r11;              "
	              "popq %%r12;              "
	              "popq %%r13;              "
	              "popq %%r14;              "
	              "popq %%r15;              "
	              "addq $0x10, %%rsp;       "
	              "iretq                    "
	              : : "g" (&tf->tf_rax) : "memory");
	panic("iretq failed");
}

static void __attribute__((noreturn)) proc_pop_swtf(struct sw_trapframe *tf)
{
	if (x86_swtf_is_partial(tf)) {
		swap_gs();
	} else {
		write_msr(MSR_GS_BASE, (uint64_t)tf->tf_gsbase);
		write_msr(MSR_FS_BASE, (uint64_t)tf->tf_fsbase);
	}
	/* We need to 0 out any registers that aren't part of the sw_tf and that we
	 * won't use/clobber on the out-path.  While these aren't part of the sw_tf,
	 * we also don't want to leak any kernel register content. */
	asm volatile ("movq %0, %%rsp;          "
	              "movq $0, %%rax;          "
	              "movq $0, %%rdx;          "
	              "movq $0, %%rsi;          "
	              "movq $0, %%rdi;          "
	              "movq $0, %%r8;           "
	              "movq $0, %%r9;           "
	              "movq $0, %%r10;          "
	              "popq %%rbx;              "
	              "popq %%rbp;              "
	              "popq %%r12;              "
	              "popq %%r13;              "
	              "popq %%r14;              "
	              "popq %%r15;              "
	              "movq %1, %%r11;          "
	              "popq %%rcx;              "
	              "popq %%rsp;              "
	              "rex.w sysret             "
	              : : "g"(&tf->tf_rbx), "i"(FL_IF) : "memory");
	panic("sysret failed");
}

	// XXX  other than exporting stuff (or moving this elsewhere), the
	// vmcs_readl seems fucked.  is an l 64? 32?  we have those other funcs too
	// 		seems like it's just a casting thing
	// 		so they have one instruction that just knows to read/write the right
	// 		amount?
	extern void vmcs_writel(unsigned long field, unsigned long value);
	extern unsigned long vmcs_readl(unsigned long field);
	extern bool vmm_emulate_msr(uint64_t *rcx, uint64_t *rdx, uint64_t *rax,
	                            int op);
	void vmcs_clear(struct vmcs *vmcs);
	void vmcs_load(struct vmcs *vmcs);
	void __vmx_setup_cpu(void);

// XXX move all this to trap.c
static void set_current_ctx_vm(struct per_cpu_info *pcpui,
                               struct vm_trapframe *vm_tf)
{
	assert(!irq_is_enabled());
	assert(!pcpui->cur_ctx);
	pcpui->actual_ctx.type = ROS_VM_CTX;
	pcpui->actual_ctx.tf.vm_tf = *vm_tf;
	pcpui->cur_ctx = &pcpui->actual_ctx;
}

static bool handle_vmexit_cpuid(struct vm_trapframe *tf)
{
	uint32_t eax, ebx, ecx, edx;

	cpuid(tf->tf_rax, tf->tf_rcx, &eax, &ebx, &ecx, &edx);
	tf->tf_rax = eax;
	tf->tf_rbx = ebx;
	tf->tf_rcx = ecx;
	tf->tf_rdx = edx;
	tf->tf_rip += 2;
	return TRUE;
}

static bool handle_vmexit_ept_fault(struct vm_trapframe *tf)
{
	int prot = 0;
	int ret;

	prot |= tf->tf_exit_qual & VMX_EPT_FAULT_READ ? PROT_READ : 0;
	prot |= tf->tf_exit_qual & VMX_EPT_FAULT_WRITE ? PROT_WRITE : 0;
	prot |= tf->tf_exit_qual & VMX_EPT_FAULT_INS ? PROT_EXEC : 0;
	ret = handle_page_fault(current, tf->tf_guest_pa, prot);
	if (ret) {
		/* TODO: maybe put ret in the TF somewhere */
		return FALSE;
	}
	return TRUE;
}

static bool handle_vmexit_nmi(struct vm_trapframe *tf)
{

	/* our NMI handler from trap.c won't run.  but we don't need the lock
	 * disabling stuff. */

			/* This is a bit hacky, but we don't have a decent API yet */
				// printx?
			extern bool mon_verbose_trace;
			if (mon_verbose_trace) {
				print_vmtrapframe(tf);
				// XXX
				//backtrace_hwtf(hw_tf);// a BT of the guest VM would be nice
			}
			printk("\n\n\n");	// visual test to see if we're running this
			printk("Core %d is at %p\n", core_id(), get_vmtf_pc(tf));

	/* XXX what are we really supposed to do here? */
	// is there something about NMIs being blocked during this handler?
	return (tf->tf_intrinfo2 & INTR_INFO_INTR_TYPE_MASK) == INTR_TYPE_NMI_INTR;
}

bool handle_vmexit_msr(struct vm_trapframe *tf)
{
	bool ret;

	ret = vmm_emulate_msr(&tf->tf_rcx, &tf->tf_rdx, &tf->tf_rax,
	                      tf->tf_exit_reason);
	if (ret)
		tf->tf_rip += 2;
	return ret;
}

// XXX
extern uintptr_t gva2gpa(struct proc *p, uintptr_t cr3, uintptr_t gva);

//void xme(struct proc *p, uintptr_t cr3, uintptr_t gva)
//{
//	uintptr_t gpa = gva2gpa(p, cr3, gva);
//	printk("gpa %p\n", gpa);
//}

static void vmexit_dispatch(struct vm_trapframe *tf)
{
	bool handled = FALSE;

	// XXX if there's a chance we'll block in here, we need to finalize the ctx
	// first and protect all of our accesses to the VMCS region.
	// 		the danger is that once we finalize, we can start the vcpu on
	// 		another core, and then fail.  so it'd be nice to not block.
	//
	// XXX check and mask the top bit of exit_reason.   (for errors on startup)
	switch (tf->tf_exit_reason) {
	case EXIT_REASON_VMCALL:
		// XXX probably just remove this flag completely.
		if (current->vmm.flags & VMM_VMCALL_PRINTF) {
			printk("%c", tf->tf_rdi);
			tf->tf_rip += 3;
			handled = TRUE;
		}
		break;
	case EXIT_REASON_CPUID:
		handled = handle_vmexit_cpuid(tf);
		break;
	case EXIT_REASON_EPT_VIOLATION:
		handled = handle_vmexit_ept_fault(tf);
		break;
	case EXIT_REASON_EXCEPTION_NMI:
		handled = handle_vmexit_nmi(tf);
		break;
	case EXIT_REASON_MSR_READ:
	case EXIT_REASON_MSR_WRITE:
		handled = handle_vmexit_msr(tf);
		break;
	case EXIT_REASON_EXTERNAL_INTERRUPT:
		// XXX prob need to call the regular IRQ/trap handlers for the kernel
		// 		if we call them, we need to not have them set_cur_ctx.  it's
		// 		already done.  that mess assumes HW_TF.  
		// 			and our actions might be diff based on the type of TF.
		// 		prob can assume this is never a trap.  or shouldn't be.
		// 			yeah, let's assert that though
		// 	 had this trigger once when i would have expected a PIR
		printd("EXTERNAL IRQ, info field %p\n", tf->tf_intrinfo2);

		lapic_send_eoi(0);
		handled = TRUE;
		break;
	case EXIT_REASON_APIC_WRITE:
		/* TODO: what do we want to do here?  There's something about the write
		 * already being virtualized, but we need to do a little more?
		 *
		 * I needed to say it was handled, and not reflect it to the user. */
			// XXX something vmrunkernel is doing?
		handled = TRUE;
		break;
	case EXIT_REASON_CR_ACCESS:
	case EXIT_REASON_IO_INSTRUCTION:
		break;
	default:
		printk("unhandled vmexit: reason 0x%x, exit qualification 0x%x\n",
		       tf->tf_exit_reason, tf->tf_exit_qual);
	}

	if (!handled) {
		tf->tf_flags |= VMCTX_FL_HAS_FAULT;
		if (reflect_current_context()) {
			/* VM contexts shouldn't be in vcore context, so this should be
			 * pretty rare (unlike SCPs or VC ctx page faults). */
			printk("Unable to reflect VM Exit\n");
			print_vmtrapframe(tf);
			proc_destroy(current);
		}
	}
}

void handle_vmexit(struct vm_trapframe *tf)
{
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];

	tf->tf_rip = vmcs_readl(GUEST_RIP);
	tf->tf_rflags = vmcs_readl(GUEST_RFLAGS);
	tf->tf_rsp = vmcs_readl(GUEST_RSP);
	tf->tf_cr2 = rcr2();
	tf->tf_cr3 = vmcs_readl(GUEST_CR3);
	tf->tf_guest_pcoreid = pcpui->guest_pcoreid;
	tf->tf_flags |= VMCTX_FL_PARTIAL;
	tf->tf_exit_reason = vmcs_readl(VM_EXIT_REASON);	// XXX read32?
	tf->tf_exit_qual = vmcs_readl(EXIT_QUALIFICATION);	// XXX read32?
	tf->tf_intrinfo1 = vmcs_readl(GUEST_INTERRUPTIBILITY_INFO);
	tf->tf_intrinfo2 = vmcs_readl(VM_EXIT_INTR_INFO);
	tf->tf_guest_va = vmcs_readl(GUEST_LINEAR_ADDRESS);
	tf->tf_guest_pa = vmcs_readl(GUEST_PHYSICAL_ADDRESS);	// XXX 64 or l?

	set_current_ctx_vm(pcpui, tf);
	tf = &pcpui->cur_ctx->tf.vm_tf;
	/* We can enable IRQs pretty early, I think.  I held off til after we
	 * set_current_ctx for debugging. */
	enable_irq();
	vmexit_dispatch(tf);

	/* We're either restarting a partial VM ctx (vmcs was launched, loaded on
	 * the core, etc) or a SW vc ctx for the reflected trap.  Or the proc is
	 * dying and we'll handle a __death KMSG shortly. */
	disable_irq();
	proc_restartcore();
}

struct vmx_vcpu *lookup_guest_pcore(struct proc *p, int guest_pcoreid)
{
	/* nr_guest_pcores is written once at setup and never changed */
	if (guest_pcoreid >= p->vmm.nr_guest_pcores)
		return 0;
	return p->vmm.guest_pcores[guest_pcoreid];
}

struct vmx_vcpu *load_guest_pcore(struct proc *p, int guest_pcoreid)
{
	struct vmx_vcpu *gpc;
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];

	gpc = lookup_guest_pcore(p, guest_pcoreid);
	if (!gpc)
		return 0;
	assert(pcpui->guest_pcoreid == -1);
	spin_lock(&p->vmm.lock);
	if (gpc->cpu != -1) {
		spin_unlock(&p->vmm.lock);
		return 0;
	}
	gpc->cpu = core_id();
	spin_unlock(&p->vmm.lock);
	/* We've got dibs on the gpc; we don't need to hold the lock any longer. */
	pcpui->guest_pcoreid = guest_pcoreid;
	ept_sync_context(vcpu_get_eptp(gpc));
	vmcs_load(gpc->vmcs);
	__vmx_setup_cpu();
	return gpc;
}

void unload_guest_pcore(struct proc *p, int guest_pcoreid)
{
	struct vmx_vcpu *gpc;
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];

	gpc = lookup_guest_pcore(p, guest_pcoreid);
	assert(gpc);
	spin_lock(&p->vmm.lock);
	assert(gpc->cpu != -1);
	ept_sync_context(vcpu_get_eptp(gpc));
	vmcs_clear(gpc->vmcs);
	gpc->cpu = -1;
	/* As soon as we unlock, this gpc can be started on another core */
	spin_unlock(&p->vmm.lock);
	pcpui->guest_pcoreid = -1;
}

// XXX fucked header
void finalize_vmtf(void)
{
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];

	unload_guest_pcore(pcpui->cur_proc, pcpui->guest_pcoreid);
}

static void __attribute__((noreturn)) proc_pop_vmtf(struct vm_trapframe *tf)
{
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];
	struct proc *p = pcpui->cur_proc;
	struct vmx_vcpu *gpc;

	if (x86_vmtf_is_partial(tf)) {
		gpc = lookup_guest_pcore(p, tf->tf_guest_pcoreid);
		assert(gpc);
		assert(pcpui->guest_pcoreid == tf->tf_guest_pcoreid);
	} else {
		gpc = load_guest_pcore(p, tf->tf_guest_pcoreid);
		if (!gpc) {
			// XXX GPC is already in use, reflect back to the user
			assert(0);
		}
	}

	// XXX for all of these vmcs writes that might not have changed, we could
	// cache stuff like KERNEL_GS_BASE, stacktop, maybe GS_BASE.  we only need
	// to change those if we changed pcore (which we can track with get_cpu)
	// 		how expensive are vmcs writes?  cr2 loads?

	// XXX something faster than rdmsr?  like just  = (uintptr_t)pcpui
	// XXX host[0] is K_GS_BASE?
	// 		btw, we can set HOST_GS_BASE in the VMCS so we have TLS immediately
	// 			other than FS and GS base, others could be autoloaded
	// 				(like EFER, PERF, PAT.  we could avoid autoloading those)
	gpc->msr_autoload.host[0].value = read_msr(MSR_KERNEL_GS_BASE);

	// XXX get_stacktop() instead?
	vmcs_writel(HOST_RSP, pcpui->stacktop);
	vmcs_writel(HOST_GS_BASE, (unsigned long)pcpui);

	// XXX could store cr2 internally and have cr3 in gpci
	vmcs_writel(GUEST_RSP, tf->tf_rsp);
	vmcs_writel(GUEST_CR3, tf->tf_cr3);
	vmcs_writel(GUEST_RIP, tf->tf_rip);

	// XXX 0x2 is the reserved bit.  need better rflags mgmt.
	// 		same with securing any TF.  and write_eflags.
	// 			those don't need it. 
	// 		probably other eflags that need securing
	vmcs_writel(GUEST_RFLAGS, tf->tf_rflags | 0x2);

	/* cr2 is not part of the VMCS state; we need to save/restore it manually */
	lcr2(tf->tf_cr2);

	// XXX does this work yet?
	// 		had it fuck up, might be the VMM's fault
	//vmcs_writel(VM_ENTRY_INTR_INFO_FIELD, tf->tf_trap_inject);


	/* vmlaunch/resume can fail, so we need to be able to return from this.
	 * Thus we can't clobber rsp via the popq style of setting the registers.
	 * Likewise, we don't want to lose rbp via the clobber list.
	 *
	 * Partial contexts have already been launched, so we resume them. */
	asm volatile ("testl $"STRINGIFY(VMCTX_FL_PARTIAL)", %c[flags](%0);" 
	              "pushq %%rbp;              "	/* save in case we fail */
	              "movq %c[rbx](%0), %%rbx;  "
	              "movq %c[rcx](%0), %%rcx;  "
	              "movq %c[rdx](%0), %%rdx;  "
	              "movq %c[rbp](%0), %%rbp;  "
	              "movq %c[rsi](%0), %%rsi;  "
	              "movq %c[rdi](%0), %%rdi;  "
	              "movq %c[r8](%0),  %%r8;   "
	              "movq %c[r9](%0),  %%r9;   "
	              "movq %c[r10](%0), %%r10;  "
	              "movq %c[r11](%0), %%r11;  "
	              "movq %c[r12](%0), %%r12;  "
	              "movq %c[r13](%0), %%r13;  "
	              "movq %c[r14](%0), %%r14;  "
	              "movq %c[r15](%0), %%r15;  "
	              "movq %c[rax](%0), %%rax;  "	/* clobber our *tf last */
	              "jnz 1f;                   "	/* jump if partial */
	              ASM_VMX_VMLAUNCH";         "	/* non-partial gets launched */
	              "jmp 2f;                   "
	              "1: "ASM_VMX_VMRESUME";    "	/* partials get resumed */
	              "2: popq %%rbp;            "	/* vmlaunch failed */
	              :
	              : "a" (tf),
	                [rax]"i"(offsetof(struct vm_trapframe, tf_rax)),
	                [rbx]"i"(offsetof(struct vm_trapframe, tf_rbx)),
	                [rcx]"i"(offsetof(struct vm_trapframe, tf_rcx)),
	                [rdx]"i"(offsetof(struct vm_trapframe, tf_rdx)),
	                [rbp]"i"(offsetof(struct vm_trapframe, tf_rbp)),
	                [rsi]"i"(offsetof(struct vm_trapframe, tf_rsi)),
	                [rdi]"i"(offsetof(struct vm_trapframe, tf_rdi)),
	                 [r8]"i"(offsetof(struct vm_trapframe, tf_r8)),
	                 [r9]"i"(offsetof(struct vm_trapframe, tf_r9)),
	                [r10]"i"(offsetof(struct vm_trapframe, tf_r10)),
	                [r11]"i"(offsetof(struct vm_trapframe, tf_r11)),
	                [r12]"i"(offsetof(struct vm_trapframe, tf_r12)),
	                [r13]"i"(offsetof(struct vm_trapframe, tf_r13)),
	                [r14]"i"(offsetof(struct vm_trapframe, tf_r14)),
	                [r15]"i"(offsetof(struct vm_trapframe, tf_r15)),
	                [flags]"i"(offsetof(struct vm_trapframe, tf_flags))
	              : "cc", "memory", "rbx", "rcx", "rdx", "rsi", "rdi",
	                "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15");
	/* vmlaunch/resume failed.  It could be for a few reasons, including things
	 * like launching instead of resuming, not having a VMCS loaded, failing a
	 * host-state area check, etc.  Those are kernel problems.
	 *
	 * The user also might be able to trigger some of these failures.  For
	 * instance, rflags could be bad, or the trap_injection could be
	 * misformatted.  We might catch that in secure_tf, or we could reflect
	 * those to the user.  Detecting btw the kernel and user mistakes might be
	 * a pain.
	 *
	 * We should always have a non-shadow VMCS, so ZF should be 1 and we can
	 * read the error register. */
	// XXX
	// 		how do we know the diff btw our bug (partial context error) and a
	// 		user bug?  CF vs ZF?  (CF means it was a launch issue)
	//
	// 	there's so much that could go wrong, it's hard for us to be able to
	// 	catch them all.  so maybe just throw it back up.  even if its our fault.
	// 		maybe whitelist kernel mistakes, if we know it is us, we'll
	// 		panic/bug_on.  o/w we pass it back

	unsigned long rflags = read_flags();// XXX grab from ASM? (put addr on stack)


	// XXX vmcs_read32?
	panic("vmlaunch failed, flags %p, error code: %p", rflags,
	      vmcs_readl(VM_INSTRUCTION_ERROR));
}

void proc_pop_ctx(struct user_context *ctx)
{
	disable_irq();
	switch (ctx->type) {
	case ROS_HW_CTX:
		proc_pop_hwtf(&ctx->tf.hw_tf);
		break;
	case ROS_SW_CTX:
		proc_pop_swtf(&ctx->tf.sw_tf);
		break;
	case ROS_VM_CTX:
		proc_pop_vmtf(&ctx->tf.vm_tf);
		break;
	default:
		/* We should have caught this when securing the ctx */
		panic("Unknown context type %d!", ctx->type);
	}
}

/* Helper: if *addr isn't a canonical user address, poison it.  Use this when
 * you need a canonical address (like MSR_FS_BASE) */
static void enforce_user_canon(uintptr_t *addr)
{
	if (*addr >> 47 != 0)
		*addr = 0x5a5a5a5a;
}

void proc_init_ctx(struct user_context *ctx, uint32_t vcoreid, uintptr_t entryp,
                   uintptr_t stack_top, uintptr_t tls_desc)
{
	struct sw_trapframe *sw_tf = &ctx->tf.sw_tf;
	/* zero the entire structure for any type, prevent potential disclosure */
	memset(ctx, 0, sizeof(struct user_context));
	ctx->type = ROS_SW_CTX;
	/* Stack pointers in a fresh stack frame need to be 16 byte aligned
	 * (AMD64 ABI). If we call this function from within load_elf(), it
	 * should already be aligned properly, but we round again here for good
	 * measure. We used to subtract an extra 8 bytes here to allow us to
	 * write our _start() function in C instead of assembly. This was
	 * necessary to account for a preamble inserted the compiler which
	 * assumed a return address was pushed on the stack. Now that we properly
	 * pass our arguments on the stack, we will have to rewrite our _start()
	 * function in assembly to handle things properly. */
	sw_tf->tf_rsp = ROUNDDOWN(stack_top, 16);
	sw_tf->tf_rip = entryp;
	sw_tf->tf_rbp = 0;	/* for potential backtraces */
	sw_tf->tf_mxcsr = 0x00001f80;	/* x86 default mxcsr */
	sw_tf->tf_fpucw = 0x037f;		/* x86 default FP CW */
	/* Coupled closely with user's entry.S.  id is the vcoreid, which entry.S
	 * uses to determine what to do.  vcoreid == 0 is the main core/context. */
	sw_tf->tf_rbx = vcoreid;
	sw_tf->tf_fsbase = tls_desc;
	proc_secure_ctx(ctx);
}

static void proc_secure_hwtf(struct hw_trapframe *tf)
{
	enforce_user_canon(&tf->tf_gsbase);
	enforce_user_canon(&tf->tf_fsbase);
	/* GD_UD is the user data segment selector in the GDT, and
	 * GD_UT is the user text segment selector (see inc/memlayout.h).
	 * The low 2 bits of each segment register contains the
	 * Requestor Privilege Level (RPL); 3 means user mode. */
	tf->tf_ss = GD_UD | 3;
	tf->tf_cs = GD_UT | 3;
	tf->tf_rflags |= FL_IF;
	x86_hwtf_clear_partial(tf);
}

static void proc_secure_swtf(struct sw_trapframe *tf)
{
	enforce_user_canon(&tf->tf_gsbase);
	enforce_user_canon(&tf->tf_fsbase);
	enforce_user_canon(&tf->tf_rip);
	x86_swtf_clear_partial(tf);
}

static void proc_secure_vmtf(struct vm_trapframe *tf)
{
	/* The user can say whatever it wants for the bulk of the TF, but the only
	 * thing it can't fake is whether or not it is a partial context, which
	 * other parts of the kernel rely on. */
	x86_vmtf_clear_partial(tf);
}

void proc_secure_ctx(struct user_context *ctx)
{
	switch (ctx->type) {
	case ROS_HW_CTX:
		proc_secure_hwtf(&ctx->tf.hw_tf);
		break;
	case ROS_SW_CTX:
		proc_secure_swtf(&ctx->tf.sw_tf);
		break;
	case ROS_VM_CTX:
		proc_secure_vmtf(&ctx->tf.vm_tf);
		break;
	default:
		/* If we aren't another ctx type, we're assuming (and forcing) a HW ctx.
		 * If this is somehow fucked up, userspace should die rather quickly. */
		ctx->type = ROS_HW_CTX;
		proc_secure_hwtf(&ctx->tf.hw_tf);
	}
}

/* Called when we are currently running an address space on our core and want to
 * abandon it.  We need a known good pgdir before releasing the old one.  We
 * decref, since current no longer tracks the proc (and current no longer
 * protects the cr3). */
void __abandon_core(void)
{
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];
	lcr3(boot_cr3);
	proc_decref(pcpui->cur_proc);
	pcpui->cur_proc = 0;
}
