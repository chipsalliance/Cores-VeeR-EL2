// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

#define DT_DRV_COMPAT chipsalliance_veer_el2_timer
#include <zephyr/drivers/timer/system_timer.h>
#include <zephyr/arch/riscv/csr.h>
#include <zephyr/irq.h>
#include <zephyr/init.h>

#define MITCNT0 0x7D2
#define MITB0   0x7D3
#define MITCTL0 0x7D4
#define MITCTL_EN      BIT(0)
#define MITCTL_HALT_EN BIT(1)
#define MITCTL_PAUSE_EN BIT(2)

#define CYC_PER_TICK (CONFIG_SYS_CLOCK_HW_CYCLES_PER_SEC / \
                      CONFIG_SYS_CLOCK_TICKS_PER_SEC)


static uint64_t last_announced_mcycle;

static void timer_isr(const void *arg)
{
	ARG_UNUSED(arg);

	/* Internal timer interrupt is a 1-cycle pulse. Pulses that hit while
	   interrupts are masked are lost, so derive elapsed ticks from mcycle
	   instead of counting interrupts. */
	uint64_t now = sys_clock_cycle_get_64();
	uint32_t ticks = (uint32_t)((now - last_announced_mcycle) / CYC_PER_TICK);

	last_announced_mcycle += (uint64_t)ticks * CYC_PER_TICK;
	sys_clock_announce(ticks);
}

uint32_t sys_clock_elapsed(void)
{
	/* Whole ticks not yet announced, normally 0
	   >0 if a timer pulse was lost while interrupts were masked */
	return (uint32_t)((sys_clock_cycle_get_64() - last_announced_mcycle) / CYC_PER_TICK);
}

/* Free-running cycle count: standard mcycle, not the internal timer */
uint32_t sys_clock_cycle_get_32(void) { return csr_read(mcycle); }
uint64_t sys_clock_cycle_get_64(void)
{
	uint32_t hi, lo;
	do {
		hi = csr_read(mcycleh);
		lo = csr_read(mcycle);
	} while (hi != csr_read(mcycleh));
	return ((uint64_t)hi << 32) | lo;
}

static int sys_clock_driver_init(void)
{
	csr_write(MITCTL0, 0);
	csr_write(MITCNT0, 0);
	csr_write(MITB0, CYC_PER_TICK - 1);
	IRQ_CONNECT(DT_INST_IRQN(0), 0, timer_isr, NULL, 0);
	irq_enable(DT_INST_IRQN(0));

	last_announced_mcycle = sys_clock_cycle_get_64();

	csr_write(MITCTL0, MITCTL_EN | MITCTL_HALT_EN | MITCTL_PAUSE_EN);
	return 0;
}

SYS_INIT(sys_clock_driver_init, PRE_KERNEL_2, CONFIG_SYSTEM_CLOCK_INIT_PRIORITY);
