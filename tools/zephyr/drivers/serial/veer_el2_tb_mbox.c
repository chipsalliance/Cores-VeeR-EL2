/*
 * VeeR EL2 testbench "UART": every byte written to the mailbox address
 * is printed by tb_top. Output only.
 */
#define DT_DRV_COMPAT chipsalliance_veer_el2_tb_mailbox

#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/fatal.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/sys/poweroff.h>
#include <zephyr/sys/sys_io.h>
#include <zephyr/arch/cpu.h>
#include <errno.h>

#define TB_MBOX_ADDR   DT_INST_REG_ADDR(0)
#define TB_CODE_PASS   0xFF
#define TB_CODE_FAIL   0x01


struct mbox_config {
	mem_addr_t base;
};

static void mbox_poll_out(const struct device *dev, unsigned char c)
{
	const struct mbox_config *cfg = dev->config;

	if (c == TB_CODE_PASS || c == TB_CODE_FAIL) {
		c = '?';
	}
	sys_write8(c, cfg->base);
}

static int mbox_poll_in(const struct device *dev, unsigned char *c)
{
	ARG_UNUSED(dev);
	ARG_UNUSED(c);
	return -ENOTSUP;
}

static DEVICE_API(uart, mbox_api) = {
	.poll_in  = mbox_poll_in,
	.poll_out = mbox_poll_out,
};


#ifdef CONFIG_VEER_EL2_TB_EXIT

static FUNC_NORETURN void tb_exit(uint8_t code)
{
	sys_write8(code, TB_MBOX_ADDR);
	for (;;) {
		/* tb ends the simulation on this write */
	}
}

/* Success path: sys_poweroff() lands here */
void z_sys_poweroff(void)
{
	tb_exit(TB_CODE_PASS);
}

/* Failure path: overrides the weak default */
void k_sys_fatal_error_handler(unsigned int reason, const struct arch_esf *esf)
{
	ARG_UNUSED(esf);
	printk("FATAL: reason %u\n", reason);
	tb_exit(TB_CODE_FAIL);
}

#if CONFIG_VEER_EL2_TB_EXIT_AFTER_MS > 0
static void tb_exit_timer_fn(struct k_timer *t)
{
	ARG_UNUSED(t);
	printk("\nTB: %d ms without fatal error, passing\n",
	       CONFIG_VEER_EL2_TB_EXIT_AFTER_MS);
	sys_poweroff();
}
K_TIMER_DEFINE(tb_exit_timer, tb_exit_timer_fn, NULL);

static int tb_exit_init(void)
{
	k_timer_start(&tb_exit_timer, K_MSEC(CONFIG_VEER_EL2_TB_EXIT_AFTER_MS),
		      K_NO_WAIT);
	return 0;
}
SYS_INIT(tb_exit_init, APPLICATION, 99);
#endif

#ifdef CONFIG_VEER_EL2_TB_EXIT_ON_MAIN_RETURN
int __real_main(void);

int __wrap_main(void)
{
	int ret = __real_main();

	if (ret != 0) {
		printk("Test failed with status %d\n", ret);
		tb_exit(TB_CODE_FAIL);
	}
	sys_poweroff();
}
#endif

#endif /* CONFIG_VEER_EL2_TB_EXIT */

#define MBOX_INIT(n)                                                    \
	static const struct mbox_config mbox_cfg_##n = {                \
		.base = DT_INST_REG_ADDR(n),                            \
	};                                                              \
	DEVICE_DT_INST_DEFINE(n, NULL, NULL, NULL, &mbox_cfg_##n,       \
			      PRE_KERNEL_1, CONFIG_SERIAL_INIT_PRIORITY,\
			      &mbox_api);

DT_INST_FOREACH_STATUS_OKAY(MBOX_INIT)
