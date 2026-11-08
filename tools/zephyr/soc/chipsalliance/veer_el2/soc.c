// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

#include <zephyr/toolchain.h>
#include <zephyr/arch/riscv/csr.h>

#define MRAC 0x7C0

void soc_early_init_hook(void)
{
	csr_write(MRAC, 0x08000000);
}
