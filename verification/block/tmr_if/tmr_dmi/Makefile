#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR   := $(abspath $(TEST_DIR)../../../../../design)
CFGDIR   := $(TEST_DIR)/snapshots/default

TEST_FILES = $(sort $(wildcard test_*.py))

MODULE    ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL   = el2_tmr_dmi

TMR_ENABLE := 1

EXTRA_CONFIG_ARGS += -set=mubi_width=2 -set=mubi_false=0x1 -set=mubi_true=0x2

VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/lib/el2_mem_if.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/tmr/el2_tmr_voter.sv \
    $(SRCDIR)/tmr/el2_tmr_dmi.sv \

include $(TEST_DIR)/../../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/..
