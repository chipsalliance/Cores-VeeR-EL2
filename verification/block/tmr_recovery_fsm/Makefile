#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR   := $(abspath $(TEST_DIR)../../../../design)
CFGDIR   := $(TEST_DIR)/snapshots/default

TEST_FILES = $(sort $(wildcard test_*.py))

MODULE    ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL   = el2_tmr_recovery_fsm
EXTRA_ARGS = -I$(SRCDIR)/include/

EXTRA_CONFIG_ARGS += -set=mubi_width=2 -set=mubi_false=0x1 -set=mubi_true=0x2 -set=user_mode=1
TMR_ENABLE := 1

VERILOG_SOURCES = \
    $(SRCDIR)/tmr/el2_tmr_3way_fatal_check_mubi.sv \
    $(SRCDIR)/tmr/el2_tmr_recovery_fsm.sv

include $(TEST_DIR)/../common.mk
export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/../tmr_if
