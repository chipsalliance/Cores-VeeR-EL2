#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR   := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES = $(sort $(wildcard test_*.py))

MODULE    ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL   = el2_tmr_recovery_fsm
EXTRA_ARGS = -I$(SRCDIR)/include/

COMPILE_ARGS = \
 -DRV_MUBI_WIDTH=2 \
 -DRV_MUBI_TRUE=2 \
 -DRV_MUBI_FALSE=1 \
 -DRV_TRIPLE_MODULAR_REDUNDANCY_ENABLE=1 \
 -DRV_USER_MODE=1

VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/tmr/el2_tmr_3way_fatal_check_mubi.sv \
    $(SRCDIR)/tmr/el2_tmr_recovery_fsm.sv

include $(TEST_DIR)/../common.mk
export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/../tmr_if
