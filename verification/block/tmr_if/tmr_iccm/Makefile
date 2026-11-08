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
TOPLEVEL   = tmr_iccm_wrapper

COMPILE_ARGS = \
 -DRV_MUBI_WIDTH=2 \
 -DRV_MUBI_TRUE=2 \
 -DRV_MUBI_FALSE=1 \
 -DRV_TRIPLE_MODULAR_REDUNDANCY_ENABLE=1

VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/lib/el2_mem_if.sv \
    $(SRCDIR)/tmr/el2_tmr_voter.sv \
    $(SRCDIR)/tmr/el2_tmr_mubidff.sv \
    $(SRCDIR)/tmr/el2_tmr_fault_storage.sv \
    $(SRCDIR)/tmr/el2_tmr_iccm.sv \
    tmr_iccm_wrapper.sv

include $(TEST_DIR)/../../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/..
