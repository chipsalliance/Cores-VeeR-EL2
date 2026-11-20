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
TOPLEVEL   = el2_tmr_axi_m

COMPILE_ARGS = \
 +define+RV_MUBI_WIDTH=2 \
 +define+RV_MUBI_TRUE=2 \
 +define+RV_MUBI_FALSE=1 \
 +define+RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE=1 \
 -pvalue+AddrWidth=32 \
 -pvalue+DataWidth=64 \
 -pvalue+IdWidth=4 \

include $(TEST_DIR)/../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/../tmr_common

# Deliberately declare source list here not to include most of the common
# VeeR files. This test is a unit test.
VERILOG_SOURCES = \
    $(CFGDIR)/common_defines.vh \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/lib/beh_lib.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/tmr/el2_tmr_voter.sv \
    $(SRCDIR)/tmr/el2_tmr_mubidff.sv \
    $(SRCDIR)/tmr/el2_tmr_fault_storage.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_rdy.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_m_ch_ax.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_m_ch_b.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_m_ch_r.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_m_ch_w.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_m.sv

