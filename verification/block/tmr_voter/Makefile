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
TOPLEVEL   = el2_tmr_voter_wrapper

COMPILE_ARGS = \
 +define+RV_MUBI_WIDTH=2 \
 +define+RV_MUBI_TRUE=2 \
 +define+RV_MUBI_FALSE=1 \
 +define+RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE=1 \
 -pvalue+Width=8

include $(TEST_DIR)/../common.mk

# Deliberately declare source list here not to include most of the common
# VeeR files. This test is a unit test.
VERILOG_SOURCES = \
    $(CFGDIR)/common_defines.vh \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/lib/beh_lib.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/tmr/el2_tmr_voter.sv \
    $(TEST_DIR)/el2_tmr_voter_wrapper.sv

