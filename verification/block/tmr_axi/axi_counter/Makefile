#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR   := $(abspath $(TEST_DIR)../../../../../design)

TEST_FILES = $(sort $(wildcard test_*.py))

MODULE    ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL   = el2_tmr_axi_counter_wrapper

COMPILE_ARGS = \
 -DRV_MUBI_WIDTH=2 \
 -DRV_MUBI_TRUE=2 \
 -DRV_MUBI_FALSE=1 \
 -DRV_TRIPLE_MODULAR_REDUNDANCY_ENABLE=1 \

include $(TEST_DIR)/../../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/..

# Deliberately declare source list here not to include most of the common
# VeeR files. This test is a unit test.
VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_assert.sv \
    $(SRCDIR)/el2_mubi_pkg.sv \
    $(SRCDIR)/lib/el2_secded_13_8_enc.sv \
    $(SRCDIR)/lib/el2_secded_13_8_dec.sv \
    $(SRCDIR)/lib/el2_ecc_counter_8.sv \
    $(SRCDIR)/tmr/el2_tmr_axi_counter.sv \
    $(TEST_DIR)/el2_tmr_axi_counter_wrapper.sv

