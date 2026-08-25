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
TOPLEVEL   = el2_ecc_counter_8

TMR_ENABLE := 1

COMPILE_ARGS = $(TEST_DIR)/verilator.vc

VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_secded_13_8_enc.sv \
    $(SRCDIR)/lib/el2_secded_13_8_dec.sv \
    $(SRCDIR)/lib/el2_ecc_counter_8.sv

include $(TEST_DIR)/../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/..
