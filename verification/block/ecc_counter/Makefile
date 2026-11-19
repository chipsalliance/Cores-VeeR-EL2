#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES = $(sort $(wildcard test_*.py))

MODULE    ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL   = ecc_counter_wrapper

VERILOG_SOURCES = \
    $(SRCDIR)/lib/el2_secded_13_8_enc.sv \
    $(SRCDIR)/lib/el2_secded_13_8_dec.sv \
    $(SRCDIR)/lib/el2_ecc_counter_8.sv \
    $(TEST_DIR)/ecc_counter_wrapper.sv

include $(TEST_DIR)/../common.mk

export PYTHONPATH := $(PYTHONPATH):$(TEST_DIR)/..
