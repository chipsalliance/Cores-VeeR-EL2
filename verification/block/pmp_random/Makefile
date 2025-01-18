null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_pmp_wrapper
PMP_TEST := 1

VERILOG_SOURCES  = \
    $(TEST_DIR)/el2_pmp_wrapper.sv \
    $(SRCDIR)/el2_pmp.sv

include $(TEST_DIR)/../common.mk
