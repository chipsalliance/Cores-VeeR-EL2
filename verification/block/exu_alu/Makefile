
null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_exu_alu_ctl_wrapper

VERILOG_SOURCES  = \
    $(TEST_DIR)/el2_exu_alu_ctl_wrapper.sv \
    $(SRCDIR)/exu/el2_exu_alu_ctl.sv

include $(TEST_DIR)/../common.mk
