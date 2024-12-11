null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec_trigger_wrapper

VERILOG_SOURCES  = \
    $(TEST_DIR)/el2_dec_trigger_wrapper.sv \
    $(SRCDIR)/dec/el2_dec_trigger.sv

include $(TEST_DIR)/../common.mk
