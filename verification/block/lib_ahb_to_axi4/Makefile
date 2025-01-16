
null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = ahb_to_axi4_wrapper

VERILOG_SOURCES  = \
    $(SRCDIR)/lib/ahb_to_axi4.sv \
    $(TEST_DIR)/ahb_to_axi4_wrapper.sv

include $(TEST_DIR)/../common.mk
