null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_ifu_ic_data_wrapper

VERILOG_SOURCES  = \
    $(SRCDIR)/lib/el2_mem_if.sv \
    $(SRCDIR)/ifu/el2_ifu_ic_mem.sv \
    el2_ifu_ic_data_wrapper.sv

export PYTHONPATH := $(PYTHONPATH):$(CURDIR)/../common

include $(CURDIR)/../common.mk
