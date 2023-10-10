null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_pmp_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/pmp/el2_pmp_wrapper.sv \
    $(SRCDIR)/el2_pmp.sv

include $(CURDIR)/../common.mk
