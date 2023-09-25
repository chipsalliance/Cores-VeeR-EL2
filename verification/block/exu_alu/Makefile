
null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_exu_alu_ctl_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/exu_alu/el2_exu_alu_ctl_wrapper.sv \
    $(SRCDIR)/exu/el2_exu_alu_ctl.sv

include $(CURDIR)/../common.mk
