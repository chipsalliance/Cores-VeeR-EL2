null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec_ib_ctl_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/dec_ib/el2_dec_ib_ctl_wrapper.sv \
    $(SRCDIR)/dec/el2_dec_ib_ctl.sv

include $(CURDIR)/../common.mk
