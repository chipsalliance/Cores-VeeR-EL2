null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec_tlu_ctl_wrapper

EXTRA_ARGS = -I$(SRCDIR)/include/

VERILOG_SOURCES  = \
    $(SRCDIR)/dec/el2_dec_pmp_ctl.sv \
    $(SRCDIR)/dec/el2_dec_tlu_ctl.sv \
    $(CURDIR)/dec_tlu_ctl/el2_tlu_ctl_wrapper.sv

include $(CURDIR)/../common.mk
