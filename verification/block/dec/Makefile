null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec
DEC_TEST    := 1

EXTRA_ARGS = -I$(SRCDIR)/include/

VERILOG_SOURCES  = \
    $(CURDIR)/dec/el2_dec_wrapper.sv \
    $(SRCDIR)/dec/el2_dec.sv \
    $(SRCDIR)/dec/el2_dec_decode_ctl.sv \
    $(SRCDIR)/dec/el2_dec_gpr_ctl.sv \
    $(SRCDIR)/dec/el2_dec_ib_ctl.sv \
    $(SRCDIR)/dec/el2_dec_pmp_ctl.sv \
    $(SRCDIR)/dec/el2_dec_tlu_ctl.sv \
    $(SRCDIR)/dec/el2_dec_trigger.sv

include $(CURDIR)/../common.mk
