null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec_wrapper
DEC_TEST    := 1
CM_FILE      = cm.cfg

EXTRA_ARGS = -I$(SRCDIR)/include/

VERILOG_SOURCES  = \
    $(TEST_DIR)/el2_dec_wrapper.sv \
    $(SRCDIR)/dec/el2_dec.sv \
    $(SRCDIR)/dec/el2_dec_decode_ctl.sv \
    $(SRCDIR)/dec/el2_dec_gpr_ctl.sv \
    $(SRCDIR)/dec/el2_dec_ib_ctl.sv \
    $(SRCDIR)/dec/el2_dec_pmp_ctl.sv \
    $(SRCDIR)/dec/el2_dec_tlu_ctl.sv \
    $(SRCDIR)/dec/el2_dec_trigger.sv

include $(TEST_DIR)/../common.mk
