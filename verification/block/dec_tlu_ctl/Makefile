null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_dec_tlu_ctl_wrapper
CM_FILE      = cm.cfg

EXTRA_ARGS = -I$(SRCDIR)/include/

VERILOG_SOURCES  = \
    $(SRCDIR)/dec/el2_dec_pmp_ctl.sv \
    $(SRCDIR)/dec/el2_dec_tlu_ctl.sv \
    $(TEST_DIR)/el2_tlu_ctl_wrapper.sv

include $(TEST_DIR)/../common.mk
