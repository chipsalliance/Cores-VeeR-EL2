null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_ifu_compress_ctl
CM_FILE      = cm.cfg

VERILOG_SOURCES  = \
    $(SRCDIR)/ifu/el2_ifu_compress_ctl.sv

include $(TEST_DIR)/../common.mk
