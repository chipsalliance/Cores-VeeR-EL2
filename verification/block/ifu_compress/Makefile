null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_ifu_compress_ctl

VERILOG_SOURCES  = \
    $(SRCDIR)/ifu/el2_ifu_compress_ctl.sv

include $(CURDIR)/../common.mk
