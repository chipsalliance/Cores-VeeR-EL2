
null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = ahb_to_axi4

VERILOG_SOURCES  = \
    $(SRCDIR)/lib/ahb_to_axi4.sv

include $(CURDIR)/../common.mk
