null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = dmi_wrapper

VERILOG_SOURCES  = \
    $(SRCDIR)/dmi/rvjtag_tap.v \
    $(SRCDIR)/dmi/dmi_jtag_to_core_sync.v \
    $(SRCDIR)/dmi/dmi_wrapper.v

include $(CURDIR)/../common.mk

