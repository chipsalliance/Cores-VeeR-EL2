null  :=
space := $(null)
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = dmi_test_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/dmi/dmi_test_wrapper.sv \
    $(SRCDIR)/dmi/rvjtag_tap.v \
    $(SRCDIR)/dmi/dmi_mux.v \
    $(SRCDIR)/dmi/dmi_jtag_to_core_sync.v \
    $(SRCDIR)/dmi/dmi_wrapper.v

include $(CURDIR)/../common.mk

