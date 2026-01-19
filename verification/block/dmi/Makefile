null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = dmi_test_wrapper
CM_FILE      = cm.cfg

VERILOG_SOURCES  = \
    $(TEST_DIR)/dmi_test_wrapper.sv \
    $(SRCDIR)/dmi/rvjtag_tap.sv \
    $(SRCDIR)/dmi/dmi_mux.sv \
    $(SRCDIR)/dmi/dmi_jtag_to_core_sync.sv \
    $(SRCDIR)/dmi/dmi_wrapper.sv

include $(TEST_DIR)/../common.mk

