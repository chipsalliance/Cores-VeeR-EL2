null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_lsu_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/lsu/el2_lsu_wrapper.sv \
    $(SRCDIR)/lsu/el2_lsu.sv \
    $(SRCDIR)/lsu/el2_lsu_dccm_ctl.sv \
    $(SRCDIR)/lsu/el2_lsu_stbuf.sv \
    $(SRCDIR)/lsu/el2_lsu_ecc.sv \
    $(SRCDIR)/lsu/el2_lsu_trigger.sv \
    $(SRCDIR)/lsu/el2_lsu_bus_intf.sv \
    $(SRCDIR)/lsu/el2_lsu_lsc_ctl.sv \
    $(SRCDIR)/lsu/el2_lsu_addrcheck.sv \
    $(SRCDIR)/lsu/el2_lsu_clkdomain.sv \
    $(SRCDIR)/lsu/el2_lsu_bus_buffer.sv

include $(CURDIR)/../common.mk
