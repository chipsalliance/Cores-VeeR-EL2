null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_veer_lockstep_wrapper

EXTRA_VEER_CONFIG = -set lockstep_enable=1 -set lockstep_regfile_enable=1

VERILOG_INCLUDE_DIRS += \
	${RV_ROOT}/testbench \
	${RV_ROOT}/design/include

VERILOG_SOURCES  = \
	${SRCDIR}/lib/el2_mem_if.sv \
	${SRCDIR}/lib/el2_regfile_if.sv \
	${SRCDIR}/el2_veer_wrapper.sv \
	${SRCDIR}/el2_mem.sv \
	${SRCDIR}/el2_pic_ctrl.sv \
	${SRCDIR}/el2_veer.sv \
	${SRCDIR}/el2_dma_ctrl.sv \
	${SRCDIR}/el2_pmp.sv \
	${SRCDIR}/ifu/el2_ifu_aln_ctl.sv \
	${SRCDIR}/ifu/el2_ifu_compress_ctl.sv \
	${SRCDIR}/ifu/el2_ifu_ifc_ctl.sv \
	${SRCDIR}/ifu/el2_ifu_bp_ctl.sv \
	${SRCDIR}/ifu/el2_ifu_ic_mem.sv \
	${SRCDIR}/ifu/el2_ifu_mem_ctl.sv \
	${SRCDIR}/ifu/el2_ifu_iccm_mem.sv \
	${SRCDIR}/ifu/el2_ifu.sv \
	${SRCDIR}/dec/el2_dec_decode_ctl.sv \
	${SRCDIR}/dec/el2_dec_gpr_ctl.sv \
	${SRCDIR}/dec/el2_dec_ib_ctl.sv \
	${SRCDIR}/dec/el2_dec_pmp_ctl.sv \
	${SRCDIR}/dec/el2_dec_tlu_ctl.sv \
	${SRCDIR}/dec/el2_dec_trigger.sv \
	${SRCDIR}/dec/el2_dec.sv \
	${SRCDIR}/exu/el2_exu_alu_ctl.sv \
	${SRCDIR}/exu/el2_exu_mul_ctl.sv \
	${SRCDIR}/exu/el2_exu_div_ctl.sv \
	${SRCDIR}/exu/el2_exu.sv \
	${SRCDIR}/lsu/el2_lsu.sv \
	${SRCDIR}/lsu/el2_lsu_clkdomain.sv \
	${SRCDIR}/lsu/el2_lsu_addrcheck.sv \
	${SRCDIR}/lsu/el2_lsu_lsc_ctl.sv \
	${SRCDIR}/lsu/el2_lsu_stbuf.sv \
	${SRCDIR}/lsu/el2_lsu_bus_buffer.sv \
	${SRCDIR}/lsu/el2_lsu_bus_intf.sv \
	${SRCDIR}/lsu/el2_lsu_ecc.sv \
	${SRCDIR}/lsu/el2_lsu_dccm_mem.sv \
	${SRCDIR}/lsu/el2_lsu_dccm_ctl.sv \
	${SRCDIR}/lsu/el2_lsu_trigger.sv \
	${SRCDIR}/dbg/el2_dbg.sv \
	${SRCDIR}/dmi/dmi_mux.v \
	${SRCDIR}/dmi/dmi_wrapper.v \
	${SRCDIR}/dmi/dmi_jtag_to_core_sync.v \
	${SRCDIR}/dmi/rvjtag_tap.v \
	${SRCDIR}/lib/el2_lib.sv \
	$(SRCDIR)/el2_veer_lockstep.sv \
	$(CURDIR)/dcls/el2_veer_lockstep_wrapper.sv

include $(CURDIR)/../common.mk
