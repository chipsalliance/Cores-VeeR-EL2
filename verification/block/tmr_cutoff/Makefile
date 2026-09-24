null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR   := $(abspath $(TEST_DIR)../../../../design)
CFGDIR   := $(TEST_DIR)/snapshots/default

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_tmr_complex_wrapper

# Override MUBI values to be able to test them in the testbench
EXTRA_VEER_CONFIG = -target=default -set bitmanip_zba -set bitmanip_zbb -set bitmanip_zbc -set bitmanip_zbe -set bitmanip_zbf -set bitmanip_zbp -set bitmanip_zbr -set bitmanip_zbs -set=triple_modular_redundancy_enable=1 -set=mubi_width=2 -set=mubi_true=0x2 -set=mubi_false=0x1 -set build_axi4 -set icache_waypack=0 -set icache_num_ways=2

VERILOG_INCLUDE_DIRS += \
	$(TEST_DIR)/../snapshots/default \
	$(SRCDIR)/include

VERILOG_SOURCES  = \
	$(SRCDIR)/lib/el2_secded_13_8_enc.sv \
	$(SRCDIR)/lib/el2_secded_13_8_dec.sv \
	$(SRCDIR)/lib/el2_ecc_counter_8.sv \
	$(SRCDIR)/tmr/el2_tmr_voter.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_rdy.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_m_ch_ax.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_m_ch_b.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_m_ch_r.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_m_ch_w.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_m.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_s_ch_ax.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_s_ch_b.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_s_ch_r.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_s_ch_w.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_s.sv \
	$(SRCDIR)/tmr/el2_tmr_axi_counter.sv \
	$(SRCDIR)/tmr/el2_tmr_axi.sv \
	$(SRCDIR)/tmr/el2_tmr_ic.sv \
	$(SRCDIR)/tmr/el2_tmr_iccm.sv \
	$(SRCDIR)/tmr/el2_tmr_dccm.sv \
	$(SRCDIR)/tmr/el2_tmr_dmi.sv \
	$(SRCDIR)/tmr/el2_tmr_complex_clk.sv \
	$(SRCDIR)/tmr/el2_tmr_complex_io.sv \
	$(SRCDIR)/tmr/el2_tmr_exec_ctrl.sv \
	$(SRCDIR)/tmr/el2_tmr_misc.sv \
	$(SRCDIR)/tmr/el2_tmr_pic.sv \
	$(SRCDIR)/tmr/el2_tmr_3way_fatal_check_mubi.sv \
	$(SRCDIR)/tmr/el2_tmr_recovery_fsm.sv \
	$(SRCDIR)/el2_tmr_complex.sv \
	$(SRCDIR)/el2_mem.sv \
	$(SRCDIR)/el2_pic_ctrl.sv \
	$(SRCDIR)/el2_veer.sv \
	$(SRCDIR)/el2_dma_ctrl.sv \
	$(SRCDIR)/el2_pmp.sv \
	$(SRCDIR)/ifu/el2_ifu_aln_ctl.sv \
	$(SRCDIR)/ifu/el2_ifu_compress_ctl.sv \
	$(SRCDIR)/ifu/el2_ifu_ifc_ctl.sv \
	$(SRCDIR)/ifu/el2_ifu_bp_ctl.sv \
	$(SRCDIR)/ifu/el2_ifu_ic_mem.sv \
	$(SRCDIR)/ifu/el2_ifu_mem_ctl.sv \
	$(SRCDIR)/ifu/el2_ifu_iccm_mem.sv \
	$(SRCDIR)/ifu/el2_ifu.sv \
	$(SRCDIR)/dec/el2_dec_decode_ctl.sv \
	$(SRCDIR)/dec/el2_dec_gpr_ctl.sv \
	$(SRCDIR)/dec/el2_dec_ib_ctl.sv \
	$(SRCDIR)/dec/el2_dec_pmp_ctl.sv \
	$(SRCDIR)/dec/el2_dec_tlu_ctl.sv \
	$(SRCDIR)/dec/el2_dec_trigger.sv \
	$(SRCDIR)/dec/el2_dec.sv \
	$(SRCDIR)/exu/el2_exu_alu_ctl.sv \
	$(SRCDIR)/exu/el2_exu_mul_ctl.sv \
	$(SRCDIR)/exu/el2_exu_div_ctl.sv \
	$(SRCDIR)/exu/el2_exu.sv \
	$(SRCDIR)/lsu/el2_lsu.sv \
	$(SRCDIR)/lsu/el2_lsu_clkdomain.sv \
	$(SRCDIR)/lsu/el2_lsu_addrcheck.sv \
	$(SRCDIR)/lsu/el2_lsu_lsc_ctl.sv \
	$(SRCDIR)/lsu/el2_lsu_stbuf.sv \
	$(SRCDIR)/lsu/el2_lsu_bus_buffer.sv \
	$(SRCDIR)/lsu/el2_lsu_bus_intf.sv \
	$(SRCDIR)/lsu/el2_lsu_ecc.sv \
	$(SRCDIR)/lsu/el2_lsu_dccm_mem.sv \
	$(SRCDIR)/lsu/el2_lsu_dccm_ctl.sv \
	$(SRCDIR)/lsu/el2_lsu_trigger.sv \
	$(SRCDIR)/dbg/el2_dbg.sv \
	$(SRCDIR)/dmi/dmi_mux.v \
	$(SRCDIR)/dmi/dmi_wrapper.v \
	$(SRCDIR)/dmi/dmi_jtag_to_core_sync.v \
	$(SRCDIR)/dmi/rvjtag_tap.v \
	$(SRCDIR)/lib/el2_lib.sv \
	$(SRCDIR)/lib/el2_mem_if.sv \
	$(SRCDIR)/lib/el2_prim_generic_buf.sv \
	$(SRCDIR)/lib/el2_prim_buf.sv \
	$(TEST_DIR)/el2_tmr_complex_wrapper.sv

include $(TEST_DIR)/../common.mk

COMPILE_ARGS += -Wno-SIMILARNAME
