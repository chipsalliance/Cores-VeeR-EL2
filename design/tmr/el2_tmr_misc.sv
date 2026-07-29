// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_misc
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // Reset and interrupts
    input  logic [31:1] rst_vec,
    input  logic        nmi_int,
    input  logic [31:1] nmi_vec,
    input  logic        timer_int,
    input  logic        soft_int,
    // Trace
    output logic [31:0] trace_rv_i_insn_ip,
    output logic [31:0] trace_rv_i_address_ip,
    output logic        trace_rv_i_valid_ip,
    output logic        trace_rv_i_exception_ip,
    output logic [4:0]  trace_rv_i_ecause_ip,
    output logic        trace_rv_i_interrupt_ip,
    output logic [31:0] trace_rv_i_tval_ip,

    // Perf
    output logic dec_tlu_perfcnt0,
    output logic dec_tlu_perfcnt1,
    output logic dec_tlu_perfcnt2,
    output logic dec_tlu_perfcnt3,

    output logic core_rst_l,
    output logic dec_tlu_force_halt_int,
    output logic dec_tlu_core_ecc_disable,

    // TMR
    // Reset and interrupts
    output logic [31:1] rst_vec_veer[3],
    output logic        nmi_int_veer[3],
    output logic [31:1] nmi_vec_veer[3],
    output logic        timer_int_veer[3],
    output logic        soft_int_veer[3],
    // Trace
    input  logic [31:0] trace_rv_i_insn_ip_veer[3],
    input  logic [31:0] trace_rv_i_address_ip_veer[3],
    input  logic        trace_rv_i_valid_ip_veer[3],
    input  logic        trace_rv_i_exception_ip_veer[3],
    input  logic [4:0]  trace_rv_i_ecause_ip_veer[3],
    input  logic        trace_rv_i_interrupt_ip_veer[3],
    input  logic [31:0] trace_rv_i_tval_ip_veer[3],

    // Perf
    input  logic dec_tlu_perfcnt0_veer[3],
    input  logic dec_tlu_perfcnt1_veer[3],
    input  logic dec_tlu_perfcnt2_veer[3],
    input  logic dec_tlu_perfcnt3_veer[3],

    input  logic core_rst_l_veer[3],
    input  logic dec_tlu_force_halt_veer[3],
    input  logic dec_tlu_core_ecc_disable_veer[3]
);

//TODO: Change it to use voters
  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      rst_vec_veer[i] = rst_vec;
      nmi_int_veer[i] = nmi_int;
      nmi_vec_veer[i] = nmi_vec;

      timer_int_veer[i] = timer_int;
      soft_int_veer[i] = soft_int;
    end
    // Get value from Core 0 for the time being
    trace_rv_i_insn_ip = trace_rv_i_insn_ip_veer[0];
    trace_rv_i_address_ip = trace_rv_i_address_ip_veer[0];
    trace_rv_i_valid_ip = trace_rv_i_valid_ip_veer[0];
    trace_rv_i_exception_ip = trace_rv_i_exception_ip_veer[0];
    trace_rv_i_ecause_ip = trace_rv_i_ecause_ip_veer[0];
    trace_rv_i_interrupt_ip = trace_rv_i_interrupt_ip_veer[0];
    trace_rv_i_tval_ip = trace_rv_i_tval_ip_veer[0];
    core_rst_l = core_rst_l_veer[0];
    dec_tlu_perfcnt0 = dec_tlu_perfcnt0_veer[0];
    dec_tlu_perfcnt1 = dec_tlu_perfcnt1_veer[0];
    dec_tlu_perfcnt2 = dec_tlu_perfcnt2_veer[0];
    dec_tlu_perfcnt3 = dec_tlu_perfcnt3_veer[0];
    dec_tlu_force_halt_int = dec_tlu_force_halt_veer[0];
    dec_tlu_core_ecc_disable = dec_tlu_core_ecc_disable_veer[0];
  end
endmodule
`endif
