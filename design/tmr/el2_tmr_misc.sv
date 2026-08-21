// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_misc
  import el2_pkg::*;
  import el2_mubi_pkg::*;
(
    input  logic clk,
    input  logic rst_l,

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

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t misc_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t misc_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t misc_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t fault_trace_rv_i_insn_ip_veer[3];
  el2_mubi_t fault_trace_rv_i_address_ip_veer[3];
  el2_mubi_t fault_trace_rv_i_valid_ip_veer[3];
  el2_mubi_t fault_trace_rv_i_exc_int_ip_veer[3];
  el2_mubi_t fault_trace_rv_i_ecause_ip_veer[3];
  el2_mubi_t fault_trace_rv_i_tval_ip_veer[3];

  el2_mubi_t fault_dec_tlu_perfcnt_veer[3];
  el2_mubi_t fault_dec_tlu_force_halt_veer[3];

  // ......................................................

  el2_mubi_t crit_trace_rv_i_insn_ip_veer;
  el2_mubi_t crit_trace_rv_i_address_ip_veer;
  el2_mubi_t crit_trace_rv_i_valid_ip_veer;
  el2_mubi_t crit_trace_rv_i_exc_int_ip_veer;
  el2_mubi_t crit_trace_rv_i_ecause_ip_veer;
  el2_mubi_t crit_trace_rv_i_tval_ip_veer;

  el2_mubi_t crit_dec_tlu_perfcnt_veer_nc;
  el2_mubi_t crit_dec_tlu_force_halt_veer_nc;

  el2_mubi_t crit_any;

  // ......................................................

  // Pass reset through only a single voter
  rvtmr #(.WIDTH(1)) u_core_rst_l (
    .I (core_rst_l_veer),
    .O (core_rst_l)
  );

  // ......................................................

  logic [1:0] trace_rv_i_exc_int_ip_veer[3];
  logic [1:0] trace_rv_i_exc_int_ip;

  for (genvar i=0; i<3; i=i+1) begin
    assign trace_rv_i_exc_int_ip_veer[i] = {trace_rv_i_exception_ip_veer[i], trace_rv_i_interrupt_ip_veer[i]};
  end

  assign trace_rv_i_exception_ip = trace_rv_i_exc_int_ip[1] & mubi_check_false(crit_any);
  assign trace_rv_i_interrupt_ip = trace_rv_i_exc_int_ip[0] & mubi_check_false(crit_any);

  el2_tmr_voter #(.Width(2)) u_voter_trace_rv_i_exc_int_ip (
    .in_a     (trace_rv_i_exc_int_ip_veer[0]),
    .in_b     (trace_rv_i_exc_int_ip_veer[1]),
    .in_c     (trace_rv_i_exc_int_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_exc_int_ip),

    .fault_a  (fault_trace_rv_i_exc_int_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_exc_int_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_exc_int_ip_veer[2]),

    .critical (crit_trace_rv_i_exc_int_ip_veer)
  );

  logic  trace_rv_i_valid_ip_int;
  assign trace_rv_i_valid_ip = trace_rv_i_valid_ip_int & mubi_check_false(crit_any);

  el2_tmr_voter #(.Width(1)) u_voter_trace_rv_i_valid_ip (
    .in_a     (trace_rv_i_valid_ip_veer[0]),
    .in_b     (trace_rv_i_valid_ip_veer[1]),
    .in_c     (trace_rv_i_valid_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_valid_ip_int),

    .fault_a  (fault_trace_rv_i_valid_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_valid_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_valid_ip_veer[2]),

    .critical (crit_trace_rv_i_valid_ip_veer)
  );

  el2_tmr_voter #(.Width($bits(trace_rv_i_insn_ip))) u_voter_trace_rv_i_insn_ip (
    .in_a     (trace_rv_i_insn_ip_veer[0]),
    .in_b     (trace_rv_i_insn_ip_veer[1]),
    .in_c     (trace_rv_i_insn_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_insn_ip),

    .fault_a  (fault_trace_rv_i_insn_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_insn_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_insn_ip_veer[2]),

    .critical (crit_trace_rv_i_insn_ip_veer)
  );

  el2_tmr_voter #(.Width($bits(trace_rv_i_address_ip))) u_voter_trace_rv_i_address_ip (
    .in_a     (trace_rv_i_address_ip_veer[0]),
    .in_b     (trace_rv_i_address_ip_veer[1]),
    .in_c     (trace_rv_i_address_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_address_ip),

    .fault_a  (fault_trace_rv_i_address_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_address_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_address_ip_veer[2]),

    .critical (crit_trace_rv_i_address_ip_veer)
  );

  el2_tmr_voter #(.Width($bits(trace_rv_i_ecause_ip))) u_voter_trace_rv_i_ecause_ip (
    .in_a     (trace_rv_i_ecause_ip_veer[0]),
    .in_b     (trace_rv_i_ecause_ip_veer[1]),
    .in_c     (trace_rv_i_ecause_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_ecause_ip),

    .fault_a  (fault_trace_rv_i_ecause_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_ecause_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_ecause_ip_veer[2]),

    .critical (crit_trace_rv_i_ecause_ip_veer)
  );

  el2_tmr_voter #(.Width($bits(trace_rv_i_tval_ip))) u_voter_trace_rv_i_tval_ip (
    .in_a     (trace_rv_i_tval_ip_veer[0]),
    .in_b     (trace_rv_i_tval_ip_veer[1]),
    .in_c     (trace_rv_i_tval_ip_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (trace_rv_i_tval_ip),

    .fault_a  (fault_trace_rv_i_tval_ip_veer[0]),
    .fault_b  (fault_trace_rv_i_tval_ip_veer[1]),
    .fault_c  (fault_trace_rv_i_tval_ip_veer[2]),

    .critical (crit_trace_rv_i_tval_ip_veer)
  );

  // Aggregate critical failure signals for the trace interface
  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;
  el2_mubi_t crit_l2;

  assign crit_l0 = mubi_or(crit_trace_rv_i_insn_ip_veer,   crit_trace_rv_i_address_ip_veer);
  assign crit_l1 = mubi_or(crit_trace_rv_i_valid_ip_veer,  crit_trace_rv_i_exc_int_ip_veer);
  assign crit_l2 = mubi_or(crit_trace_rv_i_ecause_ip_veer, crit_trace_rv_i_tval_ip_veer);

  assign crit_any = mubi_or3(crit_l0, crit_l1, crit_l2);

  // ......................................................

  logic [3:0] dec_tlu_perfcnt_veer[3];
  logic [3:0] dec_tlu_perfcnt;

  for (genvar i=0; i<3; i=i+1) begin
    assign dec_tlu_perfcnt_veer[i] = {
      dec_tlu_perfcnt3_veer[i],
      dec_tlu_perfcnt2_veer[i],
      dec_tlu_perfcnt1_veer[i],
      dec_tlu_perfcnt0_veer[i]
    };
  end

  assign dec_tlu_perfcnt0 = dec_tlu_perfcnt[0];
  assign dec_tlu_perfcnt1 = dec_tlu_perfcnt[1];
  assign dec_tlu_perfcnt2 = dec_tlu_perfcnt[2];
  assign dec_tlu_perfcnt3 = dec_tlu_perfcnt[3];

  el2_tmr_voter #(.Width($bits(dec_tlu_perfcnt))) u_voter_dec_tlu_perfcnt (
    .in_a     (dec_tlu_perfcnt_veer[0]),
    .in_b     (dec_tlu_perfcnt_veer[1]),
    .in_c     (dec_tlu_perfcnt_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dec_tlu_perfcnt),

    .fault_a  (fault_dec_tlu_perfcnt_veer[0]),
    .fault_b  (fault_dec_tlu_perfcnt_veer[1]),
    .fault_c  (fault_dec_tlu_perfcnt_veer[2]),

    .critical (crit_dec_tlu_perfcnt_veer_nc)
  );

  el2_tmr_voter #(.Width($bits(dec_tlu_force_halt_int))) u_voter_dec_tlu_force_halt (
    .in_a     (dec_tlu_force_halt_veer[0]),
    .in_b     (dec_tlu_force_halt_veer[1]),
    .in_c     (dec_tlu_force_halt_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dec_tlu_force_halt_int),

    .fault_a  (fault_dec_tlu_force_halt_veer[0]),
    .fault_b  (fault_dec_tlu_force_halt_veer[1]),
    .fault_c  (fault_dec_tlu_force_halt_veer[2]),

    .critical (crit_dec_tlu_force_halt_veer_nc)
  );

  // ......................................................

  // Fault aggregation and registers
  for (genvar i=0; i<3; i=i+1) begin : fault
    el2_mubi_t  fault_l00;
    el2_mubi_t  fault_l01;
    el2_mubi_t  fault_l02;
    el2_mubi_t  fault_l03;
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l00 = mubi_or(fault_trace_rv_i_insn_ip_veer[i],   fault_trace_rv_i_address_ip_veer[i]);
    assign fault_l01 = mubi_or(fault_trace_rv_i_valid_ip_veer[i],  fault_trace_rv_i_exc_int_ip_veer[i]);
    assign fault_l02 = mubi_or(fault_trace_rv_i_ecause_ip_veer[i], fault_trace_rv_i_tval_ip_veer[i]);
    assign fault_l03 = mubi_or(fault_dec_tlu_perfcnt_veer[i],      fault_dec_tlu_force_halt_veer[i]);

    assign fault_l0  = mubi_or(fault_l00, fault_l01);
    assign fault_l1  = mubi_or(fault_l02, fault_l03);

    assign fault_any = mubi_or3(fault_l0, fault_l1, misc_fault_d[i]);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        misc_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(misc_fault_clr[i])) begin
          misc_fault_q[i] <= El2MuBiFalse;
        end else begin
          misc_fault_q[i] <= mubi_or(misc_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(misc_fault_q[i]);

  end

  // ......................................................

  // Propagate response to Cores
  for (genvar i=0; i < 3; i+=1) begin
    assign rst_vec_veer[i]   = rst_vec;
    assign nmi_int_veer[i]   = nmi_int;
    assign nmi_vec_veer[i]   = nmi_vec;

    assign timer_int_veer[i] = timer_int;
    assign soft_int_veer[i]  = soft_int;
  end

endmodule
`endif
