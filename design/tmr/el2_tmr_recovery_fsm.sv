// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE

typedef enum logic [8:0] {
  IDLE                          = 9'b110000110,
  HALT_CORES                    = 9'b001100011,
  READ_REG                      = 9'b011001111,
  SET_FLAG_RD                   = 9'b100111111,
  RESET_CPU                     = 9'b010101100,
  SET_FLAG_CC                   = 9'b101010001,
  WRITE_REG                     = 9'b001010110,
  SET_FLAG_SR                   = 9'b010010011,
  RESTART_CPU                   = 9'b100100000,
  SET_FLAG_CR                   = 9'b011110101,
  CLEAR_FLAG_ERR                = 9'b000001010,
  CLEAR_FLAG_RD                 = 9'b001111000,
  CLEAR_FLAG_CC                 = 9'b111110010,
  CLEAR_FLAG_SR                 = 9'b101001100,
  CLEAR_FLAG_CR                 = 9'b000000101
} recovery_state_t;

module el2_tmr_recovery_fsm
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic clk,
    input  logic rst_l,
    input  el2_mubi_pkg::el2_mubi_t external_flag,
    output el2_mubi_pkg::el2_mubi_t clear_external_flag,

    output el2_mubi_pkg::el2_mubi_t recovery_gpr_en_veer[3],
    output logic                    recovery_gpr_wen_veer[3],
    output logic [ 4:0]             recovery_gpr_wraddr_veer[3],
    output logic [31:0]             recovery_gpr_wrdata_veer[3],
    output logic [ 4:0]             recovery_gpr_rdaddr_veer[3],
    input  logic [31:0]             recovery_gpr_rddata_veer[3],

    output el2_mubi_pkg::el2_mubi_t recovery_csr_en_veer[3],
    output logic                    recovery_csr_wen_veer[3],
    output logic [11:0]             recovery_csr_wraddr_veer[3],
    output logic [31:0]             recovery_csr_wrdata_veer[3],
    output logic [11:0]             recovery_csr_rdaddr_veer[3],
    input  logic [31:0]             recovery_csr_rddata_veer[3],

    output logic sync_rst_l,

    // VeeR exec ctrl
    output logic i_cpu_halt_req_veer[3],
    output logic i_cpu_run_req_veer[3],
    input  logic o_cpu_halt_ack_veer[3],
    input  logic o_cpu_halt_status_veer[3],
    input  logic o_cpu_run_ack_veer[3],
    output logic mpc_reset_run_req_veer[3],

    // External exec ctrl
    input  logic ext_i_cpu_halt_req_veer[3],
    input  logic ext_i_cpu_run_req_veer[3],
    output logic ext_o_cpu_halt_ack_veer[3],
    output logic ext_o_cpu_halt_status_veer[3],
    output logic ext_o_cpu_run_ack_veer[3],
    input  logic ext_mpc_reset_run_req_veer[3],

    // Error flags
    output el2_mubi_pkg::el2_mubi_t fatal_err,

    input  logic scan_mode
);

`ifdef RV_USER_MODE
  localparam int csr_cnt = 163;
`else
  localparam int csr_cnt = 146;
`endif

  logic recovery_state_en;
  recovery_state_t recovery_nxstate, recovery_state;

  rvdffiee #(9) fsm_state_ff (.*, .din(recovery_nxstate), .dout(recovery_state), .en(recovery_state_en));

  // Exec control

  logic int_i_cpu_halt_req_veer;
  logic int_i_cpu_run_req_veer;
  logic int_o_cpu_halt_ack_veer, int_o_cpu_halt_ack_veer_d;
  logic int_o_cpu_halt_status_veer, int_o_cpu_halt_status_veer_d;
  logic int_o_cpu_run_ack_veer, int_o_cpu_run_ack_veer_d;

  for (genvar i=0; i < 3; ++i) begin : mux_exec_ctrl_signals
    assign i_cpu_halt_req_veer[i] = recovery_state == IDLE | recovery_state == '0 ? ext_i_cpu_halt_req_veer[i] : int_i_cpu_halt_req_veer;
    assign i_cpu_run_req_veer[i] = recovery_state == IDLE | recovery_state == '0 ? ext_i_cpu_run_req_veer[i] : int_i_cpu_run_req_veer;
    assign mpc_reset_run_req_veer[i] = recovery_state == IDLE | recovery_state == '0 ? ext_mpc_reset_run_req_veer[i] : 'b0;
    assign ext_o_cpu_halt_ack_veer[i] = o_cpu_halt_ack_veer[i];
    assign ext_o_cpu_halt_status_veer[i] = o_cpu_halt_status_veer[i];
    assign ext_o_cpu_run_ack_veer[i] = o_cpu_run_ack_veer[i];
  end
  assign sync_rst_l = recovery_state == RESET_CPU;
  assign int_i_cpu_halt_req_veer = recovery_state == HALT_CORES;
  assign int_i_cpu_run_req_veer = recovery_state == RESTART_CPU;
  rvtmr #(1) halt_ack_tmr_m (.I(o_cpu_halt_ack_veer), .O(int_o_cpu_halt_ack_veer));
  rvtmr #(1) run_ack_tmr_m (.I(o_cpu_run_ack_veer), .O(int_o_cpu_run_ack_veer));
  rvtmr #(1) halt_status_tmr_m (.I(o_cpu_halt_status_veer), .O(int_o_cpu_halt_status_veer));
  rvdff #(.WIDTH(3)) cpu_exec_status_d (.*,
    .din({int_o_cpu_halt_ack_veer, int_o_cpu_run_ack_veer, int_o_cpu_halt_status_veer}),
    .dout({int_o_cpu_halt_ack_veer_d, int_o_cpu_run_ack_veer_d, int_o_cpu_halt_status_veer_d})
  );

  // GPR and CSR counters
  logic [7:0] cnt_csr [3], cnt_nxtcsr [3];
  logic [5:0] cnt_gpr [3], cnt_nxtgpr [3];
  logic cnt_csr_clr[3], cnt_gpr_clr[3];
  logic cnt_csr_inc[3], cnt_gpr_inc[3];

  for (genvar i=0; i<3; ++i) begin : csr_address_counters
    logic [7:0] cnt_csr_int;
    rvdffsc #(8) cnt_csr_ff (.*, .din(cnt_nxtcsr[i]), .dout(cnt_csr[i]), .clear(cnt_csr_clr[i]), .en(1'b1));
    rvtmr #(8) cnt_csr_tmr (.I(cnt_csr), .O(cnt_csr_int));
    assign cnt_nxtcsr[i] = cnt_csr_inc[i] ? 8'(cnt_csr_int + 8'h1) : cnt_csr_int;
    assign cnt_csr_clr[i] = (recovery_nxstate != recovery_state) & recovery_state_en;
  end

  for (genvar i=0; i<3; ++i) begin : gpr_address_counters
    logic [5:0] cnt_gpr_int;
    rvdffsc #(6) cnt_gpr_ff (.*, .din(cnt_nxtgpr[i]), .dout(cnt_gpr[i]), .clear(cnt_gpr_clr[i]), .en(1'b1));
    rvtmr #(6) cnt_gpr_tmr (.I(cnt_gpr), .O(cnt_gpr_int));
    assign cnt_nxtgpr[i] = 6'(cnt_gpr_int + 6'h1);
    assign cnt_gpr_clr[i] = (recovery_nxstate != recovery_state) & recovery_state_en;
  end

  // GPR and CSR access
  logic [31:0] csr_wrdata;
  logic [31:0] gpr_wrdata;

  for (genvar i=0; i < 3; ++i) begin : drive_csr_access_signals
    logic [11:0] csr_addr;
    el2_tmr_csr_addr_decode csr_cnt_to_csr_addr(.counter(cnt_csr[i]), .csr_addr(csr_addr));
    assign recovery_csr_en_veer[i] =
      (recovery_state == READ_REG) | (recovery_state == WRITE_REG) ? El2MuBiTrue : El2MuBiFalse;
    assign recovery_csr_wen_veer[i] = recovery_state == WRITE_REG ? 1'b1 : 1'b0;
    assign recovery_csr_wraddr_veer[i] = csr_addr;
    assign recovery_csr_wrdata_veer[i] = recovery_state == WRITE_REG ? csr_wrdata : 32'b0;
    assign recovery_csr_rdaddr_veer[i] = csr_addr;
  end

  for (genvar i=0; i < 3; ++i) begin : drive_gpr_access_signals
    assign recovery_gpr_en_veer[i] =
      (recovery_state == READ_REG) | (recovery_state == WRITE_REG) ? El2MuBiTrue : El2MuBiFalse;
    assign recovery_gpr_wen_veer[i] = recovery_state == WRITE_REG ? 1'b1 : 1'b0;
    assign recovery_gpr_wraddr_veer[i] = cnt_gpr[i][4:0];
    assign recovery_gpr_wrdata_veer[i] = recovery_state == WRITE_REG ? gpr_wrdata : 32'b0;
    assign recovery_gpr_rdaddr_veer[i] = cnt_gpr[i][4:0];
  end


  // GPR and CSR delayed value

  el2_mubi_t gpr_ready[3], csr_ready[3];
  el2_mubi_t all_gpr_ready, all_csr_ready;
  logic [31:0] recovery_gpr_rddata_veer_d[3];
  logic [31:0] recovery_csr_rddata_veer_d[3];
  for (genvar i=0; i < 3; ++i) begin : register_read_check
    rvdff #(.WIDTH(32)) csr_value_d_m (.*, .din(recovery_csr_rddata_veer[i]), .dout(recovery_csr_rddata_veer_d[i]));
    assign csr_ready[i] = el2_mubi_reg_comp(recovery_csr_rddata_veer[i], recovery_csr_rddata_veer_d[i]);
    rvdff #(.WIDTH(32)) gpr_value_d_m (.*, .din(recovery_gpr_rddata_veer[i]), .dout(recovery_gpr_rddata_veer_d[i]));
    assign gpr_ready[i] = el2_mubi_reg_comp(recovery_gpr_rddata_veer[i], recovery_gpr_rddata_veer_d[i]);
  end
  assign all_csr_ready = mubi_and3(csr_ready[0], csr_ready[1], csr_ready[2]);
  assign all_gpr_ready = mubi_and3(gpr_ready[0], gpr_ready[1], gpr_ready[2]);

  el2_mubi_t csr_fatal, gpr_fatal;
  el2_tmr_3way_fatal_check_mubi #(.Width(32)) verify_csr(.in(recovery_csr_rddata_veer_d), .fatal(csr_fatal));
  el2_tmr_3way_fatal_check_mubi #(.Width(32)) verify_gpr(.in(recovery_gpr_rddata_veer_d), .fatal(gpr_fatal));

  el2_mubi_t csr_ready_and_fatal, gpr_ready_and_fatal;
  assign csr_ready_and_fatal = el2_mubi_mux_el2_mubi_true(
    .sel(all_csr_ready), .match(csr_fatal), .mismatch(El2MuBiFalse));
  assign gpr_ready_and_fatal = el2_mubi_mux_el2_mubi_true(
    .sel(all_gpr_ready), .match(gpr_fatal), .mismatch(El2MuBiFalse));

  assign fatal_err = mubi_or(.a(csr_ready_and_fatal), .b(gpr_ready_and_fatal));

  // GPR and CSR storage

  logic [38:0] csr_recovery_storage [csr_cnt];
  logic [38:0] csr_with_ecc_wr;
  logic [38:0] csr_with_ecc_rd;

  logic [csr_cnt-1:0] csr_we;
  logic [csr_cnt-1:0] csr_src;
  logic [csr_cnt-1:0] csr_re;
  rvtmr #(32) csr_tmr (.I(recovery_csr_rddata_veer_d), .O(csr_with_ecc_wr[0+:32]));
  rvecc_encode csr_ecc_enc (.din(csr_with_ecc_wr[0+:32]), .ecc_out(csr_with_ecc_wr[32+:7]));
  rvecc_decode csr_ecc_dec (
    .en(1'b1), .din(csr_with_ecc_rd[0+:32]), .ecc_in(csr_with_ecc_rd[32+:7]),
    .sed_ded(1'b0), .dout(csr_wrdata), .ecc_out(), .single_ecc_error(), .double_ecc_error() // TODO: Add ECC error to fatal error
  );

  for(genvar i=0; i < csr_cnt; ++i) begin : csr_reg_storage
    assign csr_we[i]  = (cnt_csr[0] == 8'(i)) & mubi_check_true(all_csr_ready);
    assign csr_src[i] = (cnt_csr[1] == 8'(i)) & mubi_check_true(all_csr_ready);
    assign csr_re[i]  = (cnt_csr[2] == 8'(i));
    logic [38:0] csr_recovery_storage_int;
    assign csr_recovery_storage_int = csr_src[i] ? csr_with_ecc_wr : csr_recovery_storage[i];
    rvdffs #(39) csr_recovery_storage_ff (.*, .din(csr_recovery_storage_int), .dout(csr_recovery_storage[i]), .en(csr_we[i]));
  end
  always_comb begin
    csr_with_ecc_rd = '0;
    for (int i=0; i < csr_cnt; ++i) begin
      csr_with_ecc_rd |= ({39{csr_re[i]}} & csr_recovery_storage[i]);
    end
  end

  logic [38:0] gpr_recovery_storage [32];
  logic [38:0] gpr_with_ecc_wr;
  logic [38:0] gpr_with_ecc_rd;

  logic [31:0] gpr_we;
  logic [31:0] gpr_src;
  logic [31:0] gpr_re;
  rvtmr #(32) gpr_tmr (.I(recovery_gpr_rddata_veer_d), .O(gpr_with_ecc_wr[0+:32]));
  rvecc_encode gpr_ecc_enc (.din(gpr_with_ecc_wr[0+:32]), .ecc_out(gpr_with_ecc_wr[32+:7]));
  rvecc_decode gpr_ecc_dec (
    .en(1'b1), .din(gpr_with_ecc_rd[0+:32]), .ecc_in(gpr_with_ecc_rd[32+:7]),
    .sed_ded(1'b0), .dout(gpr_wrdata), .ecc_out(), .single_ecc_error(), .double_ecc_error() // TODO: Add ECC error to fatal error
  );

  for(genvar i=0; i < 32; ++i) begin : gpr_reg_storage
    assign gpr_we[i]  = (cnt_gpr[0] == 6'(i)) & mubi_check_true(all_gpr_ready);
    assign gpr_src[i] = (cnt_gpr[1] == 6'(i)) & mubi_check_true(all_gpr_ready);
    assign gpr_re[i]  = (cnt_gpr[2] == 6'(i));
    logic [38:0] gpr_recovery_storage_int;
    assign gpr_recovery_storage_int = gpr_src[i] ? gpr_with_ecc_wr : gpr_recovery_storage[i];
    rvdffs #(39) gpr_recovery_storage_ff (.*, .din(gpr_recovery_storage_int), .dout(gpr_recovery_storage[i]), .en(gpr_we[i]));
  end
  always_comb begin
    gpr_with_ecc_rd = '0;
    for (int i=0; i < 32; ++i) begin
      gpr_with_ecc_rd |= ({39{gpr_re[i]}} & gpr_recovery_storage[i]);
    end
  end

  for(genvar i=0; i < 3; ++i) begin : cnt_inc_logic
    assign cnt_csr_inc[i] = recovery_state == READ_REG ? csr_with_ecc_wr == csr_with_ecc_rd :
      recovery_state == WRITE_REG ? csr_wrdata == recovery_csr_rddata_veer[i]: 1'b1;
    assign cnt_gpr_inc[i] = recovery_state == READ_REG ? gpr_with_ecc_wr == gpr_with_ecc_rd :
      recovery_state == WRITE_REG ? gpr_wrdata == recovery_gpr_rddata_veer[i]: 1'b1;
  end

  // Flags
  el2_mubi_t read_reg_flag_r[3];
  el2_mubi_t cpu_clear_flag_r[3];
  el2_mubi_t state_recovered_flag_r[3];
  el2_mubi_t cpu_running_flag_r[3];

  for (genvar i=0; i<3; ++i) begin : flag_logic
    // Read flag
    el2_mubi_t read_reg_flag_int;
    el2_mubi_t nxread_reg_flag;
    logic read_reg_flag_clr;
    rvdff #(El2MuBiWidth) read_reg_flag_ff (.*,
      .din(nxread_reg_flag),
      .dout(read_reg_flag_r[i])
    );
    rvtmr #(El2MuBiWidth) read_reg_flag_tmr (.I(read_reg_flag_r), .O(read_reg_flag_int));
    assign nxread_reg_flag = el2_mubi_mux_el2_mubi_true(
      .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(SET_FLAG_RD))),
      .match(El2MuBiTrue),
      .mismatch(el2_mubi_mux_el2_mubi_true(
          .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(CLEAR_FLAG_RD))),
          .match(El2MuBiFalse),
          .mismatch(el2_mubi_mux_el2_mubi_true(
              .sel(el2_mubi_reg_comp(32'(read_reg_flag_int), 32'h0)),
              .match(El2MuBiFalse),
              .mismatch(read_reg_flag_int)
            )
          )
        )
      )
    );

    // CPU clear flag
    el2_mubi_t cpu_clear_flag_int;
    el2_mubi_t nxcpu_clear_flag;
    logic cpu_clear_flag_clr;
    rvdff #(El2MuBiWidth) cpu_clear_flag_ff (.*,
      .din(nxcpu_clear_flag),
      .dout(cpu_clear_flag_r[i])
    );
    rvtmr #(El2MuBiWidth) cpu_clear_flag_tmr (.I(cpu_clear_flag_r), .O(cpu_clear_flag_int));
    assign nxcpu_clear_flag = el2_mubi_mux_el2_mubi_true(
      .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(SET_FLAG_CC))),
      .match(El2MuBiTrue),
      .mismatch(el2_mubi_mux_el2_mubi_true(
          .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(CLEAR_FLAG_CC))),
          .match(El2MuBiFalse),
          .mismatch(el2_mubi_mux_el2_mubi_true(
              .sel(el2_mubi_reg_comp(32'(cpu_clear_flag_int), 32'h0)),
              .match(El2MuBiFalse),
              .mismatch(cpu_clear_flag_int)
            )
          )
        )
      )
    );

    // State recoverd flag
    el2_mubi_t state_recovered_flag_int;
    el2_mubi_t nxstate_recovered_flag;
    logic state_recovered_flag_clr;
    rvdff #(El2MuBiWidth) state_recovered_flag_ff (.*,
          .din(nxstate_recovered_flag),
          .dout(state_recovered_flag_r[i])
    );
    rvtmr #(El2MuBiWidth) state_recovered_flag_tmr (.I(state_recovered_flag_r), .O(state_recovered_flag_int));
    assign nxstate_recovered_flag = el2_mubi_mux_el2_mubi_true(
      .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(SET_FLAG_SR))),
      .match(El2MuBiTrue),
      .mismatch(el2_mubi_mux_el2_mubi_true(
          .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(CLEAR_FLAG_SR))),
          .match(El2MuBiFalse),
          .mismatch(el2_mubi_mux_el2_mubi_true(
              .sel(el2_mubi_reg_comp(32'(state_recovered_flag_int), 32'h0)),
              .match(El2MuBiFalse),
              .mismatch(state_recovered_flag_int)
            )
          )
        )
      )
    );

    // CPU running flag
    el2_mubi_t cpu_running_flag_int;
    el2_mubi_t nxcpu_running_flag;
    logic cpu_running_flag_clr;
    rvdff #(El2MuBiWidth) cpu_running_flag_ff (.*,
          .din(nxcpu_running_flag),
          .dout(cpu_running_flag_r[i])
    );
    rvtmr #(El2MuBiWidth) cpu_running_flag_tmr (.I(cpu_running_flag_r), .O(cpu_running_flag_int));
    assign nxcpu_running_flag = el2_mubi_mux_el2_mubi_true(
      .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(SET_FLAG_CR))),
      .match(El2MuBiTrue),
      .mismatch(el2_mubi_mux_el2_mubi_true(
          .sel(el2_mubi_reg_comp(32'(recovery_state), 32'(CLEAR_FLAG_CR))),
          .match(El2MuBiFalse),
          .mismatch(el2_mubi_mux_el2_mubi_true(
              .sel(el2_mubi_reg_comp(32'(cpu_running_flag_int), 32'h0)),
              .match(El2MuBiFalse),
              .mismatch(cpu_running_flag_int)
            )
          )
        )
      )
    );
  end

  el2_mubi_t read_reg_flag;
  rvtmr #(El2MuBiWidth) read_reg_flag_final_tmr (.I(read_reg_flag_r), .O(read_reg_flag));
  el2_mubi_t cpu_clear_flag;
  rvtmr #(El2MuBiWidth) cpu_clear_flag_final_tmr (.I(cpu_clear_flag_r), .O(cpu_clear_flag));
  el2_mubi_t state_recovered_flag;
  rvtmr #(El2MuBiWidth) state_recovered_flag_final_tmr (.I(state_recovered_flag_r), .O(state_recovered_flag));
  el2_mubi_t cpu_running_flag;
  rvtmr #(El2MuBiWidth) cpu_running_flag_final_tmr (.I(cpu_running_flag_r), .O(cpu_running_flag));

  assign clear_external_flag = el2_mubi_reg_comp(32'(recovery_state), 32'(CLEAR_FLAG_ERR));

  // Recovery state Machine
  always_comb begin : RECOVERY_SM
    recovery_nxstate = IDLE;
    recovery_state_en = 1'b0;
    case(recovery_state)
      IDLE: begin : idle
        recovery_nxstate = el2_mubi_mux_recovery_state_true(.sel(external_flag), .match(HALT_CORES), .mismatch(IDLE));
        recovery_state_en = mubi_check_true(external_flag);
      end
      HALT_CORES: begin : halt_cores
        recovery_nxstate = READ_REG;
        recovery_state_en = (int_o_cpu_halt_ack_veer & int_o_cpu_halt_ack_veer_d) &
          (int_o_cpu_halt_status_veer & int_o_cpu_halt_status_veer_d);
      end
      READ_REG: begin : read_reg
        recovery_nxstate = SET_FLAG_RD;
        recovery_state_en = (cnt_gpr[0][5] & cnt_gpr[1][5] & cnt_gpr[2][5]) &
          (cnt_csr[0] == 8'(csr_cnt) & cnt_csr[1] == 8'(csr_cnt) & cnt_csr[2] == 8'(csr_cnt));
      end
      SET_FLAG_RD: begin : set_flag_rd
        recovery_nxstate = el2_mubi_mux_recovery_state_true(.sel(read_reg_flag), .match(RESET_CPU), .mismatch(SET_FLAG_RD));
        recovery_state_en = mubi_check_true(read_reg_flag);
      end
      RESET_CPU: begin : reset_cpu
        recovery_nxstate = SET_FLAG_CC;
        recovery_state_en = (cnt_gpr[0][3] & cnt_gpr[1][3] & cnt_gpr[2][3]);
      end
      SET_FLAG_CC: begin : set_flag_cc
        recovery_nxstate = el2_mubi_mux_recovery_state_true(.sel(cpu_clear_flag), .match(WRITE_REG), .mismatch(SET_FLAG_CC));
        recovery_state_en = mubi_check_true(cpu_clear_flag);
      end
      WRITE_REG: begin : write_reg
        recovery_nxstate = SET_FLAG_SR;
        recovery_state_en = (cnt_gpr[0][5] & cnt_gpr[1][5] & cnt_gpr[2][5]) &
          (cnt_csr[0] == 8'(csr_cnt) & cnt_csr[1] == 8'(csr_cnt) & cnt_csr[2] == 8'(csr_cnt));
      end
      SET_FLAG_SR: begin : set_flag_sr
        recovery_nxstate = el2_mubi_mux_recovery_state_true(.sel(state_recovered_flag), .match(RESTART_CPU), .mismatch(SET_FLAG_SR));
        recovery_state_en = mubi_check_true(state_recovered_flag);
      end
      RESTART_CPU: begin : restart_cpu
        recovery_nxstate = SET_FLAG_CR;
        recovery_state_en = (int_o_cpu_run_ack_veer & int_o_cpu_run_ack_veer_d) &
          (~int_o_cpu_halt_status_veer & ~int_o_cpu_halt_status_veer_d);
      end
      SET_FLAG_CR: begin : set_flag_cr
        recovery_nxstate = el2_mubi_mux_recovery_state_true(.sel(cpu_running_flag), .match(CLEAR_FLAG_ERR), .mismatch(SET_FLAG_CR));
        recovery_state_en = mubi_check_true(cpu_running_flag);
      end
      CLEAR_FLAG_ERR: begin : clear_flag_err
        recovery_nxstate = el2_mubi_mux_recovery_state_false(.sel(external_flag), .match(CLEAR_FLAG_RD), .mismatch(CLEAR_FLAG_ERR));
        recovery_state_en = mubi_check_false(external_flag);
      end
      CLEAR_FLAG_RD: begin : clear_flag_rd
        recovery_nxstate = el2_mubi_mux_recovery_state_false(.sel(read_reg_flag), .match(CLEAR_FLAG_CC), .mismatch(CLEAR_FLAG_RD));
        recovery_state_en = mubi_check_false(read_reg_flag);
      end
      CLEAR_FLAG_CC: begin : clear_flag_cc
        recovery_nxstate = el2_mubi_mux_recovery_state_false(.sel(cpu_clear_flag), .match(CLEAR_FLAG_SR), .mismatch(CLEAR_FLAG_CC));
        recovery_state_en = mubi_check_false(cpu_clear_flag);
      end
      CLEAR_FLAG_SR: begin : clear_flag_sr
        recovery_nxstate = el2_mubi_mux_recovery_state_false(.sel(state_recovered_flag), .match(CLEAR_FLAG_CR), .mismatch(CLEAR_FLAG_SR));
        recovery_state_en = mubi_check_false(state_recovered_flag);
      end
      CLEAR_FLAG_CR: begin : clear_flag_cr
        recovery_nxstate = el2_mubi_mux_recovery_state_false(.sel(cpu_running_flag), .match(IDLE), .mismatch(CLEAR_FLAG_CR));
        recovery_state_en = mubi_check_false(cpu_running_flag);
      end
      default: begin : invalid
        case({
              mubi_check_false(cpu_running_flag),
              mubi_check_false(state_recovered_flag),
              mubi_check_false(cpu_clear_flag),
              mubi_check_false(read_reg_flag),
              mubi_check_false(external_flag),
              mubi_check_true(cpu_running_flag),
              mubi_check_true(state_recovered_flag),
              mubi_check_true(cpu_clear_flag),
              mubi_check_true(read_reg_flag),
              mubi_check_true(external_flag)})
          10'b1111100000: begin : invalid_to_idle
            recovery_nxstate = IDLE;
            recovery_state_en = 1'b1;
          end
          10'b1111000001: begin : invalid_to_halt_cores
            recovery_nxstate = HALT_CORES;
            recovery_state_en = 1'b1;
          end
          10'b1110000011: begin : invalid_to_disable_cpu_start_after_reset
            recovery_nxstate = RESET_CPU;
            recovery_state_en = 1'b1;
          end
          10'b1100000111: begin : invalid_to_write_regs
            recovery_nxstate = WRITE_REG;
            recovery_state_en = 1'b1;
          end
          10'b1000001111: begin : invalid_to_restart_cpu
            recovery_nxstate = RESTART_CPU;
            recovery_state_en = 1'b1;
          end
          10'b0000011111: begin : invalid_to_clear_err
            recovery_nxstate = CLEAR_FLAG_ERR;
            recovery_state_en = 1'b1;
          end
          10'b0000111110: begin : invalid_to_clear_rd
            recovery_nxstate = CLEAR_FLAG_RD;
            recovery_state_en = 1'b1;
          end
          10'b0001111100: begin : invalid_to_clear_cc
            recovery_nxstate = CLEAR_FLAG_CC;
            recovery_state_en = 1'b1;
          end
          10'b0011111000: begin : invalid_to_clear_sr
            recovery_nxstate = CLEAR_FLAG_SR;
            recovery_state_en = 1'b1;
          end
          10'b0111110000: begin : invalid_to_clear_cr
            recovery_nxstate = CLEAR_FLAG_CR;
            recovery_state_en = 1'b1;
          end
          default: begin : unknown_flag_states
          end
        endcase
      end
    endcase
  end

endmodule

module el2_tmr_csr_addr_decode
(
    input  logic [ 7:0] counter,
    output logic [11:0] csr_addr
);

  // To generate MU mode CSR decode logic
  // 1.  csrrecovery -in csrdecode_mu > csrrecovery_mu.e
  // 2.  espresso -Dso -oeqntott csrdecode_mu.e | ./addassign > csrrecovery_mu.svh
  // To generate M-only mode CSR decode logic
  // 1.  csrrecovery -in csrdecode_m > csrrecovery_m.e
  // 2.  espresso -Dso -oeqntott csrdecode_m.e | ./addassign > csrrecovery_m.svh
`ifdef RV_USER_MODE
  `include "csrrecovery_mu.svh"
`else
  `include "csrrecovery_m.svh"
`endif
endmodule

function automatic recovery_state_t el2_mubi_mux_recovery_state_true (
    el2_mubi_pkg::el2_mubi_t sel, recovery_state_t match, recovery_state_t mismatch
  );
  recovery_state_t steps [el2_mubi_pkg::El2MuBiWidth];
  steps[0] = el2_mubi_pkg::El2MuBiTrue[0] == sel[0] ? match : mismatch;
  for (int i=1; i < el2_mubi_pkg::El2MuBiWidth; ++i) begin
    steps[i] = el2_mubi_pkg::El2MuBiTrue[i] == sel[i] ? steps[i-1] : mismatch;
  end
  return steps[el2_mubi_pkg::El2MuBiWidth-1];
endfunction : el2_mubi_mux_recovery_state_true

function automatic recovery_state_t el2_mubi_mux_recovery_state_false (
    el2_mubi_pkg::el2_mubi_t sel, recovery_state_t match, recovery_state_t mismatch
  );
  recovery_state_t steps [el2_mubi_pkg::El2MuBiWidth];
  steps[0] = el2_mubi_pkg::El2MuBiFalse[0] == sel[0] ? match : mismatch;
  for (int i=1; i < el2_mubi_pkg::El2MuBiWidth; ++i) begin
    steps[i] = el2_mubi_pkg::El2MuBiFalse[i] == sel[i] ? steps[i-1] : mismatch;
  end
  return steps[el2_mubi_pkg::El2MuBiWidth-1];
endfunction : el2_mubi_mux_recovery_state_false

function automatic el2_mubi_pkg::el2_mubi_t el2_mubi_reg_comp (
    logic [31:0] a, logic [31:0] b
  );
  logic [el2_mubi_pkg::El2MuBiWidth-1:0] out;
  logic t, c;
  t = a == b;
  c = a != b;
  for (int i=0; i < el2_mubi_pkg::El2MuBiWidth; ++i) begin
    out[i] = el2_mubi_pkg::El2MuBiTrue[i] ? t : c;
  end
  return el2_mubi_pkg::el2_mubi_t'(out);
endfunction : el2_mubi_reg_comp

`endif
