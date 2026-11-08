module el2_tmr_dec_timer_ctl
import el2_pkg::*;
(
   input logic gclk,
   input logic rst_l,
   input logic recovery_halt,
   input logic active_state_veer[3],
   input logic dec_tlu_dec_clk_override_veer[3],

   input logic        dec_csr_wen_r_mod_veer[3],  // csr write enable at wb
   input logic [11:0] dec_csr_wraddr_r_veer[3],   // write address for csr
   input logic [31:0] dec_csr_wrdata_r_veer[3],   // csr write data at wb

   input logic csr_mitctl0_veer[3],
   input logic csr_mitctl1_veer[3],
   input logic csr_mitb0_veer[3],
   input logic csr_mitb1_veer[3],
   input logic csr_mitcnt0_veer[3],
   input logic csr_mitcnt1_veer[3],

   input logic dec_pause_state_veer[3],            // Paused
   input logic dec_tlu_pmu_fw_halted_veer[3],      // pmu/fw halted
   input logic internal_dbg_halt_timers_veer[3],   // debug halted

   output logic [31:0] dec_timer_rddata_d_veer[3], // timer CSR read data
   output logic        dec_timer_read_d_veer[3],   // timer CSR address match
   output logic        dec_timer_t0_pulse_veer[3], // timer0 int
   output logic        dec_timer_t1_pulse_veer[3], // timer1 int

   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input  logic        scan_mode
   /*pragma coverage on*/
);
  localparam MITCTL_ENABLE             = 0;
  localparam MITCTL_ENABLE_HALTED      = 1;
  localparam MITCTL_ENABLE_PAUSED      = 2;

  logic clk;
  logic free_l2clk;
  logic csr_wr_clk [3];

  logic [1:0] csr_wr_diff[3];
  logic       csr_wr_clk_en_comb[3];

  logic [31:0] mitcnt0_ns[3], mitcnt0[3], mitcnt1_ns[3], mitcnt1[3];
  logic [31:0] mitb0[3], mitb1[3], mitb0_b[3], mitb1_b[3], mitb0_b_ns[3], mitb1_b_ns[3];
  logic [2:0] mitctl0_ns[3], mitctl0[3];
  logic [3:0] mitctl1_ns[3], mitctl1[3];
  logic mit0_match_ns[3];
  logic mit1_match_ns[3];

  logic active_state_int;
  rvtmr #(1) tmr_active_state (.I(active_state_veer), .O(active_state_int));

  // Replicate clocking structure
  rvoclkhdr free_cg2 (.clk(gclk), .en(1'b1), .l1clk(free_l2clk), .*);
  rvoclkhdr active_cg2 (.clk(gclk), .en(active_state_int), .l1clk(clk), .*);
  for (genvar i=0; i < 3; ++i) begin : csr_clk_cg
    rvoclkhdr csr_wr_cg2 (.clk(clk), .en(csr_wr_clk_en_comb[i]), .l1clk(csr_wr_clk[i]), .*);
  end

  for (genvar i=0; i<3; ++i) begin : csr_wr_clk_enable_logic
    assign csr_wr_clk_en_comb[i] = dec_csr_wen_r_mod_veer[i] | dec_tlu_dec_clk_override_veer[i] | (|csr_wr_diff[i]);
  end

  logic  mit0_match[3], mit1_match[3];

  for (genvar i=0; i < 3; ++i) begin : handle_interrupt_generation
    logic [31:0] mitcnt0_int, mitcnt1_int, mitb0_int, mitb1_int;
    logic mit0_match_int, mit1_match_int;

    rvtmr #(32) tmr_mitcnt0 (.I(mitcnt0), .O(mitcnt0_int));
    rvtmr #(32) tmr_mitcnt1 (.I(mitcnt1), .O(mitcnt1_int));
    rvtmr #(32) tmr_mitb0   (.I(mitb0),   .O(mitb0_int));
    rvtmr #(32) tmr_mitb1   (.I(mitb1),   .O(mitb1_int));

    assign mit0_match_ns[i] = (mitcnt0_int[31:0] >= mitb0_int[31:0]);
    assign mit1_match_ns[i] = (mitcnt1_int[31:0] >= mitb1_int[31:0]);

    rvdffsc mit0_match_recv_reg (.*, .clk(free_l2clk), .en(mit0_match_ns[i]), .clear(!recovery_halt),
        .din(1'b1), .dout(mit0_match[i]));
    rvdffsc mit1_match_recv_reg (.*, .clk(free_l2clk), .en(mit1_match_ns[i]), .clear(!recovery_halt),
        .din(1'b1), .dout(mit1_match[i]));

    rvtmr #(1) tmr_mit0_match (.I(mit0_match), .O(mit0_match_int));
    rvtmr #(1) tmr_mit1_match (.I(mit1_match), .O(mit1_match_int));

    assign dec_timer_t0_pulse_veer[i] = (mit0_match_ns[i] | mit0_match_int) & !recovery_halt;
    assign dec_timer_t1_pulse_veer[i] = (mit1_match_ns[i] | mit1_match_int) & !recovery_halt;
  end

  // ----------------------------------------------------------------------
  // MITCNT0 (RW)
  // [31:0] : Internal Timer Counter 0

  localparam MITCNT0       = 12'h7d2;

  for (genvar i=0; i<3; ++i) begin : internal_counter0
    logic wr_mitcnt0_r;
    logic mitcnt0_inc_ok;
    logic mitcnt0_inc_cout;
    logic mitcnt0_wel;
    logic mitcnt0_weh;
    logic [31:0] mitcnt0_inc;
    logic [31:0] mitcnt0_int;
    logic [31:0] mitcnt0_ns_int;

    assign wr_mitcnt0_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITCNT0);

    assign mitcnt0_inc_ok = mitctl0[i][MITCTL_ENABLE] &
                            (~dec_pause_state_veer[i] | mitctl0[i][MITCTL_ENABLE_PAUSED]) &
                            (~dec_tlu_pmu_fw_halted_veer[i] | mitctl0[i][MITCTL_ENABLE_HALTED]) &
                            (~internal_dbg_halt_timers_veer[i] | recovery_halt);

    assign {mitcnt0_inc_cout, mitcnt0_inc[7:0]} = mitcnt0[i][7:0] + {7'b0, 1'b1};
    assign mitcnt0_inc[31:8] = mitcnt0[i][31:8] + {23'b0, mitcnt0_inc_cout};

    assign mitcnt0_ns[i][31:0]  = wr_mitcnt0_r ? dec_csr_wrdata_r_veer[i][31:0] : mit0_match_ns[i] ? 'b0 : mitcnt0_inc[31:0];

    rvtmr #(32) tmr_mitcnt0    (.I(mitcnt0),    .O(mitcnt0_int));
    rvtmr #(32) tmr_mitcnt0_ns (.I(mitcnt0_ns), .O(mitcnt0_ns_int));

    assign mitcnt0_wel = wr_mitcnt0_r | mitcnt0_inc_ok | mit0_match_ns[i];
    assign mitcnt0_weh = wr_mitcnt0_r | (mitcnt0_inc_ok & mitcnt0_inc_cout) | mit0_match_ns[i];

    rvdffe #(24) mitcnt0_ffb      (.*, .clk(free_l2clk), .en(mitcnt0_weh | (mitcnt0[i] != mitcnt0_int)), .din(mitcnt0_ns_int[31:8]), .dout(mitcnt0[i][31:8]));
    rvdffe #(8)  mitcnt0_ffa      (.*, .clk(free_l2clk), .en(mitcnt0_wel | (mitcnt0[i] != mitcnt0_int)), .din(mitcnt0_ns_int[7:0]),  .dout(mitcnt0[i][7:0]));
  end

  // ----------------------------------------------------------------------
  // MITCNT1 (RW)
  // [31:0] : Internal Timer Counter 0

  localparam MITCNT1       = 12'h7d5;

  for (genvar i=0; i<3; ++i) begin : internal_counter1
    logic wr_mitcnt1_r;
    logic mitcnt1_inc_ok;
    logic mitcnt1_inc_cout;
    logic mitcnt1_wel;
    logic mitcnt1_weh;
    logic [31:0] mitcnt1_inc;
    logic [31:0] mitcnt1_int;
    logic [31:0] mitcnt1_ns_int;

    assign wr_mitcnt1_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITCNT1);

    assign mitcnt1_inc_ok = mitctl1[i][MITCTL_ENABLE] &
                            (~dec_pause_state_veer[i] | mitctl1[i][MITCTL_ENABLE_PAUSED]) &
                            (~dec_tlu_pmu_fw_halted_veer[i] | mitctl1[i][MITCTL_ENABLE_HALTED]) &
                            (~internal_dbg_halt_timers_veer[i] | recovery_halt) &
                            (~mitctl1[i][3] | mit0_match_ns[i]);

    // only inc MITCNT1 if not cascaded with 0, or if 0 overflows
    assign {mitcnt1_inc_cout, mitcnt1_inc[7:0]} = mitcnt1[i][7:0] + {7'b0, 1'b1};
    assign mitcnt1_inc[31:8] = mitcnt1[i][31:8] + {23'b0, mitcnt1_inc_cout};

    assign mitcnt1_ns[i][31:0]  = wr_mitcnt1_r ? dec_csr_wrdata_r_veer[i][31:0] : mit1_match_ns[i] ? 'b0 : mitcnt1_inc[31:0];

    rvtmr #(32) tmr_mitcnt1    (.I(mitcnt1),    .O(mitcnt1_int));
    rvtmr #(32) tmr_mitcnt1_ns (.I(mitcnt1_ns), .O(mitcnt1_ns_int));

    assign mitcnt1_wel = wr_mitcnt1_r | mitcnt1_inc_ok | mit1_match_ns[i];
    assign mitcnt1_weh = wr_mitcnt1_r | (mitcnt1_inc_ok & mitcnt1_inc_cout) | mit1_match_ns[i];

    rvdffe #(24) mitcnt1_ffb      (.*, .clk(free_l2clk), .en(mitcnt1_weh | (mitcnt1[i] != mitcnt1_int)), .din(mitcnt1_ns_int[31:8]), .dout(mitcnt1[i][31:8]));
    rvdffe #(8)  mitcnt1_ffa      (.*, .clk(free_l2clk), .en(mitcnt1_wel | (mitcnt1[i] != mitcnt1_int)), .din(mitcnt1_ns_int[7:0]),  .dout(mitcnt1[i][7:0]));
  end

  // ----------------------------------------------------------------------
  // MITB0 (RW)
  // [31:0] : Internal Timer Bound 0

  localparam MITB0         = 12'h7d3;

  for (genvar i=0; i<3; ++i) begin : internal_counter0_bound
    logic wr_mitb0_r;
    logic [31:0] mitb0_b_int;
    logic [31:0] mitb0_b_ns_int;
    assign wr_mitb0_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITB0);

    assign mitb0_b_ns[i] = wr_mitb0_r ? ~dec_csr_wrdata_r_veer[i][31:0] : mitb0_b_int;

    rvtmr #(32) tmr_mitb0_b    (.I(mitb0_b),    .O(mitb0_b_int));
    rvtmr #(32) tmr_mitb0_b_ns (.I(mitb0_b_ns), .O(mitb0_b_ns_int));

    rvdffe #(32) mitb0_ff      (.*, .en(wr_mitb0_r | (mitb0_b[i] != mitb0_b_int)), .din(mitb0_b_ns_int), .dout(mitb0_b[i][31:0]));
    assign mitb0[i][31:0] = ~mitb0_b[i][31:0];
  end

  // ----------------------------------------------------------------------
  // MITB1 (RW)
  // [31:0] : Internal Timer Bound 1

  localparam MITB1         = 12'h7d6;

  for (genvar i=0; i<3; ++i) begin : internal_counter1_bound
    logic wr_mitb1_r;
    logic [31:0] mitb1_b_int;
    logic [31:0] mitb1_b_ns_int;
    assign wr_mitb1_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITB1);

    assign mitb1_b_ns[i] = wr_mitb1_r ? ~dec_csr_wrdata_r_veer[i][31:0] : mitb1_b_int;

    rvtmr #(32) tmr_mitb1_b    (.I(mitb1_b),    .O(mitb1_b_int));
    rvtmr #(32) tmr_mitb1_b_ns (.I(mitb1_b_ns), .O(mitb1_b_ns_int));

    rvdffe #(32) mitb1_ff      (.*, .en(wr_mitb1_r | (mitb1_b[i] != mitb1_b_int)), .din(mitb1_b_ns_int), .dout(mitb1_b[i][31:0]));
    assign mitb1[i][31:0] = ~mitb1_b[i][31:0];
  end

  // ----------------------------------------------------------------------
  // MITCTL0 (RW) Internal Timer Ctl 0
  // [31:3] : Reserved, reads 0x0
  // [2]    : Enable while PAUSEd
  // [1]    : Enable while HALTed
  // [0]    : Enable (resets to 0x1)

  localparam MITCTL0       = 12'h7d4;

  for (genvar i=0; i<3; ++i) begin : internal_counter0_ctrl
    logic wr_mitctl0_r;
    logic mitctl0_0_b;
    logic mitctl0_0_b_ns;
    logic [2:0] mitctl0_ns_int;

    assign wr_mitctl0_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITCTL0);
    assign mitctl0_ns[i][2:0] = wr_mitctl0_r ? {dec_csr_wrdata_r_veer[i][2:0]} : {mitctl0[i][2:0]};

    rvtmr #(3) tmr_mitctl0_ns (.I(mitctl0_ns), .O(mitctl0_ns_int));

    assign csr_wr_diff[i][0] = {mitctl0_ns_int[2:1], mitctl0_0_b_ns} != {mitctl0[i][2:1], mitctl0_0_b};

    assign mitctl0_0_b_ns = ~mitctl0_ns_int[0];
    rvdffs #(3) mitctl0_ff      (.*, .clk(csr_wr_clk[i]), .en(wr_mitctl0_r | (|csr_wr_diff[i])), .din({mitctl0_ns_int[2:1], mitctl0_0_b_ns}), .dout({mitctl0[i][2:1], mitctl0_0_b}));
    assign mitctl0[i][0] = ~mitctl0_0_b;
  end

  // ----------------------------------------------------------------------
  // MITCTL1 (RW) Internal Timer Ctl 1
  // [31:4] : Reserved, reads 0x0
  // [3]    : Cascade
  // [2]    : Enable while PAUSEd
  // [1]    : Enable while HALTed
  // [0]    : Enable (resets to 0x1)

  localparam MITCTL1       = 12'h7d7;

  for (genvar i=0; i<3; ++i) begin : internal_counter1_ctrl
    logic wr_mitctl1_r;
    logic mitctl1_0_b;
    logic mitctl1_0_b_ns;
    logic [3:0] mitctl1_ns_int;

    assign wr_mitctl1_r = dec_csr_wen_r_mod_veer[i] & (dec_csr_wraddr_r_veer[i][11:0] == MITCTL1);
    assign mitctl1_ns[i][3:0] = wr_mitctl1_r ? {dec_csr_wrdata_r_veer[i][3:0]} : {mitctl1[i][3:0]};

    rvtmr #(4) tmr_mitctl1_ns (.I(mitctl1_ns), .O(mitctl1_ns_int));

    assign csr_wr_diff[i][1] = {mitctl1_ns_int[3:1], mitctl1_0_b_ns} != {mitctl1[i][3:1], mitctl1_0_b};

    assign mitctl1_0_b_ns = ~mitctl1_ns_int[0];
    rvdffs #(4) mitctl1_ff      (.*, .clk(csr_wr_clk[i]), .en(wr_mitctl1_r | (|csr_wr_diff[i])), .din({mitctl1_ns_int[3:1], mitctl1_0_b_ns}), .dout({mitctl1[i][3:1], mitctl1_0_b}));
    assign mitctl1[i][0] = ~mitctl1_0_b;
  end

  for (genvar i=0; i < 3; ++i) begin : CSR_access_resp
    logic csr_mitcnt1, csr_mitcnt0, csr_mitb1, csr_mitb0, csr_mitctl0, csr_mitctl1;
    logic [31:0] mitcnt0_int, mitcnt1_int, mitb0_int, mitb1_int;
    logic [2:0]  mitctl0_int;
    logic [3:0]  mitctl1_int;

    rvtmr #(1)  tmr_csr_mitcnt0 (.I(csr_mitcnt0_veer), .O(csr_mitcnt0));
    rvtmr #(1)  tmr_csr_mitcnt1 (.I(csr_mitcnt1_veer), .O(csr_mitcnt1));
    rvtmr #(1)  tmr_csr_mitb0   (.I(csr_mitb0_veer),   .O(csr_mitb0));
    rvtmr #(1)  tmr_csr_mitb1   (.I(csr_mitb1_veer),   .O(csr_mitb1));
    rvtmr #(1)  tmr_csr_mitctl0 (.I(csr_mitctl0_veer), .O(csr_mitctl0));
    rvtmr #(1)  tmr_csr_mitctl1 (.I(csr_mitctl1_veer), .O(csr_mitctl1));
    rvtmr #(32) tmr_mitcnt0     (.I(mitcnt0), .O(mitcnt0_int));
    rvtmr #(32) tmr_mitcnt1     (.I(mitcnt1), .O(mitcnt1_int));
    rvtmr #(32) tmr_mitb0       (.I(mitb0),   .O(mitb0_int));
    rvtmr #(32) tmr_mitb1       (.I(mitb1),   .O(mitb1_int));
    rvtmr #(3)  tmr_mitctl0     (.I(mitctl0), .O(mitctl0_int));
    rvtmr #(4)  tmr_mitctl1     (.I(mitctl1), .O(mitctl1_int));

    assign dec_timer_read_d_veer[i] = csr_mitcnt1 | csr_mitcnt0 | csr_mitb1 | csr_mitb0 | csr_mitctl0 | csr_mitctl1;
    assign dec_timer_rddata_d_veer[i][31:0] = ( ({32{csr_mitcnt0}}      & mitcnt0_int[31:0]) |
                                                ({32{csr_mitcnt1}}      & mitcnt1_int[31:0]) |
                                                ({32{csr_mitb0}}        & mitb0_int[31:0]) |
                                                ({32{csr_mitb1}}        & mitb1_int[31:0]) |
                                                ({32{csr_mitctl0}}      & {29'b0, mitctl0_int[2:0]}) |
                                                ({32{csr_mitctl1}}      & {28'b0, mitctl1_int[3:0]})
                                              );
  end
endmodule // dec_timer_ctl
