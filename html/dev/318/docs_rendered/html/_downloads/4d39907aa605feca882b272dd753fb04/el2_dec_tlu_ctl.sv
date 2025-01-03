// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or it's affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


//********************************************************************************
// el2_dec_tlu_ctl.sv
//
//
// Function: CSRs, Commit/WB, flushing, exceptions, interrupts
// Comments:
//
//********************************************************************************

module el2_dec_tlu_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic clk,
   input logic free_clk,
   input logic free_l2clk,
   input logic rst_l,
   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input logic scan_mode,
   /*pragma coverage on*/

   //rst_vec is supposed to be connected to constant in the top level
   /*pragma coverage off*/
   input logic [31:1] rst_vec, // reset vector, from core pins
   /*pragma coverage on*/
   input logic        nmi_int, // nmi pin
   //nmi_vec is supposed to be connected to constant in the top level
   /*pragma coverage off*/
   input logic [31:1] nmi_vec, // nmi vector
   /*pragma coverage on*/
   input logic  i_cpu_halt_req,    // Asynchronous Halt request to CPU
   input logic  i_cpu_run_req,     // Asynchronous Restart request to CPU

   input logic lsu_fastint_stall_any,   // needed by lsu for 2nd pass of dma with ecc correction, stall next cycle


   // perf counter inputs
   input logic       ifu_pmu_instr_aligned,   // aligned instructions
   input logic       ifu_pmu_fetch_stall, // fetch unit stalled
   input logic       ifu_pmu_ic_miss, // icache miss
   input logic       ifu_pmu_ic_hit, // icache hit
   input logic       ifu_pmu_bus_error, // Instruction side bus error
   input logic       ifu_pmu_bus_busy, // Instruction side bus busy
   input logic       ifu_pmu_bus_trxn, // Instruction side bus transaction
   input logic       dec_pmu_instr_decoded, // decoded instructions
   input logic       dec_pmu_decode_stall, // decode stall
   input logic       dec_pmu_presync_stall, // decode stall due to presync'd inst
   input logic       dec_pmu_postsync_stall,// decode stall due to postsync'd inst
   input logic       lsu_store_stall_any,    // SB or WB is full, stall decode
   input logic       dma_dccm_stall_any,     // DMA stall of lsu
   input logic       dma_iccm_stall_any,     // DMA stall of ifu
   input logic       exu_pmu_i0_br_misp,     // pipe 0 branch misp
   input logic       exu_pmu_i0_br_ataken,   // pipe 0 branch actual taken
   input logic       exu_pmu_i0_pc4,         // pipe 0 4 byte branch
   input logic       lsu_pmu_bus_trxn,       // D side bus transaction
   input logic       lsu_pmu_bus_misaligned, // D side bus misaligned
   input logic       lsu_pmu_bus_error,      // D side bus error
   input logic       lsu_pmu_bus_busy,       // D side bus busy
   input logic       lsu_pmu_load_external_m, // D side bus load
   input logic       lsu_pmu_store_external_m, // D side bus store
   input logic       dma_pmu_dccm_read,          // DMA DCCM read
   input logic       dma_pmu_dccm_write,         // DMA DCCM write
   input logic       dma_pmu_any_read,           // DMA read
   input logic       dma_pmu_any_write,          // DMA write

   input logic [31:1] lsu_fir_addr, // Fast int address
   input logic [1:0] lsu_fir_error, // Fast int lookup error

   input logic       iccm_dma_sb_error,      // I side dma single bit error

   input    el2_lsu_error_pkt_t lsu_error_pkt_r, // lsu precise exception/error packet
   input logic         lsu_single_ecc_error_incr, // LSU inc SB error counter

   input logic dec_pause_state, // Pause counter not zero
   input logic         lsu_imprecise_error_store_any,      // store bus error
   input logic         lsu_imprecise_error_load_any,      // store bus error
   input logic [31:0]  lsu_imprecise_error_addr_any, // store bus error address

   input logic        dec_csr_wen_unq_d,       // valid csr with write - for csr legal
   input logic        dec_csr_any_unq_d,       // valid csr - for csr legal
   input logic [11:0] dec_csr_rdaddr_d,      // read address for csr

   input logic        dec_csr_wen_r,      // csr write enable at wb
   input logic [11:0] dec_csr_rdaddr_r,      // read address for csr
   input logic [11:0] dec_csr_wraddr_r,      // write address for csr
   input logic [31:0] dec_csr_wrdata_r,   // csr write data at wb

   input logic        dec_csr_stall_int_ff, // csr is mie/mstatus

   input logic dec_tlu_i0_valid_r, // pipe 0 op at e4 is valid

   input logic [31:1] exu_npc_r, // for NPC tracking

   input logic [31:1] dec_tlu_i0_pc_r, // for PC/NPC tracking

   input el2_trap_pkt_t dec_tlu_packet_r, // exceptions known at decode

   input logic [31:0] dec_illegal_inst, // For mtval
   input logic        dec_i0_decode_d,  // decode valid, used for clean icache diagnostics

   // branch info from pipe0 for errors or counter updates
   input logic [1:0]  exu_i0_br_hist_r, // history
   input logic        exu_i0_br_error_r, // error
   input logic        exu_i0_br_start_error_r, // start error
   input logic        exu_i0_br_valid_r, // valid
   input logic        exu_i0_br_mp_r, // mispredict
   input logic        exu_i0_br_middle_r, // middle of bank

   // branch info from pipe1 for errors or counter updates

   input logic             exu_i0_br_way_r, // way hit or repl

   output logic dec_tlu_core_empty,  // core is empty
   // Debug start
   output logic dec_dbg_cmd_done, // abstract command done
   output logic dec_dbg_cmd_fail, // abstract command failed
   output logic dec_tlu_dbg_halted, // Core is halted and ready for debug command
   output logic dec_tlu_debug_mode, // Core is in debug mode
   output logic dec_tlu_resume_ack, // Resume acknowledge
   output logic dec_tlu_debug_stall, // stall decode while waiting on core to empty

   output logic dec_tlu_flush_noredir_r , // Tell fetch to idle on this flush
   output logic dec_tlu_mpc_halted_only, // Core is halted only due to MPC
   output logic dec_tlu_flush_leak_one_r, // single step
   output logic dec_tlu_flush_err_r, // iside perr/ecc rfpc. This is the D stage of the error

   output logic dec_tlu_flush_extint, // fast ext int started
   output logic [31:2] dec_tlu_meihap, // meihap for fast int

   input  logic dbg_halt_req, // DM requests a halt
   input  logic dbg_resume_req, // DM requests a resume
   input  logic ifu_miss_state_idle, // I-side miss buffer empty
   input  logic lsu_idle_any, // lsu is idle
   input  logic dec_div_active, // oop div is active
   output el2_trigger_pkt_t  [3:0] trigger_pkt_any, // trigger info for trigger blocks

   input logic  ifu_ic_error_start,     // IC single bit error
   input logic  ifu_iccm_rd_ecc_single_err, // ICCM single bit error


   input logic [70:0] ifu_ic_debug_rd_data, // diagnostic icache read data
   input logic ifu_ic_debug_rd_data_valid, // diagnostic icache read data valid
   output el2_cache_debug_pkt_t dec_tlu_ic_diag_pkt, // packet of DICAWICS, DICAD0/1, DICAGO info for icache diagnostics
   // Debug end

   input logic [7:0] pic_claimid, // pic claimid for csr
   input logic [3:0] pic_pl, // pic priv level for csr
   input logic       mhwakeup, // high priority external int, wakeup if halted

   input logic mexintpend, // external interrupt pending
   input logic timer_int, // timer interrupt pending
   input logic soft_int, // software interrupt pending

   output logic o_cpu_halt_status, // PMU interface, halted
   output logic o_cpu_halt_ack, // halt req ack
   output logic o_cpu_run_ack, // run req ack
   output logic o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request

   /*pragma coverage off*/
   input logic [31:4] core_id, // Core ID
   /*pragma coverage on*/

   // external MPC halt/run interface
   input logic mpc_debug_halt_req, // Async halt request
   input logic mpc_debug_run_req, // Async run request
   input logic mpc_reset_run_req, // Run/halt after reset
   output logic mpc_debug_halt_ack, // Halt ack
   output logic mpc_debug_run_ack, // Run ack
   output logic debug_brkpt_status, // debug breakpoint

   output logic [3:0] dec_tlu_meicurpl, // to PIC
   output logic [3:0] dec_tlu_meipt, // to PIC


   output logic [31:0] dec_csr_rddata_d,      // csr read data at wb
   output logic dec_csr_legal_d,              // csr indicates legal operation

   output el2_br_tlu_pkt_t dec_tlu_br0_r_pkt, // branch pkt to bp

   output logic dec_tlu_i0_kill_writeb_wb,    // I0 is flushed, don't writeback any results to arch state
   output logic dec_tlu_flush_lower_wb,       // commit has a flush (exception, int, mispredict at e4)
   output logic dec_tlu_i0_commit_cmt,        // committed an instruction

   output logic dec_tlu_i0_kill_writeb_r,    // I0 is flushed, don't writeback any results to arch state
   output logic dec_tlu_flush_lower_r,       // commit has a flush (exception, int)
   output logic [31:1] dec_tlu_flush_path_r, // flush pc
   output logic dec_tlu_fence_i_r,           // flush is a fence_i rfnpc, flush icache
   output logic dec_tlu_wr_pause_r,           // CSR write to pause reg is at R.
   output logic dec_tlu_flush_pause_r,        // Flush is due to pause

   output logic dec_tlu_presync_d,            // CSR read needs to be presync'd
   output logic dec_tlu_postsync_d,           // CSR needs to be presync'd


   output logic [31:0] dec_tlu_mrac_ff,        // CSR for memory region control

   output logic dec_tlu_force_halt, // halt has been forced

   output logic dec_tlu_perfcnt0, // toggles when pipe0 perf counter 0 has an event inc
   output logic dec_tlu_perfcnt1, // toggles when pipe0 perf counter 1 has an event inc
   output logic dec_tlu_perfcnt2, // toggles when pipe0 perf counter 2 has an event inc
   output logic dec_tlu_perfcnt3, // toggles when pipe0 perf counter 3 has an event inc

   output logic dec_tlu_i0_exc_valid_wb1, // pipe 0 exception valid
   output logic dec_tlu_i0_valid_wb1,  // pipe 0 valid
   output logic dec_tlu_int_valid_wb1, // pipe 2 int valid
   output logic [4:0] dec_tlu_exc_cause_wb1, // exception or int cause
   output logic [31:0] dec_tlu_mtval_wb1, // MTVAL value

   // feature disable from mfdc
   output logic  dec_tlu_external_ldfwd_disable, // disable external load forwarding
   output logic  dec_tlu_sideeffect_posted_disable,  // disable posted stores to side-effect address
   output logic  dec_tlu_core_ecc_disable, // disable core ECC
   output logic  dec_tlu_bpred_disable,           // disable branch prediction
   output logic  dec_tlu_wb_coalescing_disable,   // disable writebuffer coalescing
   output logic  dec_tlu_pipelining_disable,      // disable pipelining
   output logic  dec_tlu_trace_disable,           // disable trace
   output logic [2:0]  dec_tlu_dma_qos_prty,    // DMA QoS priority coming from MFDC [18:16]

   // clock gating overrides from mcgc
   output logic  dec_tlu_misc_clk_override, // override misc clock domain gating
   output logic  dec_tlu_dec_clk_override,  // override decode clock domain gating
   output logic  dec_tlu_ifu_clk_override,  // override fetch clock domain gating
   output logic  dec_tlu_lsu_clk_override,  // override load/store clock domain gating
   output logic  dec_tlu_bus_clk_override,  // override bus clock domain gating
   output logic  dec_tlu_pic_clk_override,  // override PIC clock domain gating
   output logic  dec_tlu_picio_clk_override,// override PICIO clock domain gating
   output logic  dec_tlu_dccm_clk_override, // override DCCM clock domain gating
   output logic  dec_tlu_icm_clk_override,  // override ICCM clock domain gating

`ifdef RV_USER_MODE

   // Privilege mode
   // 0 - machine, 1 - user
   output logic  priv_mode,
   output logic  priv_mode_eff,
   output logic  priv_mode_ns,

   // mseccfg CSR content for PMP
   output logic [2:0] mseccfg,

`endif

   // pmp
   output el2_pmp_cfg_pkt_t pmp_pmpcfg  [pt.PMP_ENTRIES],
   output logic [31:0]      pmp_pmpaddr [pt.PMP_ENTRIES]
   );

   logic         clk_override, e4e5_int_clk, nmi_fir_type, nmi_lsu_load_type, nmi_lsu_store_type, nmi_int_detected_f, nmi_lsu_load_type_f,
                 nmi_lsu_store_type_f, allow_dbg_halt_csr_write, dbg_cmd_done_ns, i_cpu_run_req_d1_raw, debug_mode_status, lsu_single_ecc_error_r_d1,
                 sel_npc_r, sel_npc_resume, ce_int,
                 nmi_in_debug_mode, dpc_capture_npc, dpc_capture_pc, tdata_load, tdata_opcode, tdata_action, perfcnt_halted, tdata_chain,
                 tdata_kill_write;


   logic reset_delayed, reset_detect, reset_detected;
   logic wr_mstatus_r, wr_mtvec_r, wr_mcyclel_r, wr_mcycleh_r,
         wr_minstretl_r, wr_minstreth_r, wr_mscratch_r, wr_mepc_r, wr_mcause_r, wr_mscause_r, wr_mtval_r,
         wr_mrac_r, wr_meihap_r, wr_meicurpl_r, wr_meipt_r, wr_dcsr_r,
         wr_dpc_r, wr_meicidpl_r, wr_meivt_r, wr_meicpct_r, wr_micect_r, wr_miccmect_r, wr_mfdht_r, wr_mfdhs_r,
         wr_mdccmect_r,wr_mhpme3_r, wr_mhpme4_r, wr_mhpme5_r, wr_mhpme6_r;
   logic wr_mpmc_r;
   logic [1:1] mpmc_b_ns, mpmc, mpmc_b;
   logic set_mie_pmu_fw_halt, fw_halted_ns, fw_halted;
   logic wr_mcountinhibit_r;
`ifdef RV_USER_MODE
   logic wr_mcounteren_r;
   logic [5:0] mcounteren; // HPM6, HPM5, HPM4, HPM3, IR, CY
   logic wr_mseccfg_r;
   logic [2:0] mseccfg_ns;
`endif
   logic [6:0] mcountinhibit;
   logic wr_mtsel_r, wr_mtdata1_t0_r, wr_mtdata1_t1_r, wr_mtdata1_t2_r, wr_mtdata1_t3_r, wr_mtdata2_t0_r, wr_mtdata2_t1_r, wr_mtdata2_t2_r, wr_mtdata2_t3_r;
   logic [31:0] mtdata2_t0, mtdata2_t1, mtdata2_t2, mtdata2_t3, mtdata2_tsel_out, mtdata1_tsel_out;
   logic [9:0]  mtdata1_t0_ns, mtdata1_t0, mtdata1_t1_ns, mtdata1_t1, mtdata1_t2_ns, mtdata1_t2, mtdata1_t3_ns, mtdata1_t3;
   logic [9:0] tdata_wrdata_r;
   logic [1:0] mtsel_ns, mtsel;
   logic tlu_i0_kill_writeb_r;
`ifdef RV_USER_MODE
   logic [3:0]  mstatus_ns, mstatus; // MPRV, MPP (inverted! 0-M, 1-U), MPIE, MIE
`else
   logic [1:0]  mstatus_ns, mstatus;
`endif
   logic [1:0] mfdhs_ns, mfdhs;
   logic [31:0] force_halt_ctr, force_halt_ctr_f;
   logic        force_halt;
   logic [5:0]  mfdht, mfdht_ns;
   logic mstatus_mie_ns;
   logic [30:0] mtvec_ns, mtvec;
   logic [15:2] dcsr_ns, dcsr;
   logic [5:0] mip_ns, mip;
   logic [5:0] mie_ns, mie;
   logic [31:0] mcyclel_ns, mcyclel;
   logic [31:0] mcycleh_ns, mcycleh;
   logic [31:0] minstretl_ns, minstretl;
   logic [31:0] minstreth_ns, minstreth;
   logic [31:0] micect_ns, micect, miccmect_ns, miccmect, mdccmect_ns, mdccmect;
   logic [26:0] micect_inc, miccmect_inc, mdccmect_inc;
   logic [31:0] mscratch;
   logic [31:0] mhpmc3, mhpmc3_ns, mhpmc4, mhpmc4_ns, mhpmc5, mhpmc5_ns, mhpmc6, mhpmc6_ns;
   logic [31:0] mhpmc3h, mhpmc3h_ns, mhpmc4h, mhpmc4h_ns, mhpmc5h, mhpmc5h_ns, mhpmc6h, mhpmc6h_ns;
   logic [9:0]  mhpme3, mhpme4, mhpme5, mhpme6;
   logic [31:0] mrac;
   logic [9:2] meihap;
   logic [31:10] meivt;
   logic [3:0] meicurpl_ns, meicurpl;
   logic [3:0] meicidpl_ns, meicidpl;
   logic [3:0] meipt_ns, meipt;
   logic [31:0] mdseac;
   logic mdseac_locked_ns, mdseac_locked_f, mdseac_en, nmi_lsu_detected;
   logic [31:1] mepc_ns, mepc;
   logic [31:1] dpc_ns, dpc;
   logic [31:0] mcause_ns, mcause;
   logic [3:0] mscause_ns, mscause, mscause_type;
   logic [31:0] mtval_ns, mtval;
   logic dec_pause_state_f, dec_tlu_wr_pause_r_d1, pause_expired_r, pause_expired_wb;
   logic        tlu_flush_lower_r, tlu_flush_lower_r_d1;
   logic [31:1] tlu_flush_path_r,  tlu_flush_path_r_d1;
   logic i0_valid_wb;
   logic tlu_i0_commit_cmt;
   logic [31:1] vectored_path, interrupt_path;
   logic [16:0] dicawics_ns, dicawics;
   logic        wr_dicawics_r, wr_dicad0_r, wr_dicad1_r, wr_dicad0h_r;
   logic [31:0] dicad0_ns, dicad0, dicad0h_ns, dicad0h;

   logic [6:0]  dicad1_ns, dicad1_raw;
   logic [31:0] dicad1;
   logic        ebreak_r, ebreak_to_debug_mode_r, ecall_r, illegal_r, mret_r, inst_acc_r, fence_i_r,
                ic_perr_r, iccm_sbecc_r, ebreak_to_debug_mode_r_d1, kill_ebreak_count_r, inst_acc_second_r;
   logic ce_int_ready, ext_int_ready, timer_int_ready, soft_int_ready, int_timer0_int_ready, int_timer1_int_ready, mhwakeup_ready,
         take_ext_int, take_ce_int, take_timer_int, take_soft_int, take_int_timer0_int, take_int_timer1_int, take_nmi, take_nmi_r_d1, int_timer0_int_possible, int_timer1_int_possible;
   logic i0_exception_valid_r, interrupt_valid_r, i0_exception_valid_r_d1, interrupt_valid_r_d1, exc_or_int_valid_r, exc_or_int_valid_r_d1, mdccme_ce_req, miccme_ce_req, mice_ce_req;
   logic synchronous_flush_r;
   logic [4:0]  exc_cause_r, exc_cause_wb;
   logic        mcyclel_cout, mcyclel_cout_f, mcyclela_cout;
   logic [31:0] mcyclel_inc;
   logic [31:0] mcycleh_inc;

   logic        minstretl_cout, minstretl_cout_f, minstret_enable, minstretl_cout_ns, minstretl_couta;

   logic [31:0] minstretl_inc, minstretl_read;
   logic [31:0] minstreth_inc, minstreth_read;
   logic [31:1] pc_r, pc_r_d1, npc_r, npc_r_d1;
   logic valid_csr;
   logic rfpc_i0_r;
   logic lsu_i0_rfnpc_r;
   logic dec_tlu_br0_error_r, dec_tlu_br0_start_error_r, dec_tlu_br0_v_r;
   logic lsu_i0_exc_r, lsu_i0_exc_r_raw, lsu_exc_ma_r, lsu_exc_acc_r, lsu_exc_st_r,
         lsu_exc_valid_r, lsu_exc_valid_r_raw, lsu_exc_valid_r_d1, lsu_i0_exc_r_d1, block_interrupts;
   logic i0_trigger_eval_r;

   logic request_debug_mode_r, request_debug_mode_r_d1, request_debug_mode_done, request_debug_mode_done_f;
   logic take_halt, halt_taken, halt_taken_f, internal_dbg_halt_mode, dbg_tlu_halted_f, take_reset,
         dbg_tlu_halted, core_empty, lsu_idle_any_f, ifu_miss_state_idle_f, resume_ack_ns,
         debug_halt_req_f, debug_resume_req_f_raw, debug_resume_req_f, enter_debug_halt_req, dcsr_single_step_done, dcsr_single_step_done_f,
         debug_halt_req_d1, debug_halt_req_ns, dcsr_single_step_running, dcsr_single_step_running_f, internal_dbg_halt_timers;

   logic [3:0] i0_trigger_r, trigger_action, trigger_enabled,
               i0_trigger_chain_masked_r;
   logic       i0_trigger_hit_r, i0_trigger_hit_raw_r, i0_trigger_action_r,
               trigger_hit_r_d1,
               mepc_trigger_hit_sel_pc_r;
   logic [3:0] update_hit_bit_r, i0_iside_trigger_has_pri_r,i0trigger_qual_r, i0_lsu_trigger_has_pri_r;
   logic cpu_halt_status, cpu_halt_ack, cpu_run_ack, ext_halt_pulse, i_cpu_halt_req_d1, i_cpu_run_req_d1;

   logic inst_acc_r_raw, trigger_hit_dmode_r, trigger_hit_dmode_r_d1;
   logic [9:0] mcgc, mcgc_ns, mcgc_int;
   logic [18:0] mfdc;
   logic i_cpu_halt_req_sync_qual, i_cpu_run_req_sync_qual, pmu_fw_halt_req_ns, pmu_fw_halt_req_f, int_timer_stalled,
         fw_halt_req, enter_pmu_fw_halt_req, pmu_fw_tlu_halted, pmu_fw_tlu_halted_f, internal_pmu_fw_halt_mode,
         internal_pmu_fw_halt_mode_f, int_timer0_int_hold, int_timer1_int_hold, int_timer0_int_hold_f, int_timer1_int_hold_f;
   logic nmi_int_delayed, nmi_int_detected;
   logic [3:0] trigger_execute, trigger_data, trigger_store;
   logic dec_tlu_pmu_fw_halted;

   logic mpc_run_state_ns, debug_brkpt_status_ns, mpc_debug_halt_ack_ns, mpc_debug_run_ack_ns, dbg_halt_state_ns, dbg_run_state_ns,
         dbg_halt_state_f, mpc_debug_halt_req_sync_f, mpc_debug_run_req_sync_f, mpc_halt_state_f, mpc_halt_state_ns, mpc_run_state_f, debug_brkpt_status_f,
         mpc_debug_halt_ack_f, mpc_debug_run_ack_f, dbg_run_state_f, mpc_debug_halt_req_sync_pulse,
         mpc_debug_run_req_sync_pulse, debug_brkpt_valid, debug_halt_req, debug_resume_req, dec_tlu_mpc_halted_only_ns;
   logic take_ext_int_start, ext_int_freeze, take_ext_int_start_d1, take_ext_int_start_d2,
         take_ext_int_start_d3, ext_int_freeze_d1, ignore_ext_int_due_to_lsu_stall;
   logic mcause_sel_nmi_store, mcause_sel_nmi_load, mcause_sel_nmi_ext, fast_int_meicpct;
   logic [1:0] mcause_fir_error_type;
   logic dbg_halt_req_held_ns, dbg_halt_req_held, dbg_halt_req_final;
   logic iccm_repair_state_ns, iccm_repair_state_d1, iccm_repair_state_rfnpc;


   // internal timer, isolated for size reasons
   logic [31:0] dec_timer_rddata_d;
   logic dec_timer_read_d, dec_timer_t0_pulse, dec_timer_t1_pulse;

   // PMP unit, isolated for size reasons
   logic [31:0] dec_pmp_rddata_d;
   logic dec_pmp_read_d;

   logic nmi_int_sync, timer_int_sync, soft_int_sync, i_cpu_halt_req_sync, i_cpu_run_req_sync, mpc_debug_halt_req_sync, mpc_debug_run_req_sync, mpc_debug_halt_req_sync_raw;
   logic csr_wr_clk;
   logic e4e5_clk, e4_valid, e5_valid, e4e5_valid, internal_dbg_halt_mode_f, internal_dbg_halt_mode_f2;
   logic lsu_pmu_load_external_r, lsu_pmu_store_external_r;
   logic dec_tlu_flush_noredir_r_d1, dec_tlu_flush_pause_r_d1;
   logic lsu_single_ecc_error_r;
   logic [31:0] lsu_error_pkt_addr_r;
   logic mcyclel_cout_in;
   logic i0_valid_no_ebreak_ecall_r;
   logic minstret_enable_f;
   logic sel_exu_npc_r, sel_flush_npc_r, sel_hold_npc_r;
   logic pc0_valid_r;
   logic [15:0] mfdc_int, mfdc_ns;
   logic [31:0] mrac_in;
   logic [31:27] csr_sat;
   logic [8:6] dcsr_cause;
   logic enter_debug_halt_req_le, dcsr_cause_upgradeable;
   logic icache_rd_valid, icache_wr_valid, icache_rd_valid_f, icache_wr_valid_f;
   logic [3:0]      mhpmc_inc_r, mhpmc_inc_r_d1;

   logic [3:0][9:0] mhpme_vec;
   logic            mhpmc3_wr_en0, mhpmc3_wr_en1, mhpmc3_wr_en;
   logic            mhpmc4_wr_en0, mhpmc4_wr_en1, mhpmc4_wr_en;
   logic            mhpmc5_wr_en0, mhpmc5_wr_en1, mhpmc5_wr_en;
   logic            mhpmc6_wr_en0, mhpmc6_wr_en1, mhpmc6_wr_en;
   logic            mhpmc3h_wr_en0, mhpmc3h_wr_en;
   logic            mhpmc4h_wr_en0, mhpmc4h_wr_en;
   logic            mhpmc5h_wr_en0, mhpmc5h_wr_en;
   logic            mhpmc6h_wr_en0, mhpmc6h_wr_en;
   logic [63:0]     mhpmc3_incr, mhpmc4_incr, mhpmc5_incr, mhpmc6_incr;
   logic perfcnt_halted_d1, zero_event_r;
   logic [3:0] perfcnt_during_sleep;
   logic [9:0] event_r;

   el2_inst_pkt_t pmu_i0_itype_qual;

   logic dec_csr_wen_r_mod;

   logic flush_clkvalid;
   logic sel_fir_addr;
   logic wr_mie_r;
   logic mtval_capture_pc_r;
   logic mtval_capture_pc_plus2_r;
   logic mtval_capture_inst_r;
   logic mtval_capture_lsu_r;
   logic mtval_clear_r;
   logic wr_mcgc_r;
   logic wr_mfdc_r;
   logic wr_mdeau_r;
   logic trigger_hit_for_dscr_cause_r_d1;
   logic conditionally_illegal;

   logic  [3:0] ifu_mscause ;
   logic        ifu_ic_error_start_f, ifu_iccm_rd_ecc_single_err_f;

   // CSR address decoder

// files "csrdecode_m" (machine mode only) and "csrdecode_mu" (machine mode plus
// user mode) are human readable that have all of the CSR decodes defined and
// are part of the git repo. Modify these files as needed.

// to generate all the equations below from "csrdecode" except legal equation:

// 1) coredecode -in csrdecode > corecsrdecode.e

// 2) espresso -Dso -oeqntott < corecsrdecode.e | addassign > csrequations

// to generate the legal CSR equation below:

// 1) coredecode -in csrdecode -legal > csrlegal.e

// 2) espresso -Dso -oeqntott < csrlegal.e | addassign > csrlegal_equation

// coredecode -in csrdecode > corecsrdecode.e; espresso -Dso -oeqntott < corecsrdecode.e | addassign > csrequations; coredecode -in csrdecode -legal > csrlegal.e; espresso -Dso -oeqntott csrlegal.e | addassign > csrlegal_equation

`ifdef RV_USER_MODE

   `include "el2_dec_csr_equ_mu.svh"

   logic  csr_acc_r;    // CSR access error
   logic  csr_wr_usr_r; // Write to an unprivileged/user-level CSR
   logic  csr_rd_usr_r; // REad from an unprivileged/user-level CSR

`else

   `include "el2_dec_csr_equ_m.svh"

`endif

   el2_dec_timer_ctl  #(.pt(pt)) int_timers(.*);
   // end of internal timers

   el2_dec_pmp_ctl  #(.pt(pt)) pmp(.*);
   // end of pmp

   assign clk_override = dec_tlu_dec_clk_override;

   // Async inputs to the core have to be sync'd to the core clock.
   rvsyncss #(7) syncro_ff(.*,
                           .clk(free_clk),
                           .din ({nmi_int,      timer_int,      soft_int,      i_cpu_halt_req,      i_cpu_run_req,      mpc_debug_halt_req,          mpc_debug_run_req}),
                           .dout({nmi_int_sync, timer_int_sync, soft_int_sync, i_cpu_halt_req_sync, i_cpu_run_req_sync, mpc_debug_halt_req_sync_raw, mpc_debug_run_req_sync}));

   // for CSRs that have inpipe writes only

   rvoclkhdr csrwr_r_cgc   ( .en(dec_csr_wen_r_mod | clk_override), .l1clk(csr_wr_clk), .* );

   assign e4_valid = dec_tlu_i0_valid_r;
   assign e4e5_valid = e4_valid | e5_valid;
   assign flush_clkvalid = internal_dbg_halt_mode_f | i_cpu_run_req_d1 | interrupt_valid_r | interrupt_valid_r_d1 |
                           reset_delayed | pause_expired_r | pause_expired_wb | ic_perr_r | iccm_sbecc_r |
                           clk_override;
   rvoclkhdr e4e5_cgc     ( .en(e4e5_valid | clk_override), .l1clk(e4e5_clk), .* );
   rvoclkhdr e4e5_int_cgc ( .en(e4e5_valid | flush_clkvalid), .l1clk(e4e5_int_clk), .* );

   rvdffie #(11)  freeff (.*, .clk(free_l2clk),
                          .din ({ifu_ic_error_start, ifu_iccm_rd_ecc_single_err, iccm_repair_state_ns, e4_valid, internal_dbg_halt_mode,
                                 lsu_pmu_load_external_m, lsu_pmu_store_external_m, tlu_flush_lower_r,  tlu_i0_kill_writeb_r,
                                 internal_dbg_halt_mode_f, force_halt}),
                          .dout({ifu_ic_error_start_f, ifu_iccm_rd_ecc_single_err_f, iccm_repair_state_d1, e5_valid, internal_dbg_halt_mode_f,
                                 lsu_pmu_load_external_r, lsu_pmu_store_external_r, tlu_flush_lower_r_d1, dec_tlu_i0_kill_writeb_wb,
                                 internal_dbg_halt_mode_f2, dec_tlu_force_halt}));

   assign dec_tlu_i0_kill_writeb_r = tlu_i0_kill_writeb_r;

   assign nmi_int_detected = (nmi_int_sync & ~nmi_int_delayed) | nmi_lsu_detected | (nmi_int_detected_f & ~take_nmi_r_d1) | nmi_fir_type;
   // if the first nmi is a lsu type, note it. If there's already an nmi pending, ignore. Simultaneous with FIR, drop.
   assign nmi_lsu_load_type  = (nmi_lsu_detected & lsu_imprecise_error_load_any &  ~(nmi_int_detected_f & ~take_nmi_r_d1)) |
                               (nmi_lsu_load_type_f  & ~take_nmi_r_d1);
   assign nmi_lsu_store_type = (nmi_lsu_detected & lsu_imprecise_error_store_any & ~(nmi_int_detected_f & ~take_nmi_r_d1)) |
                               (nmi_lsu_store_type_f & ~take_nmi_r_d1);

   assign nmi_fir_type = ~nmi_int_detected_f & take_ext_int_start_d3 & |lsu_fir_error[1:0];

   // Filter subsequent bus errors after the first, until the lock on MDSEAC is cleared
   assign nmi_lsu_detected = ~mdseac_locked_f & (lsu_imprecise_error_load_any | lsu_imprecise_error_store_any) & ~nmi_fir_type;


localparam MSTATUS_MIE   = 0;
localparam int MSTATUS_MPIE  = 1;
`ifdef RV_USER_MODE
localparam MSTATUS_MPP   = 2;
localparam MSTATUS_MPRV  = 3;
`endif

localparam MIP_MCEIP     = 5;
localparam MIP_MITIP0    = 4;
localparam MIP_MITIP1    = 3;
localparam MIP_MEIP      = 2;
localparam MIP_MTIP      = 1;
localparam MIP_MSIP      = 0;

localparam MIE_MCEIE     = 5;
localparam MIE_MITIE0    = 4;
localparam MIE_MITIE1    = 3;
localparam MIE_MEIE      = 2;
localparam MIE_MTIE      = 1;
localparam MIE_MSIE      = 0;

localparam DCSR_EBREAKM  = 15;
localparam DCSR_STEPIE   = 11;
localparam DCSR_STOPC    = 10;
localparam DCSR_STEP     = 2;

`ifdef RV_USER_MODE
localparam MCOUNTEREN_CY   = 0;
localparam MCOUNTEREN_IR   = 1;
localparam MCOUNTEREN_HPM3 = 2;
localparam MCOUNTEREN_HPM4 = 3;
localparam MCOUNTEREN_HPM5 = 4;
localparam MCOUNTEREN_HPM6 = 5;

localparam MSECCFG_RLB   = 2;
localparam MSECCFG_MMWP  = 1;
localparam MSECCFG_MML   = 0;
`endif

   // ----------------------------------------------------------------------
   // MISA (RO)
   //  [31:30] XLEN - implementation width, 2'b01 - 32 bits
   //  [20]    U    - user mode support (if enabled in config)
   //  [12]    M    - integer mul/div
   //  [8]     I    - RV32I
   //  [2]     C    - Compressed extension
   localparam MISA          = 12'h301;

   // MVENDORID, MARCHID, MIMPID, MHARTID
   localparam MVENDORID     = 12'hf11;
   localparam MARCHID       = 12'hf12;
   localparam MIMPID        = 12'hf13;
   localparam MHARTID       = 12'hf14;


   // ----------------------------------------------------------------------
   // MSTATUS (RW)
   // [17]    MPRV : Modify PRiVilege (if enabled in config)
   // [12:11] MPP  : Prior priv level, either 2'b11 (machine) or 2'b00 (user)
   // [7]     MPIE : Int enable previous [1]
   // [3]     MIE  : Int enable          [0]
   localparam MSTATUS       = 12'h300;

   // ----------------------------------------------------------------------
   // MTVEC (RW)
   // [31:2] BASE : Trap vector base address
   // [1] - Reserved, not implemented, reads zero
   // [0]  MODE : 0 = Direct, 1 = Asyncs are vectored to BASE + (4 * CAUSE)
   localparam MTVEC         = 12'h305;

   // ----------------------------------------------------------------------
   // MIP (RW)
   //
   // [30] MCEIP  : (RO) M-Mode Correctable Error interrupt pending
   // [29] MITIP0 : (RO) M-Mode Internal Timer0 interrupt pending
   // [28] MITIP1 : (RO) M-Mode Internal Timer1 interrupt pending
   // [11] MEIP   : (RO) M-Mode external interrupt pending
   // [7]  MTIP   : (RO) M-Mode timer interrupt pending
   // [3]  MSIP   : (RO) M-Mode software interrupt pending
   localparam MIP           = 12'h344;

   // ----------------------------------------------------------------------
   // MIE (RW)
   // [30] MCEIE  : (RO) M-Mode Correctable Error interrupt enable
   // [29] MITIE0 : (RO) M-Mode Internal Timer0 interrupt enable
   // [28] MITIE1 : (RO) M-Mode Internal Timer1 interrupt enable
   // [11] MEIE   : (RW) M-Mode external interrupt enable
   // [7]  MTIE   : (RW) M-Mode timer interrupt enable
   // [3]  MSIE   : (RW) M-Mode software interrupt enable
   localparam MIE           = 12'h304;

   // ----------------------------------------------------------------------
   // MCYCLEL (RW)
   // [31:0] : Lower Cycle count

   localparam MCYCLEL       = 12'hb00;
   localparam logic [11:0] CYCLEL  = 12'hc00;

   // ----------------------------------------------------------------------
   // MCYCLEH (RW)
   // [63:32] : Higher Cycle count
   // Chained with mcyclel. Note: mcyclel overflow due to a mcycleh write gets ignored.

   localparam MCYCLEH       = 12'hb80;
   localparam logic [11:0] CYCLEH  = 12'hc80;

   // ----------------------------------------------------------------------
   // MINSTRETL (RW)
   // [31:0] : Lower Instruction retired count
   // From the spec "Some CSRs, such as the instructions retired counter, instret, may be modified as side effects
   // of instruction execution. In these cases, if a CSR access instruction reads a CSR, it reads the
   // value prior to the execution of the instruction. If a CSR access instruction writes a CSR, the
   // update occurs after the execution of the instruction. In particular, a value written to instret by
   // one instruction will be the value read by the following instruction (i.e., the increment of instret
   // caused by the first instruction retiring happens before the write of the new value)."
   localparam MINSTRETL     = 12'hb02;
   localparam logic [11:0] INSTRETL  = 12'hc02;

   // ----------------------------------------------------------------------
   // MINSTRETH (RW)
   // [63:32] : Higher Instret count
   // Chained with minstretl. Note: minstretl overflow due to a minstreth write gets ignored.

   localparam MINSTRETH     = 12'hb82;
   localparam logic [11:0] INSTRETH  = 12'hc82;

   // ----------------------------------------------------------------------
   // MSCRATCH (RW)
   // [31:0] : Scratch register
   localparam MSCRATCH      = 12'h340;

   // ----------------------------------------------------------------------
   // MEPC (RW)
   // [31:1] : Exception PC
   localparam MEPC          = 12'h341;

   // ----------------------------------------------------------------------
   // MCAUSE (RW)
   // [31:0] : Exception Cause
   localparam MCAUSE        = 12'h342;

   // ----------------------------------------------------------------------
   // MSCAUSE (RW)
   // [2:0] : Secondary exception Cause
   localparam MSCAUSE       = 12'h7ff;

   // ----------------------------------------------------------------------
   // MTVAL (RW)
   // [31:0] : Exception address if relevant
   localparam MTVAL         = 12'h343;

   // ----------------------------------------------------------------------
   // MCGC (RW) Clock gating control
   // [31:10]: Reserved, reads 0x0
   // [9]    : picio_clk_override
   // [7]    : dec_clk_override
   // [6]    : Unused
   // [5]    : ifu_clk_override
   // [4]    : lsu_clk_override
   // [3]    : bus_clk_override
   // [2]    : pic_clk_override
   // [1]    : dccm_clk_override
   // [0]    : icm_clk_override
   //
   localparam MCGC          = 12'h7f8;

   // ----------------------------------------------------------------------
   // MFDC (RW) Feature Disable Control
   // [31:19] : Reserved, reads 0x0
   // [18:16] : DMA QoS Prty
   // [15:13] : Reserved, reads 0x0
   // [12]   : Disable trace
   // [11]   : Disable external load forwarding
   // [10]   : Disable dual issue
   // [9]    : Disable pic multiple ints
   // [8]    : Disable core ecc
   // [7]    : Disable secondary alu?s
   // [6]    : Unused, 0x0
   // [5]    : Disable non-blocking loads/divides
   // [4]    : Disable fast divide
   // [3]    : Disable branch prediction and return stack
   // [2]    : Disable write buffer coalescing
   // [1]    : Disable load misses that bypass the write buffer
   // [0]    : Disable pipelining - Enable single instruction execution
   //
   localparam MFDC          = 12'h7f9;

   // ----------------------------------------------------------------------
   // MRAC (RW)
   // [31:0] : Region Access Control Register, 16 regions, {side_effect, cachable} pairs
   localparam MRAC          = 12'h7c0;

   // ----------------------------------------------------------------------
   // MDEAU (WAR0)
   // [31:0] : Dbus Error Address Unlock register
   //
   localparam MDEAU         = 12'hbc0;

   // ----------------------------------------------------------------------
   // MDSEAC (R)
   // [31:0] : Dbus Store Error Address Capture register
   //
   localparam MDSEAC        = 12'hfc0;

   // ----------------------------------------------------------------------
   // MPMC (R0W1)
   // [0] : FW halt
   // [1] : Set MSTATUS[MIE] on halt
   localparam MPMC          = 12'h7c6;

   // ----------------------------------------------------------------------
   // MICECT (I-Cache error counter/threshold)
   // [31:27] : Icache parity error threshold
   // [26:0]  : Icache parity error count
   localparam MICECT        = 12'h7f0;

   // ----------------------------------------------------------------------
   // MICCMECT (ICCM error counter/threshold)
   // [31:27] : ICCM parity error threshold
   // [26:0]  : ICCM parity error count
   localparam MICCMECT      = 12'h7f1;

   // ----------------------------------------------------------------------
   // MDCCMECT (DCCM error counter/threshold)
   // [31:27] : DCCM parity error threshold
   // [26:0]  : DCCM parity error count
   localparam MDCCMECT      = 12'h7f2;

   // ----------------------------------------------------------------------
   // MFDHT (Force Debug Halt Threshold)
   // [5:1] : Halt timeout threshold (power of 2)
   //   [0] : Halt timeout enabled
   localparam MFDHT         = 12'h7ce;

   // ----------------------------------------------------------------------
   // MFDHS(RW)
   // [1] : LSU operation pending when debug halt threshold reached
   // [0] : IFU operation pending when debug halt threshold reached
   localparam MFDHS         = 12'h7cf;

   // ----------------------------------------------------------------------
   // MEIVT (External Interrupt Vector Table (R/W))
   // [31:10]: Base address (R/W)
   // [9:0]  : Reserved, reads 0x0
   localparam MEIVT         = 12'hbc8;

   // ----------------------------------------------------------------------
   // MEICURPL (R/W)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : CURRPRI - Priority level of current interrupt service routine (R/W)
   localparam MEICURPL      = 12'hbcc;

   // ----------------------------------------------------------------------
   // MEICIDPL (R/W)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : External Interrupt Claim ID's Priority Level Register
   localparam MEICIDPL      = 12'hbcb;

   // ----------------------------------------------------------------------
   // MEICPCT (Capture CLAIMID in MEIHAP and PL in MEICIDPL
   // [31:1] : Reserved (read 0x0)
   // [0]    : Capture (W1, Read 0)
   localparam MEICPCT       = 12'hbca;

   // ----------------------------------------------------------------------
   // MEIPT (External Interrupt Priority Threshold)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : PRITHRESH
   localparam MEIPT         = 12'hbc9;

   // ----------------------------------------------------------------------
   // DCSR (R/W) (Only accessible in debug mode)
   // [31:28] : xdebugver (hard coded to 0x4) RO
   // [27:16] : 0x0, reserved
   // [15]    : ebreakm
   // [14]    : 0x0, reserved
   // [13]    : ebreaks (0x0 for this core)
   // [12]    : ebreaku (0x0 for this core)
   // [11]    : stepie
   // [10]    : stopcount
   // [9]     : 0x0 //stoptime
   // [8:6]   : cause (RO)
   // [5:4]   : 0x0, reserved
   // [3]     : nmip
   // [2]     : step
   // [1:0]   : prv (0x3 for this core)
   //
   localparam DCSR          = 12'h7b0;

   // ----------------------------------------------------------------------
   // DPC (R/W) (Only accessible in debug mode)
   // [31:0] : Debug PC
   localparam DPC           = 12'h7b1;

   // ----------------------------------------------------------------------
   // DICAWICS (R/W) (Only accessible in debug mode)
   // [31:25] : Reserved
   // [24]    : Array select, 0 is data, 1 is tag
   // [23:22] : Reserved
   // [21:20] : Way select
   // [19:17] : Reserved
   // [16:3]  : Index
   // [2:0]   : Reserved
   localparam DICAWICS      = 12'h7c8;

   // ----------------------------------------------------------------------
   // DICAD0 (R/W) (Only accessible in debug mode)
   //
   // If dicawics[array] is 0
   // [31:0]  : inst data
   //
   // If dicawics[array] is 1
   // [31:16] : Tag
   // [15:7]  : Reserved
   // [6:4]   : LRU
   // [3:1]   : Reserved
   // [0]     : Valid
   localparam DICAD0        = 12'h7c9;

   // ----------------------------------------------------------------------
   // DICAD0H (R/W) (Only accessible in debug mode)
   //
   // If dicawics[array] is 0
   // [63:32]  : inst data
   //
   localparam DICAD0H       = 12'h7cc;

   // ----------------------------------------------------------------------
   // DICAGO (R/W) (Only accessible in debug mode)
   // [0]     : Go
   localparam DICAGO        = 12'h7cb;

   // ----------------------------------------------------------------------
   // MHPMC3H(RW), MHPMC3(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 3
   localparam MHPMC3        = 12'hB03;
   localparam MHPMC3H       = 12'hB83;
`ifdef RV_USER_MODE
   localparam HPMC3         = 12'hC03;
   localparam HPMC3H        = 12'hC83;
`endif

   // ----------------------------------------------------------------------
   // MHPMC4H(RW), MHPMC4(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 4
   localparam MHPMC4        = 12'hB04;
   localparam MHPMC4H       = 12'hB84;
`ifdef RV_USER_MODE
   localparam HPMC4         = 12'hC04;
   localparam HPMC4H        = 12'hC84;
`endif

   // ----------------------------------------------------------------------
   // MHPMC5H(RW), MHPMC5(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 5
   localparam MHPMC5        = 12'hB05;
   localparam MHPMC5H       = 12'hB85;
`ifdef RV_USER_MODE
   localparam HPMC5         = 12'hC05;
   localparam HPMC5H        = 12'hC85;
`endif

   // ----------------------------------------------------------------------
   // MHPMC6H(RW), MHPMC6(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 6
   localparam MHPMC6        = 12'hB06;
   localparam MHPMC6H       = 12'hB86;
`ifdef RV_USER_MODE
   localparam HPMC6         = 12'hC06;
   localparam HPMC6H        = 12'hC86;
`endif

   // ----------------------------------------------------------------------
   // MHPME3(RW)
   // [9:0] : Hardware Performance Monitor Event 3
   localparam MHPME3        = 12'h323;

   // ----------------------------------------------------------------------
   // MHPME4(RW)
   // [9:0] : Hardware Performance Monitor Event 4
   localparam MHPME4        = 12'h324;

   // ----------------------------------------------------------------------
   // MHPME5(RW)
   // [9:0] : Hardware Performance Monitor Event 5
   localparam MHPME5        = 12'h325;

   // ----------------------------------------------------------------------
   // MHPME6(RW)
   // [9:0] : Hardware Performance Monitor Event 6
   localparam MHPME6        = 12'h326;

   // MCOUNTINHIBIT(RW)
   // [31:7] : Reserved, read 0x0
   // [6]    : HPM6 disable
   // [5]    : HPM5 disable
   // [4]    : HPM4 disable
   // [3]    : HPM3 disable
   // [2]    : MINSTRET disable
   // [1]    : reserved, read 0x0
   // [0]    : MCYCLE disable

   localparam MCOUNTINHIBIT             = 12'h320;

   // ----------------------------------------------------------------------
   // MTSEL (R/W)
   // [1:0] : Trigger select : 00, 01, 10 are data/address triggers. 11 is inst count
   localparam MTSEL         = 12'h7a0;

   // ----------------------------------------------------------------------
   // MTDATA1 (R/W)
   // [31:0] : Trigger Data 1
   localparam MTDATA1       = 12'h7a1;

   // ----------------------------------------------------------------------
   // MTDATA2 (R/W)
   // [31:0] : Trigger Data 2
   localparam MTDATA2       = 12'h7a2;

   assign reset_delayed = reset_detect ^ reset_detected;

   // ----------------------------------------------------------------------
   // MPC halt
   // - can interact with debugger halt and v-v

   // fast ints in progress have priority
   assign mpc_debug_halt_req_sync = mpc_debug_halt_req_sync_raw & ~ext_int_freeze_d1;

    rvdffie #(16)  mpvhalt_ff (.*, .clk(free_l2clk),
                                 .din({1'b1, reset_detect,
                                       nmi_int_sync, nmi_int_detected, nmi_lsu_load_type, nmi_lsu_store_type,
                                       mpc_debug_halt_req_sync, mpc_debug_run_req_sync,
                                       mpc_halt_state_ns, mpc_run_state_ns, debug_brkpt_status_ns,
                                       mpc_debug_halt_ack_ns, mpc_debug_run_ack_ns,
                                       dbg_halt_state_ns, dbg_run_state_ns,
                                       dec_tlu_mpc_halted_only_ns}),
                                .dout({reset_detect, reset_detected,
                                       nmi_int_delayed, nmi_int_detected_f, nmi_lsu_load_type_f, nmi_lsu_store_type_f,
                                       mpc_debug_halt_req_sync_f, mpc_debug_run_req_sync_f,
                                       mpc_halt_state_f, mpc_run_state_f, debug_brkpt_status_f,
                                       mpc_debug_halt_ack_f, mpc_debug_run_ack_f,
                                       dbg_halt_state_f, dbg_run_state_f,
                                       dec_tlu_mpc_halted_only}));

   // turn level sensitive requests into pulses
   assign mpc_debug_halt_req_sync_pulse = mpc_debug_halt_req_sync & ~mpc_debug_halt_req_sync_f;
   assign mpc_debug_run_req_sync_pulse = mpc_debug_run_req_sync & ~mpc_debug_run_req_sync_f;

   // states
   assign mpc_halt_state_ns = (mpc_halt_state_f | mpc_debug_halt_req_sync_pulse | (reset_delayed & ~mpc_reset_run_req)) & ~mpc_debug_run_req_sync;
   assign mpc_run_state_ns = (mpc_run_state_f | (mpc_debug_run_req_sync_pulse & ~mpc_debug_run_ack_f)) & (internal_dbg_halt_mode_f & ~dcsr_single_step_running_f);

   // note, MPC halt can allow the jtag debugger to just start sending commands. When that happens, set the interal debugger halt state to prevent
   // MPC run from starting the core.
   assign dbg_halt_state_ns = (dbg_halt_state_f | (dbg_halt_req_final | dcsr_single_step_done_f | trigger_hit_dmode_r_d1 | ebreak_to_debug_mode_r_d1)) & ~dbg_resume_req;
   assign dbg_run_state_ns = (dbg_run_state_f | dbg_resume_req) & (internal_dbg_halt_mode_f & ~dcsr_single_step_running_f);

   // tell dbg we are only MPC halted
   assign dec_tlu_mpc_halted_only_ns = ~dbg_halt_state_f & mpc_halt_state_f;

   // this asserts from detection of bkpt until after we leave debug mode
   assign debug_brkpt_valid = ebreak_to_debug_mode_r_d1 | trigger_hit_dmode_r_d1;
   assign debug_brkpt_status_ns = (debug_brkpt_valid | debug_brkpt_status_f) & (internal_dbg_halt_mode & ~dcsr_single_step_running_f);

   // acks back to interface
   assign mpc_debug_halt_ack_ns = (mpc_halt_state_f & internal_dbg_halt_mode_f & mpc_debug_halt_req_sync & core_empty) | (mpc_debug_halt_ack_f & mpc_debug_halt_req_sync);
   assign mpc_debug_run_ack_ns = (mpc_debug_run_req_sync & ~internal_dbg_halt_mode & ~mpc_debug_halt_req_sync) | (mpc_debug_run_ack_f & mpc_debug_run_req_sync) ;

   // Pins
   assign mpc_debug_halt_ack = mpc_debug_halt_ack_f;
   assign mpc_debug_run_ack = mpc_debug_run_ack_f;
   assign debug_brkpt_status = debug_brkpt_status_f;

   // DBG halt req is a pulse, fast ext int in progress has priority
   assign dbg_halt_req_held_ns = (dbg_halt_req | dbg_halt_req_held) & ext_int_freeze_d1;
   assign dbg_halt_req_final = (dbg_halt_req | dbg_halt_req_held) & ~ext_int_freeze_d1;

   // combine MPC and DBG halt requests
   assign debug_halt_req = (dbg_halt_req_final | mpc_debug_halt_req_sync | (reset_delayed & ~mpc_reset_run_req)) & ~internal_dbg_halt_mode_f & ~ext_int_freeze_d1;

   assign debug_resume_req = ~debug_resume_req_f &  // squash back to back resumes
                             ((mpc_run_state_ns & ~dbg_halt_state_ns) |  // MPC run req
                              (dbg_run_state_ns & ~mpc_halt_state_ns)); // dbg request is a pulse


   // HALT
   // dbg/pmu/fw requests halt, service as soon as lsu is not blocking interrupts
   assign take_halt = (debug_halt_req_f | pmu_fw_halt_req_f) & ~synchronous_flush_r & ~mret_r & ~halt_taken_f & ~dec_tlu_flush_noredir_r_d1 & ~take_reset;

   // hold after we take a halt, so we don't keep taking halts
   assign halt_taken = (dec_tlu_flush_noredir_r_d1 & ~dec_tlu_flush_pause_r_d1 & ~take_ext_int_start_d1) | (halt_taken_f & ~dbg_tlu_halted_f & ~pmu_fw_tlu_halted_f & ~interrupt_valid_r_d1);

   // After doing halt flush (RFNPC) wait until core is idle before asserting a particular halt mode
   // It takes a cycle for mb_empty to assert after a fetch, take_halt covers that cycle
   assign core_empty = force_halt |
                       (lsu_idle_any & lsu_idle_any_f & ifu_miss_state_idle & ifu_miss_state_idle_f & ~debug_halt_req & ~debug_halt_req_d1 & ~dec_div_active);

   assign dec_tlu_core_empty = core_empty;

//--------------------------------------------------------------------------------
// Debug start
//

   assign enter_debug_halt_req = (~internal_dbg_halt_mode_f & debug_halt_req) | dcsr_single_step_done_f | trigger_hit_dmode_r_d1 | ebreak_to_debug_mode_r_d1;

   // dbg halt state active from request until non-step resume
   assign internal_dbg_halt_mode = debug_halt_req_ns | (internal_dbg_halt_mode_f & ~(debug_resume_req_f & ~dcsr[DCSR_STEP]));
   // dbg halt can access csrs as long as we are not stepping
   assign allow_dbg_halt_csr_write = internal_dbg_halt_mode_f & ~dcsr_single_step_running_f;


   // hold debug_halt_req_ns high until we enter debug halt
   assign debug_halt_req_ns = enter_debug_halt_req | (debug_halt_req_f & ~dbg_tlu_halted);

   assign dbg_tlu_halted = (debug_halt_req_f & core_empty & halt_taken) | (dbg_tlu_halted_f & ~debug_resume_req_f);

   assign resume_ack_ns = (debug_resume_req_f & dbg_tlu_halted_f & dbg_run_state_ns);

   assign dcsr_single_step_done = dec_tlu_i0_valid_r & ~dec_tlu_dbg_halted & dcsr[DCSR_STEP] & ~rfpc_i0_r;

   assign dcsr_single_step_running = (debug_resume_req_f & dcsr[DCSR_STEP]) | (dcsr_single_step_running_f & ~dcsr_single_step_done_f);

   assign dbg_cmd_done_ns = dec_tlu_i0_valid_r & dec_tlu_dbg_halted;

   // used to hold off commits after an in-pipe debug mode request (triggers, DCSR)
   assign request_debug_mode_r = (trigger_hit_dmode_r | ebreak_to_debug_mode_r) | (request_debug_mode_r_d1 & ~dec_tlu_flush_lower_wb);

   assign request_debug_mode_done = (request_debug_mode_r_d1 | request_debug_mode_done_f) & ~dbg_tlu_halted_f;

    rvdffie #(18)  halt_ff (.*, .clk(free_l2clk),
                          .din({dec_tlu_flush_noredir_r, halt_taken, lsu_idle_any, ifu_miss_state_idle, dbg_tlu_halted,
                                resume_ack_ns, debug_halt_req_ns, debug_resume_req, trigger_hit_dmode_r,
                                dcsr_single_step_done, debug_halt_req, dec_tlu_wr_pause_r, dec_pause_state,
                                request_debug_mode_r, request_debug_mode_done, dcsr_single_step_running, dec_tlu_flush_pause_r,
                                dbg_halt_req_held_ns}),
                          .dout({dec_tlu_flush_noredir_r_d1, halt_taken_f, lsu_idle_any_f, ifu_miss_state_idle_f, dbg_tlu_halted_f,
                                 dec_tlu_resume_ack , debug_halt_req_f, debug_resume_req_f_raw, trigger_hit_dmode_r_d1,
                                 dcsr_single_step_done_f, debug_halt_req_d1, dec_tlu_wr_pause_r_d1, dec_pause_state_f,
                                 request_debug_mode_r_d1, request_debug_mode_done_f, dcsr_single_step_running_f, dec_tlu_flush_pause_r_d1,
                                 dbg_halt_req_held}));

   // MPC run collides with DBG halt, fix it here
   assign debug_resume_req_f = debug_resume_req_f_raw & ~dbg_halt_req;

   assign dec_tlu_debug_stall = debug_halt_req_f;
   assign dec_tlu_dbg_halted = dbg_tlu_halted_f;
   assign dec_tlu_debug_mode = internal_dbg_halt_mode_f;
   assign dec_tlu_pmu_fw_halted = pmu_fw_tlu_halted_f;

   // kill fetch redirection on flush if going to halt, or if there's a fence during db-halt
   assign dec_tlu_flush_noredir_r = take_halt | (fence_i_r & internal_dbg_halt_mode) | dec_tlu_flush_pause_r | (i0_trigger_hit_r & trigger_hit_dmode_r) | take_ext_int_start;

   assign dec_tlu_flush_extint = take_ext_int_start;

   // 1 cycle after writing the PAUSE counter, flush with noredir to idle F1-D.
   assign dec_tlu_flush_pause_r = dec_tlu_wr_pause_r_d1 & ~interrupt_valid_r & ~take_ext_int_start;

   // detect end of pause counter and rfpc
   assign pause_expired_r = ~dec_pause_state & dec_pause_state_f & ~(ext_int_ready | ce_int_ready | timer_int_ready | soft_int_ready | int_timer0_int_hold_f | int_timer1_int_hold_f | nmi_int_detected | ext_int_freeze_d1) & ~interrupt_valid_r_d1 & ~debug_halt_req_f & ~pmu_fw_halt_req_f & ~halt_taken_f;

   assign dec_tlu_flush_leak_one_r = dec_tlu_flush_lower_r  & dcsr[DCSR_STEP] & (dec_tlu_resume_ack | dcsr_single_step_running) & ~dec_tlu_flush_noredir_r;
   assign dec_tlu_flush_err_r = dec_tlu_flush_lower_r & (ic_perr_r | iccm_sbecc_r);

   // If DM attempts to access an illegal CSR, send cmd_fail back
   assign dec_dbg_cmd_done = dbg_cmd_done_ns;
   assign dec_dbg_cmd_fail = illegal_r & dec_dbg_cmd_done;


   //--------------------------------------------------------------------------------
   //--------------------------------------------------------------------------------
   // Triggers
   //
localparam MTDATA1_DMODE             = 9;
localparam MTDATA1_SEL   = 7;
localparam MTDATA1_ACTION            = 6;
localparam MTDATA1_CHAIN             = 5;
localparam MTDATA1_MATCH             = 4;
localparam MTDATA1_M_ENABLED         = 3;
localparam MTDATA1_EXE   = 2;
localparam MTDATA1_ST    = 1;
localparam MTDATA1_LD    = 0;

   // Prioritize trigger hits with other exceptions.
   //
   // Trigger should have highest priority except:
   // - trigger is an execute-data and there is an inst_access exception (lsu triggers won't fire, inst. is nop'd by decode)
   // - trigger is a store-data and there is a lsu_acc_exc or lsu_ma_exc.
   assign trigger_execute[3:0] = {mtdata1_t3[MTDATA1_EXE], mtdata1_t2[MTDATA1_EXE], mtdata1_t1[MTDATA1_EXE], mtdata1_t0[MTDATA1_EXE]};
   assign trigger_data[3:0] = {mtdata1_t3[MTDATA1_SEL], mtdata1_t2[MTDATA1_SEL], mtdata1_t1[MTDATA1_SEL], mtdata1_t0[MTDATA1_SEL]};
   assign trigger_store[3:0] = {mtdata1_t3[MTDATA1_ST], mtdata1_t2[MTDATA1_ST], mtdata1_t1[MTDATA1_ST], mtdata1_t0[MTDATA1_ST]};

   // MSTATUS[MIE] needs to be on to take triggers unless the action is trigger to debug mode.
   assign trigger_enabled[3:0] = {(mtdata1_t3[MTDATA1_ACTION] | mstatus[MSTATUS_MIE]) & mtdata1_t3[MTDATA1_M_ENABLED],
                                  (mtdata1_t2[MTDATA1_ACTION] | mstatus[MSTATUS_MIE]) & mtdata1_t2[MTDATA1_M_ENABLED],
                                  (mtdata1_t1[MTDATA1_ACTION] | mstatus[MSTATUS_MIE]) & mtdata1_t1[MTDATA1_M_ENABLED],
                                  (mtdata1_t0[MTDATA1_ACTION] | mstatus[MSTATUS_MIE]) & mtdata1_t0[MTDATA1_M_ENABLED]};

   // iside exceptions are always in i0
   assign i0_iside_trigger_has_pri_r[3:0]  = ~( (trigger_execute[3:0] & trigger_data[3:0] & {4{inst_acc_r_raw}}) | // exe-data with inst_acc
                                                ({4{exu_i0_br_error_r | exu_i0_br_start_error_r}}));               // branch error in i0

   // lsu excs have to line up with their respective triggers since the lsu op can be i0
   assign i0_lsu_trigger_has_pri_r[3:0] = ~(trigger_store[3:0] & trigger_data[3:0] & {4{lsu_i0_exc_r_raw}});

   // trigger hits have to be eval'd to cancel side effect lsu ops even though the pipe is already frozen
   assign i0_trigger_eval_r = dec_tlu_i0_valid_r;

   assign i0trigger_qual_r[3:0] = {4{i0_trigger_eval_r}} & dec_tlu_packet_r.i0trigger[3:0] & i0_iside_trigger_has_pri_r[3:0] & i0_lsu_trigger_has_pri_r[3:0] & trigger_enabled[3:0];

   // Qual trigger hits
   assign i0_trigger_r[3:0] = ~{4{dec_tlu_flush_lower_wb | dec_tlu_dbg_halted}} & i0trigger_qual_r[3:0];

   // chaining can mask raw trigger info
   assign i0_trigger_chain_masked_r[3:0]  = {i0_trigger_r[3] & (~mtdata1_t2[MTDATA1_CHAIN] | i0_trigger_r[2]),
                                             i0_trigger_r[2] & (~mtdata1_t2[MTDATA1_CHAIN] | i0_trigger_r[3]),
                                             i0_trigger_r[1] & (~mtdata1_t0[MTDATA1_CHAIN] | i0_trigger_r[0]),
                                             i0_trigger_r[0] & (~mtdata1_t0[MTDATA1_CHAIN] | i0_trigger_r[1])};

   // This is the highest priority by this point.
   assign i0_trigger_hit_raw_r = |i0_trigger_chain_masked_r[3:0];

   assign i0_trigger_hit_r = i0_trigger_hit_raw_r;

   // Actions include breakpoint, or dmode. Dmode is only possible if the DMODE bit is set.
   // Otherwise, take a breakpoint.
   assign trigger_action[3:0] = {mtdata1_t3[MTDATA1_ACTION] & mtdata1_t3[MTDATA1_DMODE],
                                 mtdata1_t2[MTDATA1_ACTION] & mtdata1_t2[MTDATA1_DMODE] & ~mtdata1_t2[MTDATA1_CHAIN],
                                 mtdata1_t1[MTDATA1_ACTION] & mtdata1_t1[MTDATA1_DMODE],
                                 mtdata1_t0[MTDATA1_ACTION] & mtdata1_t0[MTDATA1_DMODE] & ~mtdata1_t0[MTDATA1_CHAIN]};

   // this is needed to set the HIT bit in the triggers
   assign update_hit_bit_r[3:0] = ({4{|i0_trigger_r[3:0] & ~rfpc_i0_r}} & {i0_trigger_chain_masked_r[3], i0_trigger_r[2], i0_trigger_chain_masked_r[1], i0_trigger_r[0]});

   // action, 1 means dmode. Simultaneous triggers with at least 1 set for dmode force entire action to dmode.
   assign i0_trigger_action_r = |(i0_trigger_chain_masked_r[3:0] & trigger_action[3:0]);

   assign trigger_hit_dmode_r = (i0_trigger_hit_r & i0_trigger_action_r);

   assign mepc_trigger_hit_sel_pc_r = i0_trigger_hit_r & ~trigger_hit_dmode_r;


//
// Debug end
//--------------------------------------------------------------------------------

   //----------------------------------------------------------------------
   //
   // Commit
   //
   //----------------------------------------------------------------------



   //--------------------------------------------------------------------------------
   // External halt (not debug halt)
   // - Fully interlocked handshake
   // i_cpu_halt_req  ____|--------------|_______________
   // core_empty      ---------------|___________
   // o_cpu_halt_ack  _________________|----|__________
   // o_cpu_halt_status _______________|---------------------|_________
   // i_cpu_run_req                              ______|----------|____
   // o_cpu_run_ack                              ____________|------|________
   //


   // debug mode has priority, ignore PMU/FW halt/run while in debug mode
   assign i_cpu_halt_req_sync_qual = i_cpu_halt_req_sync & ~dec_tlu_debug_mode & ~ext_int_freeze_d1;
   assign i_cpu_run_req_sync_qual = i_cpu_run_req_sync & ~dec_tlu_debug_mode & pmu_fw_tlu_halted_f & ~ext_int_freeze_d1;

   rvdffie #(10) exthaltff (.*, .clk(free_l2clk), .din({i_cpu_halt_req_sync_qual, i_cpu_run_req_sync_qual,   cpu_halt_status,
                                                   cpu_halt_ack,   cpu_run_ack, internal_pmu_fw_halt_mode,
                                                   pmu_fw_halt_req_ns, pmu_fw_tlu_halted,
                                                   int_timer0_int_hold, int_timer1_int_hold}),
                                            .dout({i_cpu_halt_req_d1,        i_cpu_run_req_d1_raw,      o_cpu_halt_status,
                                                   o_cpu_halt_ack, o_cpu_run_ack, internal_pmu_fw_halt_mode_f,
                                                   pmu_fw_halt_req_f, pmu_fw_tlu_halted_f,
                                                   int_timer0_int_hold_f, int_timer1_int_hold_f}));

   // only happens if we aren't in dgb_halt
   assign ext_halt_pulse = i_cpu_halt_req_sync_qual & ~i_cpu_halt_req_d1;

   assign enter_pmu_fw_halt_req =  ext_halt_pulse | fw_halt_req;

   assign pmu_fw_halt_req_ns = (enter_pmu_fw_halt_req | (pmu_fw_halt_req_f & ~pmu_fw_tlu_halted)) & ~debug_halt_req_f;

   assign internal_pmu_fw_halt_mode = pmu_fw_halt_req_ns | (internal_pmu_fw_halt_mode_f & ~i_cpu_run_req_d1 & ~debug_halt_req_f);

   // debug halt has priority
   assign pmu_fw_tlu_halted = ((pmu_fw_halt_req_f & core_empty & halt_taken & ~enter_debug_halt_req) | (pmu_fw_tlu_halted_f & ~i_cpu_run_req_d1)) & ~debug_halt_req_f;

   assign cpu_halt_ack = (i_cpu_halt_req_d1 & pmu_fw_tlu_halted_f) | (o_cpu_halt_ack & i_cpu_halt_req_sync);
   assign cpu_halt_status = (pmu_fw_tlu_halted_f & ~i_cpu_run_req_d1) | (o_cpu_halt_status & ~i_cpu_run_req_d1 & ~internal_dbg_halt_mode_f);
   assign cpu_run_ack = (~pmu_fw_tlu_halted_f & i_cpu_run_req_sync) | (o_cpu_halt_status & i_cpu_run_req_d1_raw) | (o_cpu_run_ack & i_cpu_run_req_sync);
   assign debug_mode_status = internal_dbg_halt_mode_f;
   assign o_debug_mode_status = debug_mode_status;

`ifdef RV_ASSERT_ON
  assert_commit_while_halted: assert #0 (~(tlu_i0_commit_cmt  & o_cpu_halt_status)) else $display("ERROR: Commiting while cpu_halt_status asserted!");
  assert_flush_while_fastint: assert #0 (~((take_ext_int_start_d1 | take_ext_int_start_d2) & dec_tlu_flush_lower_r)) else $display("ERROR: TLU Flushing inside fast interrupt procedure!");
`endif

   // high priority interrupts can wakeup from external halt, so can unmasked timer interrupts
   assign i_cpu_run_req_d1 = i_cpu_run_req_d1_raw | ((nmi_int_detected | timer_int_ready | soft_int_ready | int_timer0_int_hold_f | int_timer1_int_hold_f | (mhwakeup & mhwakeup_ready)) & o_cpu_halt_status & ~i_cpu_halt_req_d1);

   //--------------------------------------------------------------------------------
   //--------------------------------------------------------------------------------

   assign lsu_single_ecc_error_r = lsu_single_ecc_error_incr;

   assign lsu_error_pkt_addr_r[31:0] = lsu_error_pkt_r.addr[31:0];


   assign lsu_exc_valid_r_raw = lsu_error_pkt_r.exc_valid & ~dec_tlu_flush_lower_wb;

   assign lsu_i0_exc_r_raw =  lsu_error_pkt_r.exc_valid;

   assign lsu_i0_exc_r = lsu_i0_exc_r_raw & lsu_exc_valid_r_raw & ~i0_trigger_hit_r & ~rfpc_i0_r;

   assign lsu_exc_valid_r = lsu_i0_exc_r;

   assign lsu_exc_ma_r  =  lsu_i0_exc_r & ~lsu_error_pkt_r.exc_type;
   assign lsu_exc_acc_r =  lsu_i0_exc_r & lsu_error_pkt_r.exc_type;
   assign lsu_exc_st_r  =  lsu_i0_exc_r & lsu_error_pkt_r.inst_type;

   // Single bit ECC errors on loads are RFNPC corrected, with the corrected data written to the GPR.
   // LSU turns the load into a store and patches the data in the DCCM
   assign lsu_i0_rfnpc_r = dec_tlu_i0_valid_r & ~i0_trigger_hit_r &
                           (~lsu_error_pkt_r.inst_type & lsu_error_pkt_r.single_ecc_error);

   //  Final commit valids
`ifdef RV_USER_MODE
   assign tlu_i0_commit_cmt = dec_tlu_i0_valid_r &
                              ~rfpc_i0_r &
                              ~lsu_i0_exc_r &
                              ~inst_acc_r &
                              ~dec_tlu_dbg_halted &
                              ~request_debug_mode_r_d1 &
                              ~i0_trigger_hit_r &
                              ~csr_acc_r;
`else
   assign tlu_i0_commit_cmt = dec_tlu_i0_valid_r &
                              ~rfpc_i0_r &
                              ~lsu_i0_exc_r &
                              ~inst_acc_r &
                              ~dec_tlu_dbg_halted &
                              ~request_debug_mode_r_d1 &
                              ~i0_trigger_hit_r;
`endif

   // unified place to manage the killing of arch state writebacks
`ifdef RV_USER_MODE
   assign tlu_i0_kill_writeb_r = rfpc_i0_r | lsu_i0_exc_r | inst_acc_r | (illegal_r & dec_tlu_dbg_halted) | i0_trigger_hit_r | csr_acc_r;
`else
   assign tlu_i0_kill_writeb_r = rfpc_i0_r | lsu_i0_exc_r | inst_acc_r | (illegal_r & dec_tlu_dbg_halted) | i0_trigger_hit_r;
`endif
   assign dec_tlu_i0_commit_cmt = tlu_i0_commit_cmt;


   // refetch PC, microarch flush
   // ic errors only in pipe0
   assign rfpc_i0_r =  ((dec_tlu_i0_valid_r & ~tlu_flush_lower_r_d1 & (exu_i0_br_error_r | exu_i0_br_start_error_r)) | // inst commit with rfpc
                        ((ic_perr_r | iccm_sbecc_r) & ~ext_int_freeze_d1)) & // ic/iccm without inst commit
                       ~i0_trigger_hit_r & // unless there's a trigger. Err signal to ic/iccm will assert anyway to clear the error.
                       ~lsu_i0_rfnpc_r;

   // From the indication of a iccm single bit error until the first commit or flush, maintain a repair state. In the repair state, rfnpc i0 commits.
   assign iccm_repair_state_ns = iccm_sbecc_r | (iccm_repair_state_d1 & ~dec_tlu_flush_lower_r);


   localparam MCPC          = 12'h7c2;

   // this is a flush of last resort, meaning only assert it if there is no other flush happening.
   assign iccm_repair_state_rfnpc = tlu_i0_commit_cmt & iccm_repair_state_d1 &
                                    ~(ebreak_r | ecall_r | mret_r | take_reset | illegal_r | (dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCPC)));

if(pt.BTB_ENABLE==1) begin
   // go ahead and repair the branch error on other flushes, doesn't have to be the rfpc flush
   assign dec_tlu_br0_error_r = exu_i0_br_error_r & dec_tlu_i0_valid_r & ~tlu_flush_lower_r_d1;
   assign dec_tlu_br0_start_error_r = exu_i0_br_start_error_r & dec_tlu_i0_valid_r & ~tlu_flush_lower_r_d1;
   assign dec_tlu_br0_v_r = exu_i0_br_valid_r & dec_tlu_i0_valid_r & ~tlu_flush_lower_r_d1 & (~exu_i0_br_mp_r | ~exu_pmu_i0_br_ataken);


   assign dec_tlu_br0_r_pkt.hist[1:0] = exu_i0_br_hist_r[1:0];
   assign dec_tlu_br0_r_pkt.br_error = dec_tlu_br0_error_r;
   assign dec_tlu_br0_r_pkt.br_start_error = dec_tlu_br0_start_error_r;
   assign dec_tlu_br0_r_pkt.valid = dec_tlu_br0_v_r;
   assign dec_tlu_br0_r_pkt.way = exu_i0_br_way_r;
   assign dec_tlu_br0_r_pkt.middle = exu_i0_br_middle_r;
end // if (pt.BTB_ENABLE==1)
else begin
   assign dec_tlu_br0_error_r = '0;
   assign dec_tlu_br0_start_error_r = '0;
   assign dec_tlu_br0_v_r = '0;
   assign dec_tlu_br0_r_pkt  = '0;
end // else: !if(pt.BTB_ENABLE==1)


   // only expect these in pipe 0
   assign       ebreak_r     =  (dec_tlu_packet_r.pmu_i0_itype == EBREAK)  & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~dcsr[DCSR_EBREAKM] & ~rfpc_i0_r;
   assign       ecall_r      =  (dec_tlu_packet_r.pmu_i0_itype == ECALL)   & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
`ifdef RV_USER_MODE
   assign       illegal_r    =  (((dec_tlu_packet_r.pmu_i0_itype == MRET) &  priv_mode) | ~dec_tlu_packet_r.legal) & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
   assign       mret_r       =  ( (dec_tlu_packet_r.pmu_i0_itype == MRET) & ~priv_mode                           ) & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
`else
   assign       illegal_r    =  ~dec_tlu_packet_r.legal   & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
   assign       mret_r       =  (dec_tlu_packet_r.pmu_i0_itype == MRET)    & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
`endif
   // fence_i includes debug only fence_i's
   assign       fence_i_r    =  (dec_tlu_packet_r.fence_i & dec_tlu_i0_valid_r & ~i0_trigger_hit_r) & ~rfpc_i0_r;
   assign       ic_perr_r    =  ifu_ic_error_start_f & ~ext_int_freeze_d1 & (~internal_dbg_halt_mode_f | dcsr_single_step_running) & ~internal_pmu_fw_halt_mode_f;
   assign       iccm_sbecc_r =  ifu_iccm_rd_ecc_single_err_f & ~ext_int_freeze_d1 & (~internal_dbg_halt_mode_f | dcsr_single_step_running) & ~internal_pmu_fw_halt_mode_f;
   assign       inst_acc_r_raw  =  dec_tlu_packet_r.icaf & dec_tlu_i0_valid_r;
   assign       inst_acc_r = inst_acc_r_raw & ~rfpc_i0_r & ~i0_trigger_hit_r;
   assign       inst_acc_second_r = dec_tlu_packet_r.icaf_second;

   assign       ebreak_to_debug_mode_r = (dec_tlu_packet_r.pmu_i0_itype == EBREAK)  & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & dcsr[DCSR_EBREAKM] & ~rfpc_i0_r;

   rvdff #(1)  exctype_wb_ff (.*, .clk(e4e5_clk),
                                .din (ebreak_to_debug_mode_r   ),
                                .dout(ebreak_to_debug_mode_r_d1));

   assign dec_tlu_fence_i_r = fence_i_r;

`ifdef RV_USER_MODE

   // CSR access
   // Address bits 9:8 == 2'b00 indicate unprivileged / user-level CSR
   assign csr_wr_usr_r = ~|dec_csr_wraddr_r[9:8];
   assign csr_rd_usr_r = ~|dec_csr_rdaddr_r[9:8];

   // CSR access error
   // cycle and instret CSR unprivileged access is controller by bits in mcounteren CSR
   logic csr_wr_acc_r;
   logic csr_rd_acc_r;

   assign csr_wr_acc_r = csr_wr_usr_r & (
                             ((dec_csr_wraddr_r[11:0] == CYCLEL)   & mcounteren[MCOUNTEREN_CY]) |
                             ((dec_csr_wraddr_r[11:0] == CYCLEH)   & mcounteren[MCOUNTEREN_CY]) |
                             ((dec_csr_wraddr_r[11:0] == INSTRETL) & mcounteren[MCOUNTEREN_IR]) |
                             ((dec_csr_wraddr_r[11:0] == INSTRETH) & mcounteren[MCOUNTEREN_IR]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC3)    & mcounteren[MCOUNTEREN_HPM3]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC3H)   & mcounteren[MCOUNTEREN_HPM3]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC4)    & mcounteren[MCOUNTEREN_HPM4]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC4H)   & mcounteren[MCOUNTEREN_HPM4]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC5)    & mcounteren[MCOUNTEREN_HPM5]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC5H)   & mcounteren[MCOUNTEREN_HPM5]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC6)    & mcounteren[MCOUNTEREN_HPM6]) |
                             ((dec_csr_wraddr_r[11:0] == HPMC6H)   & mcounteren[MCOUNTEREN_HPM6]));

   assign csr_rd_acc_r = csr_rd_usr_r & (
                             ((dec_csr_rdaddr_r[11:0] == CYCLEL)   & mcounteren[MCOUNTEREN_CY]) |
                             ((dec_csr_rdaddr_r[11:0] == CYCLEH)   & mcounteren[MCOUNTEREN_CY]) |
                             ((dec_csr_rdaddr_r[11:0] == INSTRETL) & mcounteren[MCOUNTEREN_IR]) |
                             ((dec_csr_rdaddr_r[11:0] == INSTRETH) & mcounteren[MCOUNTEREN_IR]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC3)    & mcounteren[MCOUNTEREN_HPM3]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC3H)   & mcounteren[MCOUNTEREN_HPM3]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC4)    & mcounteren[MCOUNTEREN_HPM4]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC4H)   & mcounteren[MCOUNTEREN_HPM4]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC5)    & mcounteren[MCOUNTEREN_HPM5]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC5H)   & mcounteren[MCOUNTEREN_HPM5]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC6)    & mcounteren[MCOUNTEREN_HPM6]) |
                             ((dec_csr_rdaddr_r[11:0] == HPMC6H)   & mcounteren[MCOUNTEREN_HPM6]));

   assign csr_acc_r = priv_mode & dec_tlu_i0_valid_r & ~i0_trigger_hit_r & ~rfpc_i0_r & (
                        (dec_tlu_packet_r.pmu_i0_itype == CSRREAD)  & ~csr_rd_acc_r |
                        (dec_tlu_packet_r.pmu_i0_itype == CSRWRITE) & ~csr_wr_acc_r |
                        (dec_tlu_packet_r.pmu_i0_itype == CSRRW)    & ~csr_rd_acc_r & ~csr_wr_acc_r);

`endif

   //
   // Exceptions
   //
   // - MEPC <- PC
   // - PC <- MTVEC, assert flush_lower
   // - MCAUSE <- cause
   // - MSCAUSE <- secondary cause
   // - MTVAL <-
   // - MPIE <- MIE
   // - MIE <- 0
   //
`ifdef RV_USER_MODE
   assign i0_exception_valid_r = (ebreak_r | ecall_r | illegal_r | inst_acc_r | csr_acc_r) & ~rfpc_i0_r & ~dec_tlu_dbg_halted;
`else
   assign i0_exception_valid_r = (ebreak_r | ecall_r | illegal_r | inst_acc_r) & ~rfpc_i0_r & ~dec_tlu_dbg_halted;
`endif

   // Cause:
   //
   // 0x2 : illegal
   // 0x3 : breakpoint
   // 0x8 : Environment call U-mode (if U-mode is enabled)
   // 0xb : Environment call M-mode


   assign exc_cause_r[4:0] =  ( ({5{take_ext_int}}         & 5'h0b) |
                                ({5{take_timer_int}}       & 5'h07) |
                                ({5{take_soft_int}}        & 5'h03) |
                                ({5{take_int_timer0_int}}  & 5'h1d) |
                                ({5{take_int_timer1_int}}  & 5'h1c) |
                                ({5{take_ce_int}}          & 5'h1e) |
`ifdef RV_USER_MODE
                                ({5{illegal_r| csr_acc_r}} & 5'h02) |
                                ({5{ecall_r & priv_mode}}  & 5'h08) |
                                ({5{ecall_r & ~priv_mode}} & 5'h0b) |
`else
                                ({5{illegal_r}}            & 5'h02) |
                                ({5{ecall_r}}              & 5'h0b) |
`endif
                                ({5{inst_acc_r}}           & 5'h01) |
                                ({5{ebreak_r | i0_trigger_hit_r}}   & 5'h03) |
                                ({5{lsu_exc_ma_r & ~lsu_exc_st_r}}  & 5'h04) |
                                ({5{lsu_exc_acc_r & ~lsu_exc_st_r}} & 5'h05) |
                                ({5{lsu_exc_ma_r & lsu_exc_st_r}}   & 5'h06) |
                                ({5{lsu_exc_acc_r & lsu_exc_st_r}}  & 5'h07)
                                ) & ~{5{take_nmi}};

   //
   // Interrupts
   //
   // exceptions that are committed have already happened and will cause an int at E4 to wait a cycle
   // or more if MSTATUS[MIE] is cleared.
   //
   // -in priority order, highest to lowest
   // -single cycle window where a csr write to MIE/MSTATUS is at E4 when the other conditions for externals are met.
   //  Hold off externals for a cycle to make sure we are consistent with what was just written
   assign mhwakeup_ready =  ~dec_csr_stall_int_ff & mstatus_mie_ns & mip[MIP_MEIP]   & mie_ns[MIE_MEIE];
   assign ext_int_ready   = ~dec_csr_stall_int_ff & mstatus_mie_ns & mip[MIP_MEIP]   & mie_ns[MIE_MEIE] & ~ignore_ext_int_due_to_lsu_stall;
   assign ce_int_ready    = ~dec_csr_stall_int_ff & mstatus_mie_ns & mip[MIP_MCEIP]  & mie_ns[MIE_MCEIE];
   assign soft_int_ready  = ~dec_csr_stall_int_ff & mstatus_mie_ns & mip[MIP_MSIP]   & mie_ns[MIE_MSIE];
   assign timer_int_ready = ~dec_csr_stall_int_ff & mstatus_mie_ns & mip[MIP_MTIP]   & mie_ns[MIE_MTIE];

   // MIP for internal timers pulses for 1 clock, resets the timer counter. Mip won't hold past the various stall conditions.
   assign int_timer0_int_possible = mstatus_mie_ns & mie_ns[MIE_MITIE0];
   assign int_timer0_int_ready = mip[MIP_MITIP0] & int_timer0_int_possible;
   assign int_timer1_int_possible = mstatus_mie_ns & mie_ns[MIE_MITIE1];
   assign int_timer1_int_ready = mip[MIP_MITIP1] & int_timer1_int_possible;

   // Internal timers pulse and reset. If core is PMU/FW halted, the pulse will cause an exit from halt, but won't stick around
   // Make it sticky, also for 1 cycle stall conditions.
   assign int_timer_stalled = dec_csr_stall_int_ff | synchronous_flush_r | exc_or_int_valid_r_d1 | mret_r;

   assign int_timer0_int_hold = (int_timer0_int_ready & (pmu_fw_tlu_halted_f | int_timer_stalled)) | (int_timer0_int_possible & int_timer0_int_hold_f & ~interrupt_valid_r & ~take_ext_int_start & ~internal_dbg_halt_mode_f);
   assign int_timer1_int_hold = (int_timer1_int_ready & (pmu_fw_tlu_halted_f | int_timer_stalled)) | (int_timer1_int_possible & int_timer1_int_hold_f & ~interrupt_valid_r & ~take_ext_int_start & ~internal_dbg_halt_mode_f);


   assign internal_dbg_halt_timers = internal_dbg_halt_mode_f & ~dcsr_single_step_running;


   assign block_interrupts = ( (internal_dbg_halt_mode & (~dcsr_single_step_running | dec_tlu_i0_valid_r)) | // No ints in db-halt unless we are single stepping
                               internal_pmu_fw_halt_mode | i_cpu_halt_req_d1 |// No ints in PMU/FW halt. First we exit halt
                               take_nmi | // NMI is top priority
                               ebreak_to_debug_mode_r | // Heading to debug mode, hold off ints
                               synchronous_flush_r | // exception flush this cycle
                               exc_or_int_valid_r_d1 | // ext/int past cycle (need time for MIE to update)
                               mret_r |    // mret in progress, for cases were ISR enables ints before mret
                               ext_int_freeze_d1 // Fast interrupt in progress (optional)
                               );


if (pt.FAST_INTERRUPT_REDIRECT) begin


   assign take_ext_int_start = ext_int_ready & ~block_interrupts;

   assign ext_int_freeze = take_ext_int_start | take_ext_int_start_d1 | take_ext_int_start_d2 | take_ext_int_start_d3;
   assign take_ext_int = take_ext_int_start_d3 & ~|lsu_fir_error[1:0];
   assign fast_int_meicpct = csr_meicpct & dec_csr_any_unq_d;  // MEICPCT becomes illegal if fast ints are enabled

   assign ignore_ext_int_due_to_lsu_stall = lsu_fastint_stall_any;
end
else begin
   assign take_ext_int_start = 1'b0;
   assign ext_int_freeze = 1'b0;
   assign ext_int_freeze_d1 = 1'b0;
   assign take_ext_int_start_d1 = 1'b0;
   assign take_ext_int_start_d2 = 1'b0;
   assign take_ext_int_start_d3 = 1'b0;
   assign fast_int_meicpct = 1'b0;
   assign ignore_ext_int_due_to_lsu_stall = 1'b0;

   assign take_ext_int = ext_int_ready & ~block_interrupts;
end

   assign take_ce_int  = ce_int_ready & ~ext_int_ready & ~block_interrupts;
   assign take_soft_int = soft_int_ready & ~ext_int_ready & ~ce_int_ready & ~block_interrupts;
   assign take_timer_int = timer_int_ready & ~soft_int_ready & ~ext_int_ready & ~ce_int_ready & ~block_interrupts;
   assign take_int_timer0_int = (int_timer0_int_ready | int_timer0_int_hold_f) & int_timer0_int_possible & ~dec_csr_stall_int_ff &
                                ~timer_int_ready & ~soft_int_ready & ~ext_int_ready & ~ce_int_ready & ~block_interrupts;
   assign take_int_timer1_int = (int_timer1_int_ready | int_timer1_int_hold_f) & int_timer1_int_possible & ~dec_csr_stall_int_ff &
                                ~(int_timer0_int_ready | int_timer0_int_hold_f) & ~timer_int_ready & ~soft_int_ready & ~ext_int_ready & ~ce_int_ready & ~block_interrupts;

   assign take_reset = reset_delayed & mpc_reset_run_req;
   assign take_nmi = nmi_int_detected & ~internal_pmu_fw_halt_mode & (~internal_dbg_halt_mode | (dcsr_single_step_running_f & dcsr[DCSR_STEPIE] & ~dec_tlu_i0_valid_r & ~dcsr_single_step_done_f)) &
                     ~synchronous_flush_r & ~mret_r & ~take_reset & ~ebreak_to_debug_mode_r & (~ext_int_freeze_d1 | (take_ext_int_start_d3 & |lsu_fir_error[1:0]));

   assign interrupt_valid_r = take_ext_int | take_timer_int | take_soft_int | take_nmi | take_ce_int | take_int_timer0_int | take_int_timer1_int;


   // Compute interrupt path:
   // If vectored async is set in mtvec, flush path for interrupts is MTVEC + (4 * CAUSE);
   assign vectored_path[31:1]  = {mtvec[30:1], 1'b0} + {25'b0, exc_cause_r[4:0], 1'b0};
   assign interrupt_path[31:1] = take_nmi ? nmi_vec[31:1] : ((mtvec[0] == 1'b1) ? vectored_path[31:1] : {mtvec[30:1], 1'b0});

   assign sel_npc_r  = lsu_i0_rfnpc_r | fence_i_r | iccm_repair_state_rfnpc | (i_cpu_run_req_d1 & ~interrupt_valid_r) | (rfpc_i0_r & ~dec_tlu_i0_valid_r);
   assign sel_npc_resume = (i_cpu_run_req_d1 & pmu_fw_tlu_halted_f) | pause_expired_r;

   assign sel_fir_addr = take_ext_int_start_d3 & ~|lsu_fir_error[1:0];

   assign synchronous_flush_r  = i0_exception_valid_r | // exception
                                 rfpc_i0_r | // rfpc
                                 lsu_exc_valid_r |  // lsu exception in either pipe 0 or pipe 1
                                 fence_i_r |  // fence, a rfnpc
                                 lsu_i0_rfnpc_r | // lsu dccm sb ecc
                                 iccm_repair_state_rfnpc | // Iccm sb ecc
                                 debug_resume_req_f | // resume from debug halt, fetch the dpc
                                 sel_npc_resume |  // resume from pmu/fw halt, or from pause and fetch the NPC
                                 dec_tlu_wr_pause_r_d1 | // flush at start of pause
                                 i0_trigger_hit_r; // trigger hit, ebreak or goto debug mode

   assign tlu_flush_lower_r = interrupt_valid_r | mret_r | synchronous_flush_r | take_halt | take_reset | take_ext_int_start;

   assign tlu_flush_path_r[31:1] = take_reset ? rst_vec[31:1] :

                                    ( ({31{sel_fir_addr}} & lsu_fir_addr[31:1]) |
                                      ({31{~take_nmi & sel_npc_r}} & npc_r[31:1]) |
                                      ({31{~take_nmi & rfpc_i0_r & dec_tlu_i0_valid_r & ~sel_npc_r}} & dec_tlu_i0_pc_r[31:1]) |
                                      ({31{interrupt_valid_r & ~sel_fir_addr}} & interrupt_path[31:1]) |
                                      ({31{(i0_exception_valid_r | lsu_exc_valid_r |
                                            (i0_trigger_hit_r & ~trigger_hit_dmode_r)) & ~interrupt_valid_r & ~sel_fir_addr}} & {mtvec[30:1],1'b0}) |
                                      ({31{~take_nmi & mret_r}} & mepc[31:1]) |
                                      ({31{~take_nmi & debug_resume_req_f}} & dpc[31:1]) |
                                      ({31{~take_nmi & sel_npc_resume}} & npc_r_d1[31:1]) );

   rvdffpcie #(31)  flush_lower_ff (.*, .en(tlu_flush_lower_r),
                                 .din({tlu_flush_path_r[31:1]}),
                                 .dout({tlu_flush_path_r_d1[31:1]}));

   assign dec_tlu_flush_lower_wb = tlu_flush_lower_r_d1;
   assign dec_tlu_flush_lower_r = tlu_flush_lower_r;
   assign dec_tlu_flush_path_r[31:1] = tlu_flush_path_r[31:1];


   // this is used to capture mepc, etc.
   assign exc_or_int_valid_r = lsu_exc_valid_r | i0_exception_valid_r | interrupt_valid_r | (i0_trigger_hit_r & ~trigger_hit_dmode_r);


   rvdffie #(12)  excinfo_wb_ff (.*,
                                 .din({interrupt_valid_r, i0_exception_valid_r, exc_or_int_valid_r,
                                       exc_cause_r[4:0], tlu_i0_commit_cmt & ~illegal_r, i0_trigger_hit_r,
                                       take_nmi, pause_expired_r }),
                                 .dout({interrupt_valid_r_d1, i0_exception_valid_r_d1, exc_or_int_valid_r_d1,
                                        exc_cause_wb[4:0], i0_valid_wb, trigger_hit_r_d1,
                                        take_nmi_r_d1, pause_expired_wb}));
`ifdef RV_USER_MODE

   //
   // Privilege mode
   //
   assign priv_mode_ns = (mret_r & mstatus[MSTATUS_MPP]) |
                         (exc_or_int_valid_r & 1'b0 ) |
                         ((~mret_r & ~exc_or_int_valid_r) & priv_mode);

   rvdff #(1) priv_ff (
        .clk    (free_l2clk),
        .rst_l  (rst_l),
        .din    (priv_mode_ns),
        .dout   (priv_mode)
   );

`endif

   //----------------------------------------------------------------------
   //
   // CSRs
   //
   //----------------------------------------------------------------------

   // ----------------------------------------------------------------------
   // MSTATUS (RW)
   // [17]    MPRV : Modify PRiVilege (if enabled in config)
   // [12:11] MPP  : Prior priv level, either 2'b11 (machine) or 2'b00 (user)
   // [7]     MPIE : Int enable previous [1]
   // [3]     MIE  : Int enable          [0]


   //When executing a MRET instruction, supposing MPP holds the value 3, MIE
   //is set to MPIE; the privilege mode is changed to 3; MPIE is set to 1; and MPP is set to 3
`ifdef RV_USER_MODE
   assign dec_csr_wen_r_mod = dec_csr_wen_r & ~i0_trigger_hit_r & ~rfpc_i0_r & ~csr_acc_r;
`else
   assign dec_csr_wen_r_mod = dec_csr_wen_r & ~i0_trigger_hit_r & ~rfpc_i0_r;
`endif

   assign wr_mstatus_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MSTATUS);

   // set this even if we don't go to fwhalt due to debug halt. We committed the inst, so ...
   assign set_mie_pmu_fw_halt = ~mpmc_b_ns[1] & fw_halt_req;

`ifdef RV_USER_MODE
   // mstatus[2] / mstatus_ns[2] actually stores inverse of the MPP field !
   assign mstatus_ns[3:0] = ( ({4{~wr_mstatus_r & exc_or_int_valid_r}} & {mstatus[MSTATUS_MPRV], priv_mode, mstatus[MSTATUS_MIE], 1'b0}) |
                              ({4{ wr_mstatus_r & exc_or_int_valid_r}} & {mstatus[MSTATUS_MPRV], priv_mode, dec_csr_wrdata_r[3],  1'b0}) |
                              ({4{mret_r & ~exc_or_int_valid_r}}       & {mstatus[MSTATUS_MPRV] & ~mstatus[MSTATUS_MPP], 1'b1, 1'b1, mstatus[MSTATUS_MPIE]}) |
                              ({4{set_mie_pmu_fw_halt}}                & {mstatus[3:2], mstatus[MSTATUS_MPIE], 1'b1}) |
                              ({4{wr_mstatus_r & ~exc_or_int_valid_r}} & {dec_csr_wrdata_r[17], ~dec_csr_wrdata_r[12], dec_csr_wrdata_r[7], dec_csr_wrdata_r[3]}) |
                              ({4{~wr_mstatus_r & ~exc_or_int_valid_r  & ~mret_r & ~set_mie_pmu_fw_halt}} & mstatus[3:0]) );

   // gate MIE if we are single stepping and DCSR[STEPIE] is off
   // in user mode machine interrupts are always enabled as per RISC-V privilege spec (chapter 3.1.6.1).
   assign mstatus_mie_ns = (priv_mode | mstatus[MSTATUS_MIE]) & (~dcsr_single_step_running_f | dcsr[DCSR_STEPIE]);

   // set effective privilege mode according to MPRV and MPP
   assign priv_mode_eff = ( mstatus[MSTATUS_MPRV] & mstatus[MSTATUS_MPP]) | // MPRV=1, use MPP
                          (~mstatus[MSTATUS_MPRV] & priv_mode);             // MPRV=0, use current operating mode

`else

   assign mstatus_ns[1:0] = ( ({2{~wr_mstatus_r & exc_or_int_valid_r}} & {mstatus[MSTATUS_MIE], 1'b0}) |
                              ({2{ wr_mstatus_r & exc_or_int_valid_r}} & {dec_csr_wrdata_r[3], 1'b0}) |
                              ({2{mret_r & ~exc_or_int_valid_r}} & {1'b1, mstatus[MSTATUS_MPIE]}) |
                              ({2{set_mie_pmu_fw_halt}} & {mstatus[MSTATUS_MPIE], 1'b1}) |
                              ({2{wr_mstatus_r & ~exc_or_int_valid_r}} & {dec_csr_wrdata_r[7], dec_csr_wrdata_r[3]}) |
                              ({2{~wr_mstatus_r & ~exc_or_int_valid_r & ~mret_r & ~set_mie_pmu_fw_halt}} & mstatus[1:0]) );

   assign mstatus_mie_ns = mstatus[MSTATUS_MIE] & (~dcsr_single_step_running_f | dcsr[DCSR_STEPIE]);

`endif

   // ----------------------------------------------------------------------
   // MTVEC (RW)
   // [31:2] BASE : Trap vector base address
   // [1] - Reserved, not implemented, reads zero
   // [0]  MODE : 0 = Direct, 1 = Asyncs are vectored to BASE + (4 * CAUSE)

   assign wr_mtvec_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTVEC);
   assign mtvec_ns[30:0] = {dec_csr_wrdata_r[31:2], dec_csr_wrdata_r[0]} ;
   rvdffe #(31)  mtvec_ff (.*, .en(wr_mtvec_r), .din(mtvec_ns[30:0]), .dout(mtvec[30:0]));

   // ----------------------------------------------------------------------
   // MIP (RW)
   //
   // [30] MCEIP  : (RO) M-Mode Correctable Error interrupt pending
   // [29] MITIP0 : (RO) M-Mode Internal Timer0 interrupt pending
   // [28] MITIP1 : (RO) M-Mode Internal Timer1 interrupt pending
   // [11] MEIP   : (RO) M-Mode external interrupt pending
   // [7]  MTIP   : (RO) M-Mode timer interrupt pending
   // [3]  MSIP   : (RO) M-Mode software interrupt pending

   assign ce_int = (mdccme_ce_req | miccme_ce_req | mice_ce_req);

   assign mip_ns[5:0] = {ce_int, dec_timer_t0_pulse, dec_timer_t1_pulse, mexintpend, timer_int_sync, soft_int_sync};

   // ----------------------------------------------------------------------
   // MIE (RW)
   // [30] MCEIE  : (RO) M-Mode Correctable Error interrupt enable
   // [29] MITIE0 : (RO) M-Mode Internal Timer0 interrupt enable
   // [28] MITIE1 : (RO) M-Mode Internal Timer1 interrupt enable
   // [11] MEIE   : (RW) M-Mode external interrupt enable
   // [7]  MTIE   : (RW) M-Mode timer interrupt enable
   // [3]  MSIE   : (RW) M-Mode software interrupt enable

   assign wr_mie_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MIE);
   assign mie_ns[5:0] = wr_mie_r ? {dec_csr_wrdata_r[30:28], dec_csr_wrdata_r[11], dec_csr_wrdata_r[7], dec_csr_wrdata_r[3]} : mie[5:0];
   rvdff #(6)  mie_ff (.*, .clk(csr_wr_clk), .din(mie_ns[5:0]), .dout(mie[5:0]));


   // ----------------------------------------------------------------------
   // MCYCLEL (RW)
   // [31:0] : Lower Cycle count

   assign kill_ebreak_count_r = ebreak_to_debug_mode_r & dcsr[DCSR_STOPC];

   assign wr_mcyclel_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCYCLEL);

   assign mcyclel_cout_in = ~(kill_ebreak_count_r | (dec_tlu_dbg_halted & dcsr[DCSR_STOPC]) | dec_tlu_pmu_fw_halted | mcountinhibit[0]);

   // split for power
   assign {mcyclela_cout, mcyclel_inc[7:0]}  = mcyclel[7:0] +  {7'b0, 1'b1};
   assign {mcyclel_cout,  mcyclel_inc[31:8]} = mcyclel[31:8] + {23'b0, mcyclela_cout};

   assign mcyclel_ns[31:0] = wr_mcyclel_r ? dec_csr_wrdata_r[31:0] : mcyclel_inc[31:0];

   rvdffe #(24) mcyclel_bff      (.*, .clk(free_l2clk), .en(wr_mcyclel_r | (mcyclela_cout & mcyclel_cout_in)),    .din(mcyclel_ns[31:8]), .dout(mcyclel[31:8]));
   rvdffe #(8)  mcyclel_aff      (.*, .clk(free_l2clk), .en(wr_mcyclel_r | mcyclel_cout_in),  .din(mcyclel_ns[7:0]),  .dout(mcyclel[7:0]));

   // ----------------------------------------------------------------------
   // MCYCLEH (RW)
   // [63:32] : Higher Cycle count
   // Chained with mcyclel. Note: mcyclel overflow due to a mcycleh write gets ignored.

   assign wr_mcycleh_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCYCLEH);

   assign mcycleh_inc[31:0] = mcycleh[31:0] + {31'b0, mcyclel_cout_f};
   assign mcycleh_ns[31:0]  = wr_mcycleh_r ? dec_csr_wrdata_r[31:0] : mcycleh_inc[31:0];

   rvdffe #(32)  mcycleh_ff (.*, .clk(free_l2clk), .en(wr_mcycleh_r | mcyclel_cout_f), .din(mcycleh_ns[31:0]), .dout(mcycleh[31:0]));

   // ----------------------------------------------------------------------
   // MINSTRETL (RW)
   // [31:0] : Lower Instruction retired count
   // From the spec "Some CSRs, such as the instructions retired counter, instret, may be modified as side effects
   // of instruction execution. In these cases, if a CSR access instruction reads a CSR, it reads the
   // value prior to the execution of the instruction. If a CSR access instruction writes a CSR, the
   // update occurs after the execution of the instruction. In particular, a value written to instret by
   // one instruction will be the value read by the following instruction (i.e., the increment of instret
   // caused by the first instruction retiring happens before the write of the new value)."

   assign i0_valid_no_ebreak_ecall_r = dec_tlu_i0_valid_r & ~(ebreak_r | ecall_r | ebreak_to_debug_mode_r | illegal_r | mcountinhibit[2]);

   assign wr_minstretl_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MINSTRETL);

   assign {minstretl_couta, minstretl_inc[7:0]} = minstretl[7:0] + {7'b0,1'b1};
   assign {minstretl_cout, minstretl_inc[31:8]} = minstretl[31:8] + {23'b0, minstretl_couta};

   assign minstret_enable = (i0_valid_no_ebreak_ecall_r & tlu_i0_commit_cmt) | wr_minstretl_r;

   assign minstretl_cout_ns = minstretl_cout & ~wr_minstreth_r & i0_valid_no_ebreak_ecall_r & ~dec_tlu_dbg_halted;

   assign minstretl_ns[31:0] = wr_minstretl_r ? dec_csr_wrdata_r[31:0] : minstretl_inc[31:0];
   rvdffe #(24)  minstretl_bff (.*, .en(wr_minstretl_r | (minstretl_couta & minstret_enable)),
                                .din(minstretl_ns[31:8]), .dout(minstretl[31:8]));
   rvdffe #(8)   minstretl_aff (.*, .en(minstret_enable),
                                .din(minstretl_ns[7:0]),  .dout(minstretl[7:0]));


   assign minstretl_read[31:0] = minstretl[31:0];
   // ----------------------------------------------------------------------
   // MINSTRETH (RW)
   // [63:32] : Higher Instret count
   // Chained with minstretl. Note: minstretl overflow due to a minstreth write gets ignored.

   assign wr_minstreth_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MINSTRETH);

   assign minstreth_inc[31:0] = minstreth[31:0] + {31'b0, minstretl_cout_f};
   assign minstreth_ns[31:0]  = wr_minstreth_r ? dec_csr_wrdata_r[31:0] : minstreth_inc[31:0];
   rvdffe #(32)  minstreth_ff (.*, .en((minstret_enable_f & minstretl_cout_f) | wr_minstreth_r), .din(minstreth_ns[31:0]), .dout(minstreth[31:0]));

   assign minstreth_read[31:0] = minstreth_inc[31:0];

   // ----------------------------------------------------------------------
   // MSCRATCH (RW)
   // [31:0] : Scratch register
   assign wr_mscratch_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MSCRATCH);

   rvdffe #(32)  mscratch_ff (.*, .en(wr_mscratch_r), .din(dec_csr_wrdata_r[31:0]), .dout(mscratch[31:0]));

   // ----------------------------------------------------------------------
   // MEPC (RW)
   // [31:1] : Exception PC

   // NPC

   assign sel_exu_npc_r = ~dec_tlu_dbg_halted & ~tlu_flush_lower_r_d1 & dec_tlu_i0_valid_r;
   assign sel_flush_npc_r = ~dec_tlu_dbg_halted & tlu_flush_lower_r_d1 & ~dec_tlu_flush_noredir_r_d1;
   assign sel_hold_npc_r = ~sel_exu_npc_r & ~sel_flush_npc_r;

   assign npc_r[31:1] =  ( ({31{sel_exu_npc_r}} & exu_npc_r[31:1]) |
                           ({31{~mpc_reset_run_req & reset_delayed}} & rst_vec[31:1]) | // init to reset vector for mpc halt on reset case
                           ({31{(sel_flush_npc_r)}} & tlu_flush_path_r_d1[31:1]) |
                           ({31{(sel_hold_npc_r)}} & npc_r_d1[31:1]) );

   rvdffpcie #(31)  npwbc_ff (.*, .en(sel_exu_npc_r | sel_flush_npc_r | reset_delayed), .din(npc_r[31:1]), .dout(npc_r_d1[31:1]));

   // PC has to be captured for exceptions and interrupts. For MRET, we could execute it and then take an
   // interrupt before the next instruction.
   assign pc0_valid_r = ~dec_tlu_dbg_halted & dec_tlu_i0_valid_r;

   assign pc_r[31:1]  = ( ({31{ pc0_valid_r}} & dec_tlu_i0_pc_r[31:1]) |
                          ({31{~pc0_valid_r}} & pc_r_d1[31:1]));

   rvdffpcie #(31)  pwbc_ff (.*, .en(pc0_valid_r), .din(pc_r[31:1]), .dout(pc_r_d1[31:1]));

   assign wr_mepc_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEPC);

   assign mepc_ns[31:1] = ( ({31{i0_exception_valid_r | lsu_exc_valid_r | mepc_trigger_hit_sel_pc_r}} & pc_r[31:1]) |
                            ({31{interrupt_valid_r}} & npc_r[31:1]) |
                            ({31{wr_mepc_r & ~exc_or_int_valid_r}} & dec_csr_wrdata_r[31:1]) |
                            ({31{~wr_mepc_r & ~exc_or_int_valid_r}} & mepc[31:1]) );


   rvdffe #(31)  mepc_ff (.*, .en(i0_exception_valid_r | lsu_exc_valid_r | mepc_trigger_hit_sel_pc_r | interrupt_valid_r | wr_mepc_r), .din(mepc_ns[31:1]), .dout(mepc[31:1]));

   // ----------------------------------------------------------------------
   // MCAUSE (RW)
   // [31:0] : Exception Cause

   assign wr_mcause_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCAUSE);
   assign mcause_sel_nmi_store = exc_or_int_valid_r & take_nmi & nmi_lsu_store_type;
   assign mcause_sel_nmi_load = exc_or_int_valid_r & take_nmi & nmi_lsu_load_type;
   assign mcause_sel_nmi_ext = exc_or_int_valid_r & take_nmi & take_ext_int_start_d3 & |lsu_fir_error[1:0] & ~nmi_int_detected_f;
   // FIR value decoder
   // 0 –no error
   // 1 –uncorrectable ecc  => f000_1000
   // 2 –dccm region access error => f000_1001
   // 3 –non dccm region access error => f000_1002
   assign mcause_fir_error_type[1:0] = {&lsu_fir_error[1:0], lsu_fir_error[1] & ~lsu_fir_error[0]};

   assign mcause_ns[31:0] = ( ({32{mcause_sel_nmi_store}} & {32'hf000_0000}) |
                              ({32{mcause_sel_nmi_load}} & {32'hf000_0001}) |
                              ({32{mcause_sel_nmi_ext}} & {28'hf000_100, 2'b0, mcause_fir_error_type[1:0]}) |
                              ({32{exc_or_int_valid_r & ~take_nmi}} & {interrupt_valid_r, 26'b0, exc_cause_r[4:0]}) |
                              ({32{wr_mcause_r & ~exc_or_int_valid_r}} & dec_csr_wrdata_r[31:0]) |
                              ({32{~wr_mcause_r & ~exc_or_int_valid_r}} & mcause[31:0]) );

   rvdffe #(32)  mcause_ff (.*, .en(exc_or_int_valid_r | wr_mcause_r), .din(mcause_ns[31:0]), .dout(mcause[31:0]));
   // ----------------------------------------------------------------------
   // MSCAUSE (RW)
   // [2:0] : Secondary exception Cause
   assign wr_mscause_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MSCAUSE);

   assign ifu_mscause[3:0]  =  (dec_tlu_packet_r.icaf_type[1:0] == 2'b00) ? 4'b1001 :
                               {2'b00 , dec_tlu_packet_r.icaf_type[1:0]} ;

   assign mscause_type[3:0] = ( ({4{lsu_i0_exc_r}} & lsu_error_pkt_r.mscause[3:0]) |
                                ({4{i0_trigger_hit_r}} & 4'b0001) |
                                ({4{ebreak_r}} & 4'b0010) |
                                ({4{inst_acc_r}} & ifu_mscause[3:0])
                                );

   assign mscause_ns[3:0] = ( ({4{exc_or_int_valid_r}} & mscause_type[3:0]) |
                              ({4{ wr_mscause_r & ~exc_or_int_valid_r}} & dec_csr_wrdata_r[3:0]) |
                              ({4{~wr_mscause_r & ~exc_or_int_valid_r}} & mscause[3:0])
                             );

   rvdff #(4)  mscause_ff (.*, .clk(e4e5_int_clk), .din(mscause_ns[3:0]), .dout(mscause[3:0]));
   // ----------------------------------------------------------------------
   // MTVAL (RW)
   // [31:0] : Exception address if relevant

   assign wr_mtval_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTVAL);
   assign mtval_capture_pc_r = exc_or_int_valid_r & (ebreak_r | (inst_acc_r & ~inst_acc_second_r) | mepc_trigger_hit_sel_pc_r) & ~take_nmi;
   assign mtval_capture_pc_plus2_r = exc_or_int_valid_r & (inst_acc_r & inst_acc_second_r) & ~take_nmi;
   assign mtval_capture_inst_r = exc_or_int_valid_r & illegal_r & ~take_nmi;
   assign mtval_capture_lsu_r = exc_or_int_valid_r & lsu_exc_valid_r & ~take_nmi;
   assign mtval_clear_r = exc_or_int_valid_r & ~mtval_capture_pc_r & ~mtval_capture_inst_r & ~mtval_capture_lsu_r & ~mepc_trigger_hit_sel_pc_r;


   assign mtval_ns[31:0] = (({32{mtval_capture_pc_r}} & {pc_r[31:1], 1'b0}) |
                            ({32{mtval_capture_pc_plus2_r}} & {pc_r[31:1] + 31'b1, 1'b0}) |
                            ({32{mtval_capture_inst_r}} & dec_illegal_inst[31:0]) |
                            ({32{mtval_capture_lsu_r}} & lsu_error_pkt_addr_r[31:0]) |
                            ({32{wr_mtval_r & ~interrupt_valid_r}} & dec_csr_wrdata_r[31:0]) |
                            ({32{~take_nmi & ~wr_mtval_r & ~mtval_capture_pc_r & ~mtval_capture_inst_r & ~mtval_clear_r & ~mtval_capture_lsu_r}} & mtval[31:0]) );


   rvdffe #(32)  mtval_ff (.*, .en(tlu_flush_lower_r | wr_mtval_r), .din(mtval_ns[31:0]), .dout(mtval[31:0]));

   // ----------------------------------------------------------------------
   // MSECCFG
   // [31:3] : Reserved, read 0x0
   // [2]    : RLB
   // [1]    : MMWP
   // [0]    : MML

`ifdef RV_USER_MODE

   localparam MSECCFG  = 12'h747;
   localparam MSECCFGH = 12'h757;

   // Detect if any PMP region is locked regardless of being enabled. This is
   // necessary for mseccfg.RLB bit write behavior
   logic [pt.PMP_ENTRIES-1:0] pmp_region_locked;
   for (genvar r = 0; r < pt.PMP_ENTRIES; r++) begin : g_regions
     assign pmp_region_locked[r] = pmp_pmpcfg[r].lock;
   end

   logic  pmp_any_region_locked;
   assign pmp_any_region_locked = |pmp_region_locked;

   // mseccfg
   assign wr_mseccfg_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MSECCFG);
   rvdffs #(3) mseccfg_ff (.*, .clk(csr_wr_clk), .en(wr_mseccfg_r), .din(mseccfg_ns), .dout(mseccfg));

   assign mseccfg_ns = {
     pmp_any_region_locked ?
        (dec_csr_wrdata_r[MSECCFG_RLB] & mseccfg[MSECCFG_RLB]) :  // When any PMP region is locked this bit can only be cleared
         dec_csr_wrdata_r[MSECCFG_RLB],                           // Otherwise regularly writeable
     dec_csr_wrdata_r[MSECCFG_MMWP] |  mseccfg[MSECCFG_MMWP],     // Sticky bit, can only be set but not cleared
     dec_csr_wrdata_r[MSECCFG_MML ] |  mseccfg[MSECCFG_MML ]      // Sticky bit, can only be set but never cleared
   };

`endif

   // ----------------------------------------------------------------------
   // MCGC (RW) Clock gating control
   // [31:10]: Reserved, reads 0x0
   // [9]    : picio_clk_override
   // [7]    : dec_clk_override
   // [6]    : Unused
   // [5]    : ifu_clk_override
   // [4]    : lsu_clk_override
   // [3]    : bus_clk_override
   // [2]    : pic_clk_override
   // [1]    : dccm_clk_override
   // [0]    : icm_clk_override
   //
   assign wr_mcgc_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCGC);

   assign mcgc_ns[9:0] = wr_mcgc_r ? {~dec_csr_wrdata_r[9], dec_csr_wrdata_r[8:0]} : mcgc_int[9:0];
   rvdffe #(10)  mcgc_ff (.*, .en(wr_mcgc_r), .din(mcgc_ns[9:0]), .dout(mcgc_int[9:0]));

   assign mcgc[9:0] = {~mcgc_int[9], mcgc_int[8:0]};

   assign dec_tlu_picio_clk_override= mcgc[9];
   assign dec_tlu_misc_clk_override = mcgc[8];
   assign dec_tlu_dec_clk_override  = mcgc[7];
   //sign dec_tlu_exu_clk_override  = mcgc[6];
   assign dec_tlu_ifu_clk_override  = mcgc[5];
   assign dec_tlu_lsu_clk_override  = mcgc[4];
   assign dec_tlu_bus_clk_override  = mcgc[3];
   assign dec_tlu_pic_clk_override  = mcgc[2];
   assign dec_tlu_dccm_clk_override = mcgc[1];
   assign dec_tlu_icm_clk_override  = mcgc[0];

   // ----------------------------------------------------------------------
   // MFDC (RW) Feature Disable Control
   // [31:19] : Reserved, reads 0x0
   // [18:16] : DMA QoS Prty
   // [15:13] : Reserved, reads 0x0
   // [12]   : Disable trace
   // [11]   : Disable external load forwarding
   // [10]   : Disable dual issue
   // [9]    : Disable pic multiple ints
   // [8]    : Disable core ecc
   // [7]    : Disable secondary alu?s
   // [6]    : Unused, 0x0
   // [5]    : Disable non-blocking loads/divides
   // [4]    : Disable fast divide
   // [3]    : Disable branch prediction and return stack
   // [2]    : Disable write buffer coalescing
   // [1]    : Disable load misses that bypass the write buffer
   // [0]    : Disable pipelining - Enable single instruction execution
   //

   assign wr_mfdc_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MFDC);

   rvdffe #(16)  mfdc_ff (.*, .en(wr_mfdc_r), .din({mfdc_ns[15:0]}), .dout(mfdc_int[15:0]));

   // flip poweron value of bit 6 for AXI build
   if(pt.BUILD_AXI4==1) begin : axi4
      // flip poweron valid of bit 12
         assign mfdc_ns[15:0] = {~dec_csr_wrdata_r[18:16], dec_csr_wrdata_r[12], dec_csr_wrdata_r[11:7], ~dec_csr_wrdata_r[6], dec_csr_wrdata_r[5:0]};
         assign mfdc[18:0] = {~mfdc_int[15:13], 3'b0, mfdc_int[12], mfdc_int[11:7], ~mfdc_int[6], mfdc_int[5:0]};
   end
   else begin
      // flip poweron valid of bit 12
         assign mfdc_ns[15:0] = {~dec_csr_wrdata_r[18:16],dec_csr_wrdata_r[12:0]};
         assign mfdc[18:0] = {~mfdc_int[15:13], 3'b0, mfdc_int[12:0]};
   end


   assign dec_tlu_dma_qos_prty[2:0] = mfdc[18:16];
   assign dec_tlu_trace_disable = mfdc[12];
   assign dec_tlu_external_ldfwd_disable = mfdc[11];
   assign dec_tlu_core_ecc_disable = mfdc[8];
   assign dec_tlu_sideeffect_posted_disable = mfdc[6];
   assign dec_tlu_bpred_disable = mfdc[3];
   assign dec_tlu_wb_coalescing_disable = mfdc[2];
   assign dec_tlu_pipelining_disable = mfdc[0];

   // ----------------------------------------------------------------------
   // MCPC (RW) Pause counter
   // [31:0] : Reads 0x0, decs in the wb register in decode_ctl

   assign dec_tlu_wr_pause_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCPC) & ~interrupt_valid_r & ~take_ext_int_start;

   // ----------------------------------------------------------------------
   // MRAC (RW)
   // [31:0] : Region Access Control Register, 16 regions, {side_effect, cachable} pairs

   assign wr_mrac_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MRAC);

   // prevent pairs of 0x11, side_effect and cacheable
   assign mrac_in[31:0] = {dec_csr_wrdata_r[31], dec_csr_wrdata_r[30] & ~dec_csr_wrdata_r[31],
                           dec_csr_wrdata_r[29], dec_csr_wrdata_r[28] & ~dec_csr_wrdata_r[29],
                           dec_csr_wrdata_r[27], dec_csr_wrdata_r[26] & ~dec_csr_wrdata_r[27],
                           dec_csr_wrdata_r[25], dec_csr_wrdata_r[24] & ~dec_csr_wrdata_r[25],
                           dec_csr_wrdata_r[23], dec_csr_wrdata_r[22] & ~dec_csr_wrdata_r[23],
                           dec_csr_wrdata_r[21], dec_csr_wrdata_r[20] & ~dec_csr_wrdata_r[21],
                           dec_csr_wrdata_r[19], dec_csr_wrdata_r[18] & ~dec_csr_wrdata_r[19],
                           dec_csr_wrdata_r[17], dec_csr_wrdata_r[16] & ~dec_csr_wrdata_r[17],
                           dec_csr_wrdata_r[15], dec_csr_wrdata_r[14] & ~dec_csr_wrdata_r[15],
                           dec_csr_wrdata_r[13], dec_csr_wrdata_r[12] & ~dec_csr_wrdata_r[13],
                           dec_csr_wrdata_r[11], dec_csr_wrdata_r[10] & ~dec_csr_wrdata_r[11],
                           dec_csr_wrdata_r[9], dec_csr_wrdata_r[8] & ~dec_csr_wrdata_r[9],
                           dec_csr_wrdata_r[7], dec_csr_wrdata_r[6] & ~dec_csr_wrdata_r[7],
                           dec_csr_wrdata_r[5], dec_csr_wrdata_r[4] & ~dec_csr_wrdata_r[5],
                           dec_csr_wrdata_r[3], dec_csr_wrdata_r[2] & ~dec_csr_wrdata_r[3],
                           dec_csr_wrdata_r[1], dec_csr_wrdata_r[0] & ~dec_csr_wrdata_r[1]};

   rvdffe #(32)  mrac_ff (.*, .en(wr_mrac_r), .din(mrac_in[31:0]), .dout(mrac[31:0]));

   // drive to LSU/IFU
   assign dec_tlu_mrac_ff[31:0] = mrac[31:0];

   // ----------------------------------------------------------------------
   // MDEAU (WAR0)
   // [31:0] : Dbus Error Address Unlock register
   //

   assign wr_mdeau_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MDEAU);


   // ----------------------------------------------------------------------
   // MDSEAC (R)
   // [31:0] : Dbus Store Error Address Capture register
   //

   // only capture error bus if the MDSEAC reg is not locked
   assign mdseac_locked_ns = mdseac_en | (mdseac_locked_f & ~wr_mdeau_r);

   assign mdseac_en = (lsu_imprecise_error_store_any | lsu_imprecise_error_load_any) & ~nmi_int_detected_f & ~mdseac_locked_f;

   rvdffe #(32)  mdseac_ff (.*, .en(mdseac_en), .din(lsu_imprecise_error_addr_any[31:0]), .dout(mdseac[31:0]));

   // ----------------------------------------------------------------------
   // MPMC (R0W1)
   // [0] : FW halt
   // [1] : Set MSTATUS[MIE] on halt

   assign wr_mpmc_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MPMC);

   // allow the cycle of the dbg halt flush that contains the wr_mpmc_r to
   // set the mstatus bit potentially, use delayed version of internal dbg halt.
   assign fw_halt_req = wr_mpmc_r & dec_csr_wrdata_r[0] & ~internal_dbg_halt_mode_f2 & ~ext_int_freeze_d1;

   assign fw_halted_ns = (fw_halt_req | fw_halted) & ~set_mie_pmu_fw_halt;
   assign mpmc_b_ns[1] = wr_mpmc_r ? ~dec_csr_wrdata_r[1] : ~mpmc[1];
   rvdff #(1)  mpmc_ff (.*, .clk(csr_wr_clk), .din(mpmc_b_ns[1]), .dout(mpmc_b[1]));
   assign mpmc[1] = ~mpmc_b[1];

   // ----------------------------------------------------------------------
   // MICECT (I-Cache error counter/threshold)
   // [31:27] : Icache parity error threshold
   // [26:0]  : Icache parity error count

   assign csr_sat[31:27] = (dec_csr_wrdata_r[31:27] > 5'd26) ? 5'd26 : dec_csr_wrdata_r[31:27];

   assign wr_micect_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MICECT);
   assign micect_inc[26:0] = micect[26:0] + {26'b0, ic_perr_r};
   assign micect_ns =  wr_micect_r ? {csr_sat[31:27], dec_csr_wrdata_r[26:0]} : {micect[31:27], micect_inc[26:0]};

   rvdffe #(32)  micect_ff (.*, .en(wr_micect_r | ic_perr_r), .din(micect_ns[31:0]), .dout(micect[31:0]));

   assign mice_ce_req = |({32'hffffffff << micect[31:27]} & {5'b0, micect[26:0]});

   // ----------------------------------------------------------------------
   // MICCMECT (ICCM error counter/threshold)
   // [31:27] : ICCM parity error threshold
   // [26:0]  : ICCM parity error count

   assign wr_miccmect_r     = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MICCMECT);
   assign miccmect_inc[26:0] = miccmect[26:0] + {26'b0, iccm_sbecc_r | iccm_dma_sb_error};
   assign miccmect_ns        = wr_miccmect_r ? {csr_sat[31:27], dec_csr_wrdata_r[26:0]} : {miccmect[31:27], miccmect_inc[26:0]};

   rvdffe #(32)  miccmect_ff (.*, .clk(free_l2clk), .en(wr_miccmect_r | iccm_sbecc_r | iccm_dma_sb_error), .din(miccmect_ns[31:0]), .dout(miccmect[31:0]));

   assign miccme_ce_req = |({32'hffffffff << miccmect[31:27]} & {5'b0, miccmect[26:0]});

   // ----------------------------------------------------------------------
   // MDCCMECT (DCCM error counter/threshold)
   // [31:27] : DCCM parity error threshold
   // [26:0]  : DCCM parity error count

   assign wr_mdccmect_r     = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MDCCMECT);
   assign mdccmect_inc[26:0] = mdccmect[26:0] + {26'b0, lsu_single_ecc_error_r_d1};
   assign mdccmect_ns        = wr_mdccmect_r ? {csr_sat[31:27], dec_csr_wrdata_r[26:0]} : {mdccmect[31:27], mdccmect_inc[26:0]};

   rvdffe #(32)  mdccmect_ff (.*, .clk(free_l2clk), .en(wr_mdccmect_r | lsu_single_ecc_error_r_d1), .din(mdccmect_ns[31:0]), .dout(mdccmect[31:0]));

   assign mdccme_ce_req = |({32'hffffffff << mdccmect[31:27]} & {5'b0, mdccmect[26:0]});


   // ----------------------------------------------------------------------
   // MFDHT (Force Debug Halt Threshold)
   // [5:1] : Halt timeout threshold (power of 2)
   //   [0] : Halt timeout enabled

   assign wr_mfdht_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MFDHT);

   assign mfdht_ns[5:0] = wr_mfdht_r ? dec_csr_wrdata_r[5:0] : mfdht[5:0];

   rvdffs #(6)  mfdht_ff (.*, .clk(csr_wr_clk), .en(wr_mfdht_r), .din(mfdht_ns[5:0]), .dout(mfdht[5:0]));

   // ----------------------------------------------------------------------
   // MFDHS(RW)
   // [1] : LSU operation pending when debug halt threshold reached
   // [0] : IFU operation pending when debug halt threshold reached

   assign wr_mfdhs_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MFDHS);

   assign mfdhs_ns[1:0] = wr_mfdhs_r ? dec_csr_wrdata_r[1:0] : ((dbg_tlu_halted & ~dbg_tlu_halted_f) ? {~lsu_idle_any_f, ~ifu_miss_state_idle_f} : mfdhs[1:0]);

   rvdffs #(2)  mfdhs_ff (.*, .clk(free_clk), .en(wr_mfdhs_r | dbg_tlu_halted), .din(mfdhs_ns[1:0]), .dout(mfdhs[1:0]));

   assign force_halt_ctr[31:0] = debug_halt_req_f ? (force_halt_ctr_f[31:0] + 32'b1) : (dbg_tlu_halted_f ? 32'b0 : force_halt_ctr_f[31:0]);

   rvdffe #(32)  forcehaltctr_ff (.*, .en(mfdht[0]), .din(force_halt_ctr[31:0]), .dout(force_halt_ctr_f[31:0]));

   assign force_halt = mfdht[0] & |(force_halt_ctr_f[31:0] & (32'hffffffff << mfdht[5:1]));


   // ----------------------------------------------------------------------
   // MEIVT (External Interrupt Vector Table (R/W))
   // [31:10]: Base address (R/W)
   // [9:0]  : Reserved, reads 0x0
   assign wr_meivt_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEIVT);

   rvdffe #(22)  meivt_ff (.*, .en(wr_meivt_r), .din(dec_csr_wrdata_r[31:10]), .dout(meivt[31:10]));


   // ----------------------------------------------------------------------
   // MEIHAP (External Interrupt Handler Access Pointer (R))
   // [31:10]: Base address (R/W)
   // [9:2]  : ClaimID (R)
   // [1:0]  : Reserved, 0x0

   assign wr_meihap_r = wr_meicpct_r;

   rvdffe #(8)  meihap_ff (.*, .en(wr_meihap_r), .din(pic_claimid[7:0]), .dout(meihap[9:2]));

   assign dec_tlu_meihap[31:2] = {meivt[31:10], meihap[9:2]};

   // ----------------------------------------------------------------------
   // MEICURPL (R/W)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : CURRPRI - Priority level of current interrupt service routine (R/W)
   assign wr_meicurpl_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEICURPL);
   assign meicurpl_ns[3:0] = wr_meicurpl_r ? dec_csr_wrdata_r[3:0] : meicurpl[3:0];

   rvdff #(4)  meicurpl_ff (.*, .clk(csr_wr_clk), .din(meicurpl_ns[3:0]), .dout(meicurpl[3:0]));

   // PIC needs this reg
   assign dec_tlu_meicurpl[3:0] = meicurpl[3:0];


   // ----------------------------------------------------------------------
   // MEICIDPL (R/W)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : External Interrupt Claim ID's Priority Level Register

   assign wr_meicidpl_r = (dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEICIDPL)) | take_ext_int_start;

   assign meicidpl_ns[3:0] = wr_meicpct_r ? pic_pl[3:0] : (wr_meicidpl_r ? dec_csr_wrdata_r[3:0] : meicidpl[3:0]);


   // ----------------------------------------------------------------------
   // MEICPCT (Capture CLAIMID in MEIHAP and PL in MEICIDPL
   // [31:1] : Reserved (read 0x0)
   // [0]    : Capture (W1, Read 0)
   assign wr_meicpct_r = (dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEICPCT)) | take_ext_int_start;

   // ----------------------------------------------------------------------
   // MEIPT (External Interrupt Priority Threshold)
   // [31:4] : Reserved (read 0x0)
   // [3:0]  : PRITHRESH

   assign wr_meipt_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MEIPT);
   assign meipt_ns[3:0] = wr_meipt_r ? dec_csr_wrdata_r[3:0] : meipt[3:0];

   rvdff #(4)  meipt_ff (.*, .clk(csr_wr_clk), .din(meipt_ns[3:0]), .dout(meipt[3:0]));

   // to PIC
   assign dec_tlu_meipt[3:0] = meipt[3:0];
   // ----------------------------------------------------------------------
   // DCSR (R/W) (Only accessible in debug mode)
   // [31:28] : xdebugver (hard coded to 0x4) RO
   // [27:16] : 0x0, reserved
   // [15]    : ebreakm
   // [14]    : 0x0, reserved
   // [13]    : ebreaks (0x0 for this core)
   // [12]    : ebreaku (0x0 for this core)
   // [11]    : stepie
   // [10]    : stopcount
   // [9]     : 0x0 //stoptime
   // [8:6]   : cause (RO)
   // [5:4]   : 0x0, reserved
   // [3]     : nmip
   // [2]     : step
   // [1:0]   : prv (0x3 for this core)
   //

   // RV has clarified that 'priority 4' in the spec means top priority.
   // 4. single step. 3. Debugger request. 2. Ebreak. 1. Trigger.

   // RV debug spec indicates a cause priority change for trigger hits during single step.
   assign trigger_hit_for_dscr_cause_r_d1 = trigger_hit_dmode_r_d1 | (trigger_hit_r_d1 & dcsr_single_step_done_f);

   assign dcsr_cause[8:6] = ( ({3{dcsr_single_step_done_f & ~ebreak_to_debug_mode_r_d1 & ~trigger_hit_for_dscr_cause_r_d1 & ~debug_halt_req}} & 3'b100) |
                              ({3{debug_halt_req & ~ebreak_to_debug_mode_r_d1 & ~trigger_hit_for_dscr_cause_r_d1}} &  3'b011) |
                              ({3{ebreak_to_debug_mode_r_d1 & ~trigger_hit_for_dscr_cause_r_d1}} &  3'b001) |
                              ({3{trigger_hit_for_dscr_cause_r_d1}} & 3'b010));

   assign wr_dcsr_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DCSR);



  // Multiple halt enter requests can happen before we are halted.
  // We have to continue to upgrade based on dcsr_cause priority but we can't downgrade.
   assign dcsr_cause_upgradeable = internal_dbg_halt_mode_f & (dcsr[8:6] == 3'b011);
   assign enter_debug_halt_req_le = enter_debug_halt_req & (~dbg_tlu_halted | dcsr_cause_upgradeable);

   assign nmi_in_debug_mode = nmi_int_detected_f & internal_dbg_halt_mode_f;
   assign dcsr_ns[15:2] = enter_debug_halt_req_le ? {dcsr[15:9], dcsr_cause[8:6], dcsr[5:2]} :
                          (wr_dcsr_r ? {dec_csr_wrdata_r[15], 3'b0, dec_csr_wrdata_r[11:10], 1'b0, dcsr[8:6], 2'b00, nmi_in_debug_mode | dcsr[3], dec_csr_wrdata_r[2]} :
                           {dcsr[15:4], nmi_in_debug_mode, dcsr[2]});

   rvdffe #(14)  dcsr_ff (.*, .clk(free_l2clk), .en(enter_debug_halt_req_le | wr_dcsr_r | internal_dbg_halt_mode | take_nmi), .din(dcsr_ns[15:2]), .dout(dcsr[15:2]));

   // ----------------------------------------------------------------------
   // DPC (R/W) (Only accessible in debug mode)
   // [31:0] : Debug PC

   assign wr_dpc_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DPC);
   assign dpc_capture_npc = dbg_tlu_halted & ~dbg_tlu_halted_f & ~request_debug_mode_done;
   assign dpc_capture_pc = request_debug_mode_r;

   assign dpc_ns[31:1] = ( ({31{~dpc_capture_pc & ~dpc_capture_npc & wr_dpc_r}} & dec_csr_wrdata_r[31:1]) |
                           ({31{dpc_capture_pc}} & pc_r[31:1]) |
                           ({31{~dpc_capture_pc & dpc_capture_npc}} & npc_r[31:1]) );

   rvdffe #(31)  dpc_ff (.*, .en(wr_dpc_r | dpc_capture_pc | dpc_capture_npc), .din(dpc_ns[31:1]), .dout(dpc[31:1]));

   // ----------------------------------------------------------------------
   // DICAWICS (R/W) (Only accessible in debug mode)
   // [31:25] : Reserved
   // [24]    : Array select, 0 is data, 1 is tag
   // [23:22] : Reserved
   // [21:20] : Way select
   // [19:17] : Reserved
   // [16:3]  : Index
   // [2:0]   : Reserved

   assign dicawics_ns[16:0] = {dec_csr_wrdata_r[24], dec_csr_wrdata_r[21:20], dec_csr_wrdata_r[16:3]};
   assign wr_dicawics_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAWICS);

   rvdffe #(17)  dicawics_ff (.*, .en(wr_dicawics_r), .din(dicawics_ns[16:0]), .dout(dicawics[16:0]));

   // ----------------------------------------------------------------------
   // DICAD0 (R/W) (Only accessible in debug mode)
   //
   // If dicawics[array] is 0
   // [31:0]  : inst data
   //
   // If dicawics[array] is 1
   // [31:16] : Tag
   // [15:7]  : Reserved
   // [6:4]   : LRU
   // [3:1]   : Reserved
   // [0]     : Valid

   assign dicad0_ns[31:0] = wr_dicad0_r ? dec_csr_wrdata_r[31:0] : ifu_ic_debug_rd_data[31:0];

   assign wr_dicad0_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAD0);

   rvdffe #(32)  dicad0_ff (.*, .en(wr_dicad0_r | ifu_ic_debug_rd_data_valid), .din(dicad0_ns[31:0]), .dout(dicad0[31:0]));

   // ----------------------------------------------------------------------
   // DICAD0H (R/W) (Only accessible in debug mode)
   //
   // If dicawics[array] is 0
   // [63:32]  : inst data
   //

   assign dicad0h_ns[31:0] = wr_dicad0h_r ? dec_csr_wrdata_r[31:0] : ifu_ic_debug_rd_data[63:32];

   assign wr_dicad0h_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAD0H);

   rvdffe #(32)  dicad0h_ff (.*, .en(wr_dicad0h_r | ifu_ic_debug_rd_data_valid), .din(dicad0h_ns[31:0]), .dout(dicad0h[31:0]));


if (pt.ICACHE_ECC == 1) begin : genblock1
   // ----------------------------------------------------------------------
   // DICAD1 (R/W) (Only accessible in debug mode)
   // [6:0]     : ECC
   localparam DICAD1        = 12'h7ca;

   assign dicad1_ns[6:0] = wr_dicad1_r ? dec_csr_wrdata_r[6:0] : ifu_ic_debug_rd_data[70:64];

   assign wr_dicad1_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAD1);

   rvdffe #(.WIDTH(7), .OVERRIDE(1))  dicad1_ff (.*, .en(wr_dicad1_r | ifu_ic_debug_rd_data_valid), .din(dicad1_ns[6:0]), .dout(dicad1_raw[6:0]));

   assign dicad1[31:0] = {25'b0, dicad1_raw[6:0]};

end
else begin : genblock1
   // ----------------------------------------------------------------------
   // DICAD1 (R/W) (Only accessible in debug mode)
   // [3:0]     : Parity
   localparam DICAD1        = 12'h7ca;

   assign dicad1_ns[3:0] = wr_dicad1_r ? dec_csr_wrdata_r[3:0] : ifu_ic_debug_rd_data[67:64];

   assign wr_dicad1_r = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAD1);

   rvdffs #(4)  dicad1_ff (.*, .clk(free_clk), .en(wr_dicad1_r | ifu_ic_debug_rd_data_valid), .din(dicad1_ns[3:0]), .dout(dicad1_raw[3:0]));

   assign dicad1[31:0] = {28'b0, dicad1_raw[3:0]};
end
   // ----------------------------------------------------------------------
   // DICAGO (R/W) (Only accessible in debug mode)
   // [0]     : Go

if (pt.ICACHE_ECC == 1)
   assign dec_tlu_ic_diag_pkt.icache_wrdata[70:0] = {      dicad1[6:0], dicad0h[31:0], dicad0[31:0]};
else
   assign dec_tlu_ic_diag_pkt.icache_wrdata[70:0] = {3'b0, dicad1[3:0], dicad0h[31:0], dicad0[31:0]};


   assign dec_tlu_ic_diag_pkt.icache_dicawics[16:0] = dicawics[16:0];

   assign icache_rd_valid = allow_dbg_halt_csr_write & dec_csr_any_unq_d & dec_i0_decode_d & ~dec_csr_wen_unq_d & (dec_csr_rdaddr_d[11:0] == DICAGO);
   assign icache_wr_valid = allow_dbg_halt_csr_write & dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == DICAGO);


   assign dec_tlu_ic_diag_pkt.icache_rd_valid = icache_rd_valid_f;
   assign dec_tlu_ic_diag_pkt.icache_wr_valid = icache_wr_valid_f;

   // ----------------------------------------------------------------------
   // MTSEL (R/W)
   // [1:0] : Trigger select : 00, 01, 10 are data/address triggers. 11 is inst count

   assign wr_mtsel_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTSEL);
   assign mtsel_ns[1:0] = wr_mtsel_r ? {dec_csr_wrdata_r[1:0]} : mtsel[1:0];

   rvdff #(2)  mtsel_ff (.*, .clk(csr_wr_clk), .din(mtsel_ns[1:0]), .dout(mtsel[1:0]));

   // ----------------------------------------------------------------------
   // MTDATA1 (R/W)
   // [31:0] : Trigger Data 1

   // for triggers 0, 1, 2 and 3 aka Match Control
   // [31:28] : type, hard coded to 0x2
   // [27]    : dmode
   // [26:21] : hard coded to 0x1f
   // [20]    : hit
   // [19]    : select (0 - address, 1 - data)
   // [18]    : timing, always 'before', reads 0x0
   // [17:12] : action, bits  [17:13] not implemented and reads 0x0
   // [11]    : chain
   // [10:7]  : match, bits [10:8] not implemented and reads 0x0
   // [6]     : M
   // [5:3]   : not implemented, reads 0x0
   // [2]     : execute
   // [1]     : store
   // [0]     : load
   //
   // decoder ring
   // [27]    : => 9
   // [20]    : => 8
   // [19]    : => 7
   // [12]    : => 6
   // [11]    : => 5
   // [7]     : => 4
   // [6]     : => 3
   // [2]     : => 2
   // [1]     : => 1
   // [0]     : => 0


   // don't allow setting load-data.
   assign tdata_load = dec_csr_wrdata_r[0] & ~dec_csr_wrdata_r[19];
   // don't allow setting execute-data.
   assign tdata_opcode = dec_csr_wrdata_r[2] & ~dec_csr_wrdata_r[19];
   // don't allow clearing DMODE and action=1
   assign tdata_action = (dec_csr_wrdata_r[27] & dbg_tlu_halted_f) & dec_csr_wrdata_r[12];

   // Chain bit has conditions: WARL for triggers without chains. Force to zero if dmode is 0 but next trigger dmode is 1.
   assign tdata_chain = mtsel[0] ? 1'b0 : // triggers 1 and 3 chain bit is always zero
                        mtsel[1] ?  dec_csr_wrdata_r[11] & ~(mtdata1_t3[MTDATA1_DMODE] & ~dec_csr_wrdata_r[27]) : // trigger 2
                                    dec_csr_wrdata_r[11] & ~(mtdata1_t1[MTDATA1_DMODE] & ~dec_csr_wrdata_r[27]);  // trigger 0

   // Kill mtdata1 write if dmode=1 but prior trigger has dmode=0/chain=1. Only applies to T1 and T3
   assign tdata_kill_write = mtsel[1] ? dec_csr_wrdata_r[27] & (~mtdata1_t2[MTDATA1_DMODE] & mtdata1_t2[MTDATA1_CHAIN]) : // trigger 3
                                        dec_csr_wrdata_r[27] & (~mtdata1_t0[MTDATA1_DMODE] & mtdata1_t0[MTDATA1_CHAIN]) ; // trigger 1


   assign tdata_wrdata_r[9:0]  = {dec_csr_wrdata_r[27] & dbg_tlu_halted_f,
                                   dec_csr_wrdata_r[20:19],
                                   tdata_action,
                                   tdata_chain,
                                   dec_csr_wrdata_r[7:6],
                                   tdata_opcode,
                                   dec_csr_wrdata_r[1],
                                   tdata_load};

   // If the DMODE bit is set, tdata1 can only be updated in debug_mode
   assign wr_mtdata1_t0_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA1) & (mtsel[1:0] == 2'b0) & (~mtdata1_t0[MTDATA1_DMODE] | dbg_tlu_halted_f);
   assign mtdata1_t0_ns[9:0] = wr_mtdata1_t0_r ? tdata_wrdata_r[9:0] :
                                {mtdata1_t0[9], update_hit_bit_r[0] | mtdata1_t0[8], mtdata1_t0[7:0]};

   assign wr_mtdata1_t1_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA1) & (mtsel[1:0] == 2'b01) & (~mtdata1_t1[MTDATA1_DMODE] | dbg_tlu_halted_f) & ~tdata_kill_write;
   assign mtdata1_t1_ns[9:0] = wr_mtdata1_t1_r ? tdata_wrdata_r[9:0] :
                                {mtdata1_t1[9], update_hit_bit_r[1] | mtdata1_t1[8], mtdata1_t1[7:0]};

   assign wr_mtdata1_t2_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA1) & (mtsel[1:0] == 2'b10) & (~mtdata1_t2[MTDATA1_DMODE] | dbg_tlu_halted_f);
   assign mtdata1_t2_ns[9:0] = wr_mtdata1_t2_r ? tdata_wrdata_r[9:0] :
                                {mtdata1_t2[9], update_hit_bit_r[2] | mtdata1_t2[8], mtdata1_t2[7:0]};

   assign wr_mtdata1_t3_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA1) & (mtsel[1:0] == 2'b11) & (~mtdata1_t3[MTDATA1_DMODE] | dbg_tlu_halted_f) & ~tdata_kill_write;
   assign mtdata1_t3_ns[9:0] = wr_mtdata1_t3_r ? tdata_wrdata_r[9:0] :
                                {mtdata1_t3[9], update_hit_bit_r[3] | mtdata1_t3[8], mtdata1_t3[7:0]};


   rvdffe #(10)  mtdata1_t0_ff (.*, .en(trigger_enabled[0] | wr_mtdata1_t0_r), .din(mtdata1_t0_ns[9:0]), .dout(mtdata1_t0[9:0]));
   rvdffe #(10)  mtdata1_t1_ff (.*, .en(trigger_enabled[1] | wr_mtdata1_t1_r), .din(mtdata1_t1_ns[9:0]), .dout(mtdata1_t1[9:0]));
   rvdffe #(10)  mtdata1_t2_ff (.*, .en(trigger_enabled[2] | wr_mtdata1_t2_r), .din(mtdata1_t2_ns[9:0]), .dout(mtdata1_t2[9:0]));
   rvdffe #(10)  mtdata1_t3_ff (.*, .en(trigger_enabled[3] | wr_mtdata1_t3_r), .din(mtdata1_t3_ns[9:0]), .dout(mtdata1_t3[9:0]));

   assign mtdata1_tsel_out[31:0] = ( ({32{(mtsel[1:0] == 2'b00)}} & {4'h2, mtdata1_t0[9], 6'b011111, mtdata1_t0[8:7], 6'b0, mtdata1_t0[6:5], 3'b0, mtdata1_t0[4:3], 3'b0, mtdata1_t0[2:0]}) |
                                     ({32{(mtsel[1:0] == 2'b01)}} & {4'h2, mtdata1_t1[9], 6'b011111, mtdata1_t1[8:7], 6'b0, mtdata1_t1[6:5], 3'b0, mtdata1_t1[4:3], 3'b0, mtdata1_t1[2:0]}) |
                                     ({32{(mtsel[1:0] == 2'b10)}} & {4'h2, mtdata1_t2[9], 6'b011111, mtdata1_t2[8:7], 6'b0, mtdata1_t2[6:5], 3'b0, mtdata1_t2[4:3], 3'b0, mtdata1_t2[2:0]}) |
                                     ({32{(mtsel[1:0] == 2'b11)}} & {4'h2, mtdata1_t3[9], 6'b011111, mtdata1_t3[8:7], 6'b0, mtdata1_t3[6:5], 3'b0, mtdata1_t3[4:3], 3'b0, mtdata1_t3[2:0]}));

   assign trigger_pkt_any[0].select = mtdata1_t0[MTDATA1_SEL];
   assign trigger_pkt_any[0].match = mtdata1_t0[MTDATA1_MATCH];
   assign trigger_pkt_any[0].store = mtdata1_t0[MTDATA1_ST];
   assign trigger_pkt_any[0].load = mtdata1_t0[MTDATA1_LD];
   assign trigger_pkt_any[0].execute = mtdata1_t0[MTDATA1_EXE];
   assign trigger_pkt_any[0].m = mtdata1_t0[MTDATA1_M_ENABLED];

   assign trigger_pkt_any[1].select = mtdata1_t1[MTDATA1_SEL];
   assign trigger_pkt_any[1].match = mtdata1_t1[MTDATA1_MATCH];
   assign trigger_pkt_any[1].store = mtdata1_t1[MTDATA1_ST];
   assign trigger_pkt_any[1].load = mtdata1_t1[MTDATA1_LD];
   assign trigger_pkt_any[1].execute = mtdata1_t1[MTDATA1_EXE];
   assign trigger_pkt_any[1].m = mtdata1_t1[MTDATA1_M_ENABLED];

   assign trigger_pkt_any[2].select = mtdata1_t2[MTDATA1_SEL];
   assign trigger_pkt_any[2].match = mtdata1_t2[MTDATA1_MATCH];
   assign trigger_pkt_any[2].store = mtdata1_t2[MTDATA1_ST];
   assign trigger_pkt_any[2].load = mtdata1_t2[MTDATA1_LD];
   assign trigger_pkt_any[2].execute = mtdata1_t2[MTDATA1_EXE];
   assign trigger_pkt_any[2].m = mtdata1_t2[MTDATA1_M_ENABLED];

   assign trigger_pkt_any[3].select = mtdata1_t3[MTDATA1_SEL];
   assign trigger_pkt_any[3].match = mtdata1_t3[MTDATA1_MATCH];
   assign trigger_pkt_any[3].store = mtdata1_t3[MTDATA1_ST];
   assign trigger_pkt_any[3].load = mtdata1_t3[MTDATA1_LD];
   assign trigger_pkt_any[3].execute = mtdata1_t3[MTDATA1_EXE];
   assign trigger_pkt_any[3].m = mtdata1_t3[MTDATA1_M_ENABLED];





   // ----------------------------------------------------------------------
   // MTDATA2 (R/W)
   // [31:0] : Trigger Data 2

   // If the DMODE bit is set, tdata2 can only be updated in debug_mode
   assign wr_mtdata2_t0_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA2) & (mtsel[1:0] == 2'b0)  & (~mtdata1_t0[MTDATA1_DMODE] | dbg_tlu_halted_f);
   assign wr_mtdata2_t1_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA2) & (mtsel[1:0] == 2'b01) & (~mtdata1_t1[MTDATA1_DMODE] | dbg_tlu_halted_f);
   assign wr_mtdata2_t2_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA2) & (mtsel[1:0] == 2'b10) & (~mtdata1_t2[MTDATA1_DMODE] | dbg_tlu_halted_f);
   assign wr_mtdata2_t3_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MTDATA2) & (mtsel[1:0] == 2'b11) & (~mtdata1_t3[MTDATA1_DMODE] | dbg_tlu_halted_f);

   rvdffe #(32)  mtdata2_t0_ff (.*, .en(wr_mtdata2_t0_r), .din(dec_csr_wrdata_r[31:0]), .dout(mtdata2_t0[31:0]));
   rvdffe #(32)  mtdata2_t1_ff (.*, .en(wr_mtdata2_t1_r), .din(dec_csr_wrdata_r[31:0]), .dout(mtdata2_t1[31:0]));
   rvdffe #(32)  mtdata2_t2_ff (.*, .en(wr_mtdata2_t2_r), .din(dec_csr_wrdata_r[31:0]), .dout(mtdata2_t2[31:0]));
   rvdffe #(32)  mtdata2_t3_ff (.*, .en(wr_mtdata2_t3_r), .din(dec_csr_wrdata_r[31:0]), .dout(mtdata2_t3[31:0]));

   assign mtdata2_tsel_out[31:0] = ( ({32{(mtsel[1:0] == 2'b00)}} & mtdata2_t0[31:0]) |
                                     ({32{(mtsel[1:0] == 2'b01)}} & mtdata2_t1[31:0]) |
                                     ({32{(mtsel[1:0] == 2'b10)}} & mtdata2_t2[31:0]) |
                                     ({32{(mtsel[1:0] == 2'b11)}} & mtdata2_t3[31:0]));

   assign trigger_pkt_any[0].tdata2[31:0] = mtdata2_t0[31:0];
   assign trigger_pkt_any[1].tdata2[31:0] = mtdata2_t1[31:0];
   assign trigger_pkt_any[2].tdata2[31:0] = mtdata2_t2[31:0];
   assign trigger_pkt_any[3].tdata2[31:0] = mtdata2_t3[31:0];


   //----------------------------------------------------------------------
   // Performance Monitor Counters section starts
   //----------------------------------------------------------------------
   localparam MHPME_NOEVENT             = 10'd0;
   localparam MHPME_CLK_ACTIVE          = 10'd1; // OOP - out of pipe
   localparam MHPME_ICACHE_HIT          = 10'd2; // OOP
   localparam MHPME_ICACHE_MISS         = 10'd3; // OOP
   localparam MHPME_INST_COMMIT         = 10'd4;
   localparam MHPME_INST_COMMIT_16B     = 10'd5;
   localparam MHPME_INST_COMMIT_32B     = 10'd6;
   localparam MHPME_INST_ALIGNED        = 10'd7; // OOP
   localparam MHPME_INST_DECODED        = 10'd8; // OOP
   localparam MHPME_INST_MUL            = 10'd9;
   localparam MHPME_INST_DIV            = 10'd10;
   localparam MHPME_INST_LOAD           = 10'd11;
   localparam MHPME_INST_STORE          = 10'd12;
   localparam MHPME_INST_MALOAD         = 10'd13;
   localparam MHPME_INST_MASTORE        = 10'd14;
   localparam MHPME_INST_ALU            = 10'd15;
   localparam MHPME_INST_CSRREAD        = 10'd16;
   localparam MHPME_INST_CSRRW          = 10'd17;
   localparam MHPME_INST_CSRWRITE       = 10'd18;
   localparam MHPME_INST_EBREAK         = 10'd19;
   localparam MHPME_INST_ECALL          = 10'd20;
   localparam MHPME_INST_FENCE          = 10'd21;
   localparam MHPME_INST_FENCEI         = 10'd22;
   localparam MHPME_INST_MRET           = 10'd23;
   localparam MHPME_INST_BRANCH         = 10'd24;
   localparam MHPME_BRANCH_MP           = 10'd25;
   localparam MHPME_BRANCH_TAKEN        = 10'd26;
   localparam MHPME_BRANCH_NOTP         = 10'd27;
   localparam MHPME_FETCH_STALL         = 10'd28; // OOP
   localparam MHPME_DECODE_STALL        = 10'd30; // OOP
   localparam MHPME_POSTSYNC_STALL      = 10'd31; // OOP
   localparam MHPME_PRESYNC_STALL       = 10'd32; // OOP
   localparam MHPME_LSU_SB_WB_STALL     = 10'd34; // OOP
   localparam MHPME_DMA_DCCM_STALL      = 10'd35; // OOP
   localparam MHPME_DMA_ICCM_STALL      = 10'd36; // OOP
   localparam MHPME_EXC_TAKEN           = 10'd37;
   localparam MHPME_TIMER_INT_TAKEN     = 10'd38;
   localparam MHPME_EXT_INT_TAKEN       = 10'd39;
   localparam MHPME_FLUSH_LOWER         = 10'd40;
   localparam MHPME_BR_ERROR            = 10'd41;
   localparam MHPME_IBUS_TRANS          = 10'd42; // OOP
   localparam MHPME_DBUS_TRANS          = 10'd43; // OOP
   localparam MHPME_DBUS_MA_TRANS       = 10'd44; // OOP
   localparam MHPME_IBUS_ERROR          = 10'd45; // OOP
   localparam MHPME_DBUS_ERROR          = 10'd46; // OOP
   localparam MHPME_IBUS_STALL          = 10'd47; // OOP
   localparam MHPME_DBUS_STALL          = 10'd48; // OOP
   localparam MHPME_INT_DISABLED        = 10'd49; // OOP
   localparam MHPME_INT_STALLED         = 10'd50; // OOP
   localparam MHPME_INST_BITMANIP       = 10'd54;
   localparam MHPME_DBUS_LOAD           = 10'd55;
   localparam MHPME_DBUS_STORE          = 10'd56;
   // Counts even during sleep state
   localparam MHPME_SLEEP_CYC           = 10'd512; // OOP
   localparam MHPME_DMA_READ_ALL        = 10'd513; // OOP
   localparam MHPME_DMA_WRITE_ALL       = 10'd514; // OOP
   localparam MHPME_DMA_READ_DCCM       = 10'd515; // OOP
   localparam MHPME_DMA_WRITE_DCCM      = 10'd516; // OOP

   // Pack the event selects into a vector for genvar
   assign mhpme_vec[0][9:0] = mhpme3[9:0];
   assign mhpme_vec[1][9:0] = mhpme4[9:0];
   assign mhpme_vec[2][9:0] = mhpme5[9:0];
   assign mhpme_vec[3][9:0] = mhpme6[9:0];

   // only consider committed itypes
   //logic [3:0] pmu_i0_itype_qual;
   assign pmu_i0_itype_qual[3:0] = dec_tlu_packet_r.pmu_i0_itype[3:0] & {4{tlu_i0_commit_cmt}};

   // Generate the muxed incs for all counters based on event type
   for (genvar i=0 ; i < 4; i++) begin
      assign mhpmc_inc_r[i] =  {{~mcountinhibit[i+3]}} &
           (
             ({1{(mhpme_vec[i][9:0] == MHPME_CLK_ACTIVE      )}} & 1'b1) |
             ({1{(mhpme_vec[i][9:0] == MHPME_ICACHE_HIT      )}} & {ifu_pmu_ic_hit}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_ICACHE_MISS     )}} & {ifu_pmu_ic_miss}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_COMMIT     )}} & {tlu_i0_commit_cmt & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_COMMIT_16B )}} & {tlu_i0_commit_cmt & ~exu_pmu_i0_pc4 & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_COMMIT_32B )}} & {tlu_i0_commit_cmt &  exu_pmu_i0_pc4 & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_ALIGNED    )}} & ifu_pmu_instr_aligned)  |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_DECODED    )}} & dec_pmu_instr_decoded)  |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_MUL        )}} & {(pmu_i0_itype_qual == MUL)})     |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_DIV        )}} & {dec_tlu_packet_r.pmu_divide  & tlu_i0_commit_cmt & ~illegal_r})     |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_LOAD       )}} & {(pmu_i0_itype_qual == LOAD)})    |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_STORE      )}} & {(pmu_i0_itype_qual == STORE)})   |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_MALOAD     )}} & {(pmu_i0_itype_qual == LOAD)} &
                                                                      {1{dec_tlu_packet_r.pmu_lsu_misaligned}})    |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_MASTORE    )}} & {(pmu_i0_itype_qual == STORE)} &
                                                                      {1{dec_tlu_packet_r.pmu_lsu_misaligned}})    |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_ALU        )}} & {(pmu_i0_itype_qual == ALU)})     |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_CSRREAD    )}} & {(pmu_i0_itype_qual == CSRREAD)}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_CSRWRITE   )}} & {(pmu_i0_itype_qual == CSRWRITE)})|
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_CSRRW      )}} & {(pmu_i0_itype_qual == CSRRW)})   |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_EBREAK     )}} & {(pmu_i0_itype_qual == EBREAK)})  |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_ECALL      )}} & {(pmu_i0_itype_qual == ECALL)})   |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_FENCE      )}} & {(pmu_i0_itype_qual == FENCE)})   |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_FENCEI     )}} & {(pmu_i0_itype_qual == FENCEI)})  |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_MRET       )}} & {(pmu_i0_itype_qual == MRET)})    |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_BRANCH     )}} & {
                                                                     ((pmu_i0_itype_qual == CONDBR) | (pmu_i0_itype_qual == JAL))})   |
             ({1{(mhpme_vec[i][9:0] == MHPME_BRANCH_MP       )}} & {exu_pmu_i0_br_misp & tlu_i0_commit_cmt & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_BRANCH_TAKEN    )}} & {exu_pmu_i0_br_ataken & tlu_i0_commit_cmt & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_BRANCH_NOTP     )}} & {dec_tlu_packet_r.pmu_i0_br_unpred & tlu_i0_commit_cmt & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_FETCH_STALL     )}} & { ifu_pmu_fetch_stall}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DECODE_STALL    )}} & { dec_pmu_decode_stall}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_POSTSYNC_STALL  )}} & {dec_pmu_postsync_stall}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_PRESYNC_STALL   )}} & {dec_pmu_presync_stall}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_LSU_SB_WB_STALL )}} & { lsu_store_stall_any}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_DCCM_STALL  )}} & { dma_dccm_stall_any}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_ICCM_STALL  )}} & { dma_iccm_stall_any}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_EXC_TAKEN       )}} & { (i0_exception_valid_r | i0_trigger_hit_r | lsu_exc_valid_r)}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_TIMER_INT_TAKEN )}} & { take_timer_int | take_int_timer0_int | take_int_timer1_int}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_EXT_INT_TAKEN   )}} & { take_ext_int}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_FLUSH_LOWER     )}} & { tlu_flush_lower_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_BR_ERROR        )}} & {(dec_tlu_br0_error_r | dec_tlu_br0_start_error_r) & rfpc_i0_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_IBUS_TRANS      )}} & {ifu_pmu_bus_trxn}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_TRANS      )}} & {lsu_pmu_bus_trxn}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_MA_TRANS   )}} & {lsu_pmu_bus_misaligned}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_IBUS_ERROR      )}} & {ifu_pmu_bus_error}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_ERROR      )}} & {lsu_pmu_bus_error}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_IBUS_STALL      )}} & {ifu_pmu_bus_busy}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_STALL      )}} & {lsu_pmu_bus_busy}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INT_DISABLED    )}} & {~mstatus[MSTATUS_MIE]}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INT_STALLED     )}} & {~mstatus[MSTATUS_MIE] & |(mip[5:0] & mie[5:0])}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_INST_BITMANIP     )}} & {(pmu_i0_itype_qual == BITMANIPU)}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_LOAD       )}} & {tlu_i0_commit_cmt & lsu_pmu_load_external_r & ~illegal_r}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DBUS_STORE      )}} & {tlu_i0_commit_cmt & lsu_pmu_store_external_r & ~illegal_r}) |
             // These count even during sleep
             ({1{(mhpme_vec[i][9:0] == MHPME_SLEEP_CYC       )}} & {dec_tlu_pmu_fw_halted}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_READ_ALL    )}} & {dma_pmu_any_read}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_WRITE_ALL   )}} & {dma_pmu_any_write}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_READ_DCCM   )}} & {dma_pmu_dccm_read}) |
             ({1{(mhpme_vec[i][9:0] == MHPME_DMA_WRITE_DCCM  )}} & {dma_pmu_dccm_write})
             );
   end


   if(pt.FAST_INTERRUPT_REDIRECT) begin : genblock2

`ifdef RV_USER_MODE
   rvdffie #(33)  mstatus_ff (.*, .clk(free_l2clk),
                             .din({mdseac_locked_ns, lsu_single_ecc_error_r, lsu_exc_valid_r, lsu_i0_exc_r,
                                   take_ext_int_start,    take_ext_int_start_d1, take_ext_int_start_d2, ext_int_freeze,
                                   mip_ns[5:0], mcyclel_cout & ~wr_mcycleh_r & mcyclel_cout_in,
                                   minstret_enable, minstretl_cout_ns, fw_halted_ns,
                                   meicidpl_ns[3:0], icache_rd_valid, icache_wr_valid, mhpmc_inc_r[3:0], perfcnt_halted,
                                   mstatus_ns[3:0]}),
                             .dout({mdseac_locked_f, lsu_single_ecc_error_r_d1, lsu_exc_valid_r_d1, lsu_i0_exc_r_d1,
                                    take_ext_int_start_d1, take_ext_int_start_d2, take_ext_int_start_d3, ext_int_freeze_d1,
                                    mip[5:0], mcyclel_cout_f, minstret_enable_f, minstretl_cout_f,
                                    fw_halted, meicidpl[3:0], icache_rd_valid_f, icache_wr_valid_f,
                                    mhpmc_inc_r_d1[3:0], perfcnt_halted_d1,
                                    mstatus[3:0]}));
`else
   rvdffie #(31)  mstatus_ff (.*, .clk(free_l2clk),
                             .din({mdseac_locked_ns, lsu_single_ecc_error_r, lsu_exc_valid_r, lsu_i0_exc_r,
                                   take_ext_int_start,    take_ext_int_start_d1, take_ext_int_start_d2, ext_int_freeze,
                                   mip_ns[5:0], mcyclel_cout & ~wr_mcycleh_r & mcyclel_cout_in,
                                   minstret_enable, minstretl_cout_ns, fw_halted_ns,
                                   meicidpl_ns[3:0], icache_rd_valid, icache_wr_valid, mhpmc_inc_r[3:0], perfcnt_halted,
                                   mstatus_ns[1:0]}),
                             .dout({mdseac_locked_f, lsu_single_ecc_error_r_d1, lsu_exc_valid_r_d1, lsu_i0_exc_r_d1,
                                    take_ext_int_start_d1, take_ext_int_start_d2, take_ext_int_start_d3, ext_int_freeze_d1,
                                    mip[5:0], mcyclel_cout_f, minstret_enable_f, minstretl_cout_f,
                                    fw_halted, meicidpl[3:0], icache_rd_valid_f, icache_wr_valid_f,
                                    mhpmc_inc_r_d1[3:0], perfcnt_halted_d1,
                                    mstatus[1:0]}));

`endif

   end
   else begin : genblock2
`ifdef RV_USER_MODE
   rvdffie #(29)  mstatus_ff (.*, .clk(free_l2clk),
                             .din({mdseac_locked_ns, lsu_single_ecc_error_r, lsu_exc_valid_r, lsu_i0_exc_r,
                                   mip_ns[5:0], mcyclel_cout & ~wr_mcycleh_r & mcyclel_cout_in,
                                   minstret_enable, minstretl_cout_ns, fw_halted_ns,
                                   meicidpl_ns[3:0], icache_rd_valid, icache_wr_valid, mhpmc_inc_r[3:0], perfcnt_halted,
                                   mstatus_ns[3:0]}),
                             .dout({mdseac_locked_f, lsu_single_ecc_error_r_d1, lsu_exc_valid_r_d1, lsu_i0_exc_r_d1,
                                    mip[5:0], mcyclel_cout_f, minstret_enable_f, minstretl_cout_f,
                                    fw_halted, meicidpl[3:0], icache_rd_valid_f, icache_wr_valid_f,
                                    mhpmc_inc_r_d1[3:0], perfcnt_halted_d1,
                                    mstatus[3:0]}));
`else
   rvdffie #(27)  mstatus_ff (.*, .clk(free_l2clk),
                             .din({mdseac_locked_ns, lsu_single_ecc_error_r, lsu_exc_valid_r, lsu_i0_exc_r,
                                   mip_ns[5:0], mcyclel_cout & ~wr_mcycleh_r & mcyclel_cout_in,
                                   minstret_enable, minstretl_cout_ns, fw_halted_ns,
                                   meicidpl_ns[3:0], icache_rd_valid, icache_wr_valid, mhpmc_inc_r[3:0], perfcnt_halted,
                                   mstatus_ns[1:0]}),
                             .dout({mdseac_locked_f, lsu_single_ecc_error_r_d1, lsu_exc_valid_r_d1, lsu_i0_exc_r_d1,
                                    mip[5:0], mcyclel_cout_f, minstret_enable_f, minstretl_cout_f,
                                    fw_halted, meicidpl[3:0], icache_rd_valid_f, icache_wr_valid_f,
                                    mhpmc_inc_r_d1[3:0], perfcnt_halted_d1,
                                    mstatus[1:0]}));
`endif
   end

   assign perfcnt_halted = ((dec_tlu_dbg_halted & dcsr[DCSR_STOPC]) | dec_tlu_pmu_fw_halted);
   assign perfcnt_during_sleep[3:0] = {4{~(dec_tlu_dbg_halted & dcsr[DCSR_STOPC])}} & {mhpme_vec[3][9],mhpme_vec[2][9],mhpme_vec[1][9],mhpme_vec[0][9]};

   assign dec_tlu_perfcnt0 = mhpmc_inc_r_d1[0] & ~(perfcnt_halted_d1 & ~perfcnt_during_sleep[0]);
   assign dec_tlu_perfcnt1 = mhpmc_inc_r_d1[1] & ~(perfcnt_halted_d1 & ~perfcnt_during_sleep[1]);
   assign dec_tlu_perfcnt2 = mhpmc_inc_r_d1[2] & ~(perfcnt_halted_d1 & ~perfcnt_during_sleep[2]);
   assign dec_tlu_perfcnt3 = mhpmc_inc_r_d1[3] & ~(perfcnt_halted_d1 & ~perfcnt_during_sleep[3]);

   // ----------------------------------------------------------------------
   // MHPMC3H(RW), MHPMC3(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 3

   assign mhpmc3_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC3);
   assign mhpmc3_wr_en1 = (~perfcnt_halted | perfcnt_during_sleep[0]) & (|(mhpmc_inc_r[0]));
   assign mhpmc3_wr_en  = mhpmc3_wr_en0 | mhpmc3_wr_en1;
   assign mhpmc3_incr[63:0] = {mhpmc3h[31:0],mhpmc3[31:0]} + {63'b0, 1'b1};
   assign mhpmc3_ns[31:0] = mhpmc3_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc3_incr[31:0];
   rvdffe #(32)  mhpmc3_ff (.*, .clk(free_l2clk), .en(mhpmc3_wr_en), .din(mhpmc3_ns[31:0]), .dout(mhpmc3[31:0]));

   assign mhpmc3h_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC3H);
   assign mhpmc3h_wr_en  = mhpmc3h_wr_en0 | mhpmc3_wr_en1;
   assign mhpmc3h_ns[31:0] = mhpmc3h_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc3_incr[63:32];
   rvdffe #(32)  mhpmc3h_ff (.*, .clk(free_l2clk), .en(mhpmc3h_wr_en), .din(mhpmc3h_ns[31:0]), .dout(mhpmc3h[31:0]));

   // ----------------------------------------------------------------------
   // MHPMC4H(RW), MHPMC4(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 4

   assign mhpmc4_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC4);
   assign mhpmc4_wr_en1 = (~perfcnt_halted | perfcnt_during_sleep[1]) & (|(mhpmc_inc_r[1]));
   assign mhpmc4_wr_en  = mhpmc4_wr_en0 | mhpmc4_wr_en1;
   assign mhpmc4_incr[63:0] = {mhpmc4h[31:0],mhpmc4[31:0]} + {63'b0,1'b1};
   assign mhpmc4_ns[31:0] = mhpmc4_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc4_incr[31:0];
   rvdffe #(32)  mhpmc4_ff (.*, .clk(free_l2clk), .en(mhpmc4_wr_en), .din(mhpmc4_ns[31:0]), .dout(mhpmc4[31:0]));

   assign mhpmc4h_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC4H);
   assign mhpmc4h_wr_en  = mhpmc4h_wr_en0 | mhpmc4_wr_en1;
   assign mhpmc4h_ns[31:0] = mhpmc4h_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc4_incr[63:32];
   rvdffe #(32)  mhpmc4h_ff (.*, .clk(free_l2clk), .en(mhpmc4h_wr_en), .din(mhpmc4h_ns[31:0]), .dout(mhpmc4h[31:0]));

   // ----------------------------------------------------------------------
   // MHPMC5H(RW), MHPMC5(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 5

   assign mhpmc5_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC5);
   assign mhpmc5_wr_en1 = (~perfcnt_halted | perfcnt_during_sleep[2]) & (|(mhpmc_inc_r[2]));
   assign mhpmc5_wr_en  = mhpmc5_wr_en0 | mhpmc5_wr_en1;
   assign mhpmc5_incr[63:0] = {mhpmc5h[31:0],mhpmc5[31:0]} + {63'b0,1'b1};
   assign mhpmc5_ns[31:0] = mhpmc5_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc5_incr[31:0];
   rvdffe #(32)  mhpmc5_ff (.*, .clk(free_l2clk), .en(mhpmc5_wr_en), .din(mhpmc5_ns[31:0]), .dout(mhpmc5[31:0]));

   assign mhpmc5h_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC5H);
   assign mhpmc5h_wr_en  = mhpmc5h_wr_en0 | mhpmc5_wr_en1;
   assign mhpmc5h_ns[31:0] = mhpmc5h_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc5_incr[63:32];
   rvdffe #(32)  mhpmc5h_ff (.*, .clk(free_l2clk), .en(mhpmc5h_wr_en), .din(mhpmc5h_ns[31:0]), .dout(mhpmc5h[31:0]));

   // ----------------------------------------------------------------------
   // MHPMC6H(RW), MHPMC6(RW)
   // [63:32][31:0] : Hardware Performance Monitor Counter 6

   assign mhpmc6_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC6);
   assign mhpmc6_wr_en1 = (~perfcnt_halted | perfcnt_during_sleep[3]) & (|(mhpmc_inc_r[3]));
   assign mhpmc6_wr_en  = mhpmc6_wr_en0 | mhpmc6_wr_en1;
   assign mhpmc6_incr[63:0] = {mhpmc6h[31:0],mhpmc6[31:0]} + {63'b0,1'b1};
   assign mhpmc6_ns[31:0] = mhpmc6_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc6_incr[31:0];
   rvdffe #(32)  mhpmc6_ff (.*, .clk(free_l2clk), .en(mhpmc6_wr_en), .din(mhpmc6_ns[31:0]), .dout(mhpmc6[31:0]));

   assign mhpmc6h_wr_en0 = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPMC6H);
   assign mhpmc6h_wr_en  = mhpmc6h_wr_en0 | mhpmc6_wr_en1;
   assign mhpmc6h_ns[31:0] = mhpmc6h_wr_en0 ? dec_csr_wrdata_r[31:0] : mhpmc6_incr[63:32];
   rvdffe #(32)  mhpmc6h_ff (.*, .clk(free_l2clk), .en(mhpmc6h_wr_en), .din(mhpmc6h_ns[31:0]), .dout(mhpmc6h[31:0]));

   // ----------------------------------------------------------------------
   // MHPME3(RW)
   // [9:0] : Hardware Performance Monitor Event 3

   // we only have events 0-56 with holes, 512-516, HPME* are WARL so zero otherwise.
   assign zero_event_r = ( (dec_csr_wrdata_r[9:0] > 10'd516) |
                           (|dec_csr_wrdata_r[31:10]) |
                           ((dec_csr_wrdata_r[9:0] < 10'd512) & (dec_csr_wrdata_r[9:0] > 10'd56)) |
                           ((dec_csr_wrdata_r[9:0] < 10'd54) & (dec_csr_wrdata_r[9:0] > 10'd50)) |
                           (dec_csr_wrdata_r[9:0] == 10'd29) |
                           (dec_csr_wrdata_r[9:0] == 10'd33)
                           );

   assign event_r[9:0] = zero_event_r ? '0 : dec_csr_wrdata_r[9:0];

   assign wr_mhpme3_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPME3);
   rvdffe #(10)  mhpme3_ff (.*, .en(wr_mhpme3_r), .din(event_r[9:0]), .dout(mhpme3[9:0]));
   // ----------------------------------------------------------------------
   // MHPME4(RW)
   // [9:0] : Hardware Performance Monitor Event 4

   assign wr_mhpme4_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPME4);
   rvdffe #(10)  mhpme4_ff (.*, .en(wr_mhpme4_r), .din(event_r[9:0]), .dout(mhpme4[9:0]));
   // ----------------------------------------------------------------------
   // MHPME5(RW)
   // [9:0] : Hardware Performance Monitor Event 5

   assign wr_mhpme5_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPME5);
   rvdffe #(10)  mhpme5_ff (.*, .en(wr_mhpme5_r), .din(event_r[9:0]), .dout(mhpme5[9:0]));
   // ----------------------------------------------------------------------
   // MHPME6(RW)
   // [9:0] : Hardware Performance Monitor Event 6

   assign wr_mhpme6_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MHPME6);
   rvdffe #(10)  mhpme6_ff (.*, .en(wr_mhpme6_r), .din(event_r[9:0]), .dout(mhpme6[9:0]));

   //----------------------------------------------------------------------
   // Performance Monitor Counters section ends
   //----------------------------------------------------------------------
   // ----------------------------------------------------------------------

   // ----------------------------------------------------------------------
   // MCOUNTEREN
   // [31:3] : Reserved, read 0x0
   // [2]    : INSTRET user-mode access disable
   // [1]    : reserved, read 0x0
   // [0]    : CYCLE user-mode access disable

`ifdef RV_USER_MODE

   localparam MCOUNTEREN                = 12'h306;

   assign wr_mcounteren_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCOUNTEREN);
   rvdffs #(6) mcounteren_ff (.*, .clk(csr_wr_clk), .en(wr_mcounteren_r), .din({dec_csr_wrdata_r[6:2], dec_csr_wrdata_r[0]}), .dout(mcounteren));

`endif

   // MCOUNTINHIBIT(RW)
   // [31:7] : Reserved, read 0x0
   // [6]    : HPM6 disable
   // [5]    : HPM5 disable
   // [4]    : HPM4 disable
   // [3]    : HPM3 disable
   // [2]    : MINSTRET disable
   // [1]    : reserved, read 0x0
   // [0]    : MCYCLE disable

   assign wr_mcountinhibit_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MCOUNTINHIBIT);
   rvdffs #(6)  mcountinhibit_ff (.*, .clk(csr_wr_clk), .en(wr_mcountinhibit_r), .din({dec_csr_wrdata_r[6:2], dec_csr_wrdata_r[0]}), .dout({mcountinhibit[6:2], mcountinhibit[0]}));
   assign mcountinhibit[1] = 1'b0;

   //--------------------------------------------------------------------------------
   // trace
   //--------------------------------------------------------------------------------
   logic [4:0] dec_tlu_exc_cause_wb1_raw, dec_tlu_exc_cause_wb2;
   logic       dec_tlu_int_valid_wb1_raw, dec_tlu_int_valid_wb2;

   assign {dec_tlu_i0_valid_wb1,
           dec_tlu_i0_exc_valid_wb1,
           dec_tlu_exc_cause_wb1_raw[4:0],
           dec_tlu_int_valid_wb1_raw}  =   {8{~dec_tlu_trace_disable}} & {i0_valid_wb,
                                                                          i0_exception_valid_r_d1 | lsu_i0_exc_r_d1 | (trigger_hit_r_d1 & ~trigger_hit_dmode_r_d1),
                                                                          exc_cause_wb[4:0],
                                                                          interrupt_valid_r_d1};



  // skid buffer for ints, reduces trace port count by 1
   rvdffie #(.WIDTH(6), .OVERRIDE(1))  traceskidff (.*,  .clk(clk),
                        .din ({dec_tlu_exc_cause_wb1_raw[4:0],
                               dec_tlu_int_valid_wb1_raw}),
                        .dout({dec_tlu_exc_cause_wb2[4:0],
                               dec_tlu_int_valid_wb2}));
   //skid for ints
   assign dec_tlu_exc_cause_wb1[4:0] =  dec_tlu_int_valid_wb2 ? dec_tlu_exc_cause_wb2[4:0] : dec_tlu_exc_cause_wb1_raw[4:0];
   assign dec_tlu_int_valid_wb1 = dec_tlu_int_valid_wb2;

   assign dec_tlu_mtval_wb1  = mtval[31:0];

   // end trace
   //--------------------------------------------------------------------------------


   // ----------------------------------------------------------------------
   // CSR read mux
   // ----------------------------------------------------------------------

assign dec_tlu_presync_d = presync & dec_csr_any_unq_d & ~dec_csr_wen_unq_d;
assign dec_tlu_postsync_d = postsync & dec_csr_any_unq_d;

   // allow individual configuration of these features
assign conditionally_illegal = ((csr_mitcnt0 | csr_mitcnt1 | csr_mitb0 | csr_mitb1 | csr_mitctl0 | csr_mitctl1) & ~|pt.TIMER_LEGAL_EN);

assign valid_csr = ( legal & (~(csr_dcsr | csr_dpc | csr_dmst | csr_dicawics | csr_dicad0 | csr_dicad0h | csr_dicad1 | csr_dicago) | dbg_tlu_halted_f)
                     & ~fast_int_meicpct & ~conditionally_illegal);

assign dec_csr_legal_d = ( dec_csr_any_unq_d &
                           valid_csr &          // of a valid CSR
                           ~(dec_csr_wen_unq_d & (csr_mvendorid | csr_marchid | csr_mimpid | csr_mhartid | csr_mdseac | csr_meihap)) // that's not a write to a RO CSR
                           );
   // CSR read mux
assign dec_csr_rddata_d[31:0] = (
`ifdef RV_USER_MODE
                                  ({32{csr_misa}}      & 32'h40101104) |
`else
                                  ({32{csr_misa}}      & 32'h40001104) |
`endif
                                  ({32{csr_mvendorid}} & 32'h00000045) |
                                  ({32{csr_marchid}}   & 32'h00000010) |
                                  ({32{csr_mimpid}}    & 32'h4) |
                                  ({32{csr_mhartid}}   & {core_id[31:4], 4'b0}) |
`ifdef RV_USER_MODE
                                  ({32{csr_mstatus}}   & {14'b0, mstatus[MSTATUS_MPRV], 4'b0, ~mstatus[MSTATUS_MPP], ~mstatus[MSTATUS_MPP], 3'b0, mstatus[MSTATUS_MPIE], 3'b0, mstatus[MSTATUS_MIE], 3'b0}) |
`else
                                  ({32{csr_mstatus}}   & {19'b0, 2'b11, 3'b0, mstatus[MSTATUS_MPIE], 3'b0, mstatus[MSTATUS_MIE], 3'b0}) |
`endif
                                  ({32{csr_mtvec}}     & {mtvec[30:1], 1'b0, mtvec[0]}) |
                                  ({32{csr_mip}}       & {1'b0, mip[5:3], 16'b0, mip[2], 3'b0, mip[1], 3'b0, mip[0], 3'b0}) |
                                  ({32{csr_mie}}       & {1'b0, mie[5:3], 16'b0, mie[2], 3'b0, mie[1], 3'b0, mie[0], 3'b0}) |
                                  ({32{csr_mcyclel}}   & mcyclel[31:0]) |
                                  ({32{csr_mcycleh}}   & mcycleh_inc[31:0]) |
                                  ({32{csr_minstretl}} & minstretl_read[31:0]) |
                                  ({32{csr_minstreth}} & minstreth_read[31:0]) |
                                  ({32{csr_mscratch}}  & mscratch[31:0]) |
                                  ({32{csr_mepc}}      & {mepc[31:1], 1'b0}) |
                                  ({32{csr_mcause}}    & mcause[31:0]) |
                                  ({32{csr_mscause}}   & {28'b0, mscause[3:0]}) |
                                  ({32{csr_mtval}}     & mtval[31:0]) |
                                  ({32{csr_mrac}}      & mrac[31:0]) |
                                  ({32{csr_mdseac}}    & mdseac[31:0]) |
                                  ({32{csr_meivt}}     & {meivt[31:10], 10'b0}) |
                                  ({32{csr_meihap}}    & {meivt[31:10], meihap[9:2], 2'b0}) |
                                  ({32{csr_meicurpl}}  & {28'b0, meicurpl[3:0]}) |
                                  ({32{csr_meicidpl}}  & {28'b0, meicidpl[3:0]}) |
                                  ({32{csr_meipt}}     & {28'b0, meipt[3:0]}) |
                                  ({32{csr_mcgc}}      & {22'b0, mcgc[9:0]}) |
                                  ({32{csr_mfdc}}      & {13'b0, mfdc[18:0]}) |
                                  ({32{csr_dcsr}}      & {16'h4000, dcsr[15:2], 2'b11}) |
                                  ({32{csr_dpc}}       & {dpc[31:1], 1'b0}) |
                                  ({32{csr_dicad0}}    & dicad0[31:0]) |
                                  ({32{csr_dicad0h}}   & dicad0h[31:0]) |
                                  ({32{csr_dicad1}}    & dicad1[31:0]) |
                                  ({32{csr_dicawics}}  & {7'b0, dicawics[16], 2'b0, dicawics[15:14], 3'b0, dicawics[13:0], 3'b0}) |
                                  ({32{csr_mtsel}}     & {30'b0, mtsel[1:0]}) |
                                  ({32{csr_mtdata1}}   & {mtdata1_tsel_out[31:0]}) |
                                  ({32{csr_mtdata2}}   & {mtdata2_tsel_out[31:0]}) |
                                  ({32{csr_micect}}    & {micect[31:0]}) |
                                  ({32{csr_miccmect}}  & {miccmect[31:0]}) |
                                  ({32{csr_mdccmect}}  & {mdccmect[31:0]}) |
                                  ({32{csr_mhpmc3}}    & mhpmc3[31:0]) |
                                  ({32{csr_mhpmc4}}    & mhpmc4[31:0]) |
                                  ({32{csr_mhpmc5}}    & mhpmc5[31:0]) |
                                  ({32{csr_mhpmc6}}    & mhpmc6[31:0]) |
                                  ({32{csr_mhpmc3h}}   & mhpmc3h[31:0]) |
                                  ({32{csr_mhpmc4h}}   & mhpmc4h[31:0]) |
                                  ({32{csr_mhpmc5h}}   & mhpmc5h[31:0]) |
                                  ({32{csr_mhpmc6h}}   & mhpmc6h[31:0]) |
                                  ({32{csr_mfdht}}     & {26'b0, mfdht[5:0]}) |
                                  ({32{csr_mfdhs}}     & {30'b0, mfdhs[1:0]}) |
                                  ({32{csr_mhpme3}}    & {22'b0,mhpme3[9:0]}) |
                                  ({32{csr_mhpme4}}    & {22'b0,mhpme4[9:0]}) |
                                  ({32{csr_mhpme5}}    & {22'b0,mhpme5[9:0]}) |
                                  ({32{csr_mhpme6}}    & {22'b0,mhpme6[9:0]}) |
`ifdef RV_USER_MODE
                                  ({32{csr_menvcfg}}   & 32'd0) |
                                  ({32{csr_menvcfgh}}  & 32'd0) |
                                  ({32{csr_mcounteren}}    & {25'b0, mcounteren[5:1], 1'b0, mcounteren[0]}) |
                                  ({32{csr_cyclel}}    & mcyclel[31:0]) |
                                  ({32{csr_cycleh}}    & mcycleh_inc[31:0]) |
                                  ({32{csr_instretl}}  & minstretl_read[31:0]) |
                                  ({32{csr_instreth}}  & minstreth_read[31:0]) |
                                  ({32{csr_hpmc3}}     & mhpmc3[31:0]) |
                                  ({32{csr_hpmc4}}     & mhpmc4[31:0]) |
                                  ({32{csr_hpmc5}}     & mhpmc5[31:0]) |
                                  ({32{csr_hpmc6}}     & mhpmc6[31:0]) |
                                  ({32{csr_hpmc3h}}    & mhpmc3h[31:0]) |
                                  ({32{csr_hpmc4h}}    & mhpmc4h[31:0]) |
                                  ({32{csr_hpmc5h}}    & mhpmc5h[31:0]) |
                                  ({32{csr_hpmc6h}}    & mhpmc6h[31:0]) |
                                  ({32{csr_mseccfgl}}  & {29'd0, mseccfg}) |
                                  ({32{csr_mseccfgh}}  & 32'd0) | // All bits are WPRI
`endif
                                  ({32{csr_mcountinhibit}} & {25'b0, mcountinhibit[6:0]}) |
                                  ({32{csr_mpmc}}      & {30'b0, mpmc[1], 1'b0}) |
                                  ({32{dec_timer_read_d}} & dec_timer_rddata_d[31:0]) |
                                  ({32{dec_pmp_read_d}} & dec_pmp_rddata_d[31:0])
                                  );



endmodule // el2_dec_tlu_ctl

module el2_dec_timer_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic clk,
   input logic free_l2clk,
   input logic csr_wr_clk,
   input logic rst_l,
   input logic        dec_csr_wen_r_mod,      // csr write enable at wb
   input logic [11:0] dec_csr_wraddr_r,      // write address for csr
   input logic [31:0] dec_csr_wrdata_r,   // csr write data at wb

   input logic csr_mitctl0,
   input logic csr_mitctl1,
   input logic csr_mitb0,
   input logic csr_mitb1,
   input logic csr_mitcnt0,
   input logic csr_mitcnt1,


   input logic dec_pause_state, // Paused
   input logic dec_tlu_pmu_fw_halted, // pmu/fw halted
   input logic internal_dbg_halt_timers, // debug halted

   output logic [31:0] dec_timer_rddata_d, // timer CSR read data
   output logic        dec_timer_read_d, // timer CSR address match
   output logic        dec_timer_t0_pulse, // timer0 int
   output logic        dec_timer_t1_pulse, // timer1 int

   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input  logic        scan_mode
   /*pragma coverage on*/
   );
   localparam MITCTL_ENABLE             = 0;
   localparam MITCTL_ENABLE_HALTED      = 1;
   localparam MITCTL_ENABLE_PAUSED      = 2;

   logic [31:0] mitcnt0_ns, mitcnt0, mitcnt1_ns, mitcnt1, mitb0, mitb1, mitb0_b, mitb1_b, mitcnt0_inc, mitcnt1_inc;
   logic [2:0] mitctl0_ns, mitctl0;
   logic [3:0] mitctl1_ns, mitctl1;
   logic wr_mitcnt0_r, wr_mitcnt1_r, wr_mitb0_r, wr_mitb1_r, wr_mitctl0_r, wr_mitctl1_r;
   logic mitcnt0_inc_ok, mitcnt1_inc_ok;
   logic mitcnt0_inc_cout, mitcnt1_inc_cout;
 logic mit0_match_ns;
 logic mit1_match_ns;
 logic mitctl0_0_b_ns;
 logic mitctl0_0_b;
 logic mitctl1_0_b_ns;
 logic mitctl1_0_b;

   assign mit0_match_ns = (mitcnt0[31:0] >= mitb0[31:0]);
   assign mit1_match_ns = (mitcnt1[31:0] >= mitb1[31:0]);

   assign dec_timer_t0_pulse = mit0_match_ns;
   assign dec_timer_t1_pulse = mit1_match_ns;
   // ----------------------------------------------------------------------
   // MITCNT0 (RW)
   // [31:0] : Internal Timer Counter 0

   localparam MITCNT0       = 12'h7d2;

   assign wr_mitcnt0_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITCNT0);

   assign mitcnt0_inc_ok = mitctl0[MITCTL_ENABLE] & (~dec_pause_state | mitctl0[MITCTL_ENABLE_PAUSED]) & (~dec_tlu_pmu_fw_halted | mitctl0[MITCTL_ENABLE_HALTED]) & ~internal_dbg_halt_timers;

   assign {mitcnt0_inc_cout, mitcnt0_inc[7:0]} = mitcnt0[7:0] + {7'b0, 1'b1};
   assign mitcnt0_inc[31:8] = mitcnt0[31:8] + {23'b0, mitcnt0_inc_cout};

   assign mitcnt0_ns[31:0]  = wr_mitcnt0_r ? dec_csr_wrdata_r[31:0] : mit0_match_ns ? 'b0 : mitcnt0_inc[31:0];

   rvdffe #(24) mitcnt0_ffb      (.*, .clk(free_l2clk), .en(wr_mitcnt0_r | (mitcnt0_inc_ok & mitcnt0_inc_cout) | mit0_match_ns), .din(mitcnt0_ns[31:8]), .dout(mitcnt0[31:8]));
   rvdffe #(8)  mitcnt0_ffa      (.*, .clk(free_l2clk), .en(wr_mitcnt0_r | mitcnt0_inc_ok | mit0_match_ns),                       .din(mitcnt0_ns[7:0]), .dout(mitcnt0[7:0]));

   // ----------------------------------------------------------------------
   // MITCNT1 (RW)
   // [31:0] : Internal Timer Counter 0

   localparam MITCNT1       = 12'h7d5;

   assign wr_mitcnt1_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITCNT1);

   assign mitcnt1_inc_ok = mitctl1[MITCTL_ENABLE] &
                           (~dec_pause_state | mitctl1[MITCTL_ENABLE_PAUSED]) &
                           (~dec_tlu_pmu_fw_halted | mitctl1[MITCTL_ENABLE_HALTED]) &
                           ~internal_dbg_halt_timers &
                           (~mitctl1[3] | mit0_match_ns);

   // only inc MITCNT1 if not cascaded with 0, or if 0 overflows
   assign {mitcnt1_inc_cout, mitcnt1_inc[7:0]} = mitcnt1[7:0] + {7'b0, 1'b1};
   assign mitcnt1_inc[31:8] = mitcnt1[31:8] + {23'b0, mitcnt1_inc_cout};

   assign mitcnt1_ns[31:0]  = wr_mitcnt1_r ? dec_csr_wrdata_r[31:0] : mit1_match_ns ? 'b0 : mitcnt1_inc[31:0];

   rvdffe #(24) mitcnt1_ffb      (.*, .clk(free_l2clk), .en(wr_mitcnt1_r | (mitcnt1_inc_ok & mitcnt1_inc_cout) | mit1_match_ns), .din(mitcnt1_ns[31:8]), .dout(mitcnt1[31:8]));
   rvdffe #(8)  mitcnt1_ffa      (.*, .clk(free_l2clk), .en(wr_mitcnt1_r | mitcnt1_inc_ok | mit1_match_ns),                       .din(mitcnt1_ns[7:0]), .dout(mitcnt1[7:0]));


   // ----------------------------------------------------------------------
   // MITB0 (RW)
   // [31:0] : Internal Timer Bound 0

   localparam MITB0         = 12'h7d3;

   assign wr_mitb0_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITB0);

   rvdffe #(32) mitb0_ff      (.*, .en(wr_mitb0_r), .din(~dec_csr_wrdata_r[31:0]), .dout(mitb0_b[31:0]));
   assign mitb0[31:0] = ~mitb0_b[31:0];

   // ----------------------------------------------------------------------
   // MITB1 (RW)
   // [31:0] : Internal Timer Bound 1

   localparam MITB1         = 12'h7d6;

   assign wr_mitb1_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITB1);

   rvdffe #(32) mitb1_ff      (.*, .en(wr_mitb1_r), .din(~dec_csr_wrdata_r[31:0]), .dout(mitb1_b[31:0]));
   assign mitb1[31:0] = ~mitb1_b[31:0];

   // ----------------------------------------------------------------------
   // MITCTL0 (RW) Internal Timer Ctl 0
   // [31:3] : Reserved, reads 0x0
   // [2]    : Enable while PAUSEd
   // [1]    : Enable while HALTed
   // [0]    : Enable (resets to 0x1)

   localparam MITCTL0       = 12'h7d4;

   assign wr_mitctl0_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITCTL0);
   assign mitctl0_ns[2:0] = wr_mitctl0_r ? {dec_csr_wrdata_r[2:0]} : {mitctl0[2:0]};

   assign mitctl0_0_b_ns = ~mitctl0_ns[0];
   rvdffs #(3) mitctl0_ff      (.*, .clk(csr_wr_clk), .en(wr_mitctl0_r), .din({mitctl0_ns[2:1], mitctl0_0_b_ns}), .dout({mitctl0[2:1], mitctl0_0_b}));
   assign mitctl0[0] = ~mitctl0_0_b;

   // ----------------------------------------------------------------------
   // MITCTL1 (RW) Internal Timer Ctl 1
   // [31:4] : Reserved, reads 0x0
   // [3]    : Cascade
   // [2]    : Enable while PAUSEd
   // [1]    : Enable while HALTed
   // [0]    : Enable (resets to 0x1)

   localparam MITCTL1       = 12'h7d7;

   assign wr_mitctl1_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:0] == MITCTL1);
   assign mitctl1_ns[3:0] = wr_mitctl1_r ? {dec_csr_wrdata_r[3:0]} : {mitctl1[3:0]};

   assign mitctl1_0_b_ns = ~mitctl1_ns[0];
   rvdffs #(4) mitctl1_ff      (.*, .clk(csr_wr_clk), .en(wr_mitctl1_r), .din({mitctl1_ns[3:1], mitctl1_0_b_ns}), .dout({mitctl1[3:1], mitctl1_0_b}));
   assign mitctl1[0] = ~mitctl1_0_b;
   assign dec_timer_read_d = csr_mitcnt1 | csr_mitcnt0 | csr_mitb1 | csr_mitb0 | csr_mitctl0 | csr_mitctl1;
   assign dec_timer_rddata_d[31:0] = ( ({32{csr_mitcnt0}}      & mitcnt0[31:0]) |
                                       ({32{csr_mitcnt1}}      & mitcnt1[31:0]) |
                                       ({32{csr_mitb0}}        & mitb0[31:0]) |
                                       ({32{csr_mitb1}}        & mitb1[31:0]) |
                                       ({32{csr_mitctl0}}      & {29'b0, mitctl0[2:0]}) |
                                       ({32{csr_mitctl1}}      & {28'b0, mitctl1[3:0]})
                                       );


endmodule // dec_timer_ctl