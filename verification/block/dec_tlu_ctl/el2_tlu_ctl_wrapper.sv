module el2_dec_tlu_ctl_wrapper
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


   el2_lsu_error_pkt_t lsu_error_pkt_r;
   el2_trap_pkt_t dec_tlu_packet_r;

   assign lsu_error_pkt_r = '0;
   assign dec_tlu_packet_r = '0;

el2_dec_tlu_ctl dut (
  .lsu_error_pkt_r(lsu_error_pkt_r),
  .dec_tlu_packet_r(dec_tlu_packet_r),
  .*
);
endmodule
