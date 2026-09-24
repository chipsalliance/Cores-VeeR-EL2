// SPDX-License-Identifier: Apache-2.0
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
//

`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
`define TMR_RECOVERY_FSM tb_top.rvtop_wrapper.rvtop.tmr_complex.el2_tmr_recovery_fsm_u
`endif

package tb_top_pkg;

`ifndef VERILATOR
  class bitflip_mask_generator #(
      int DATA_AND_ECC_W = 39
  );

    rand logic [DATA_AND_ECC_W-1:0] rand_sram_bitflip_mask;
    logic do_double_bitflip;
    constraint bitflip_c {
      if (do_double_bitflip) {
        $countones(rand_sram_bitflip_mask) == 2;
      } else {
        $countones(rand_sram_bitflip_mask) == 1;
      }
    }

    function new;
      this.rand_sram_bitflip_mask = '0;
      this.do_double_bitflip = 1'b0;
    endfunction

    function logic [DATA_AND_ECC_W-1:0] get_mask(bit do_double_bit = 1'b0);
      this.do_double_bitflip = do_double_bit;
      this.randomize();
      return this.rand_sram_bitflip_mask;
    endfunction

  endclass
`endif

  function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
    return 2 << ($urandom % (37)) | 39'(do_double_bit);
  endfunction

  // sanitize_x: Translates 4-state 'X'/'Z' uninitialized SRAM bits into deterministic '0'
  // (modeling physical bus pull-down behavior).
  // The 39-bit width [38:0] matches the widest internal memory data path across both ICCM
  // and DCCM: pt.ICCM_FDATA_WIDTH = pt.DCCM_FDATA_WIDTH = 39 (32-bit data + 7-bit ECC,
  // matching the ram_*x39 macro data port widths).
  function static logic [38:0] sanitize_x(input logic [38:0] val);
    for (int b = 0; b < 39; b++) begin
      sanitize_x[b] = (val[b] === 1'b1) ? 1'b1 : 1'b0;
    end
  endfunction

  typedef struct packed {
    //  [9] - DCCM Access (ME/clken) Fault Injection (disables both reads and writes)
    //  [8] - DCCM Write Enable Fault Injection
    //  [7] - DCCM Address Fault Injection
    //  [6] - ICCM Access (ME/clken) Fault Injection (disables both reads and writes)
    //  [5] - ICCM Write Enable Fault Injection
    //  [4] - ICCM Address Fault Injection
    //  [3] - Double bit, DCCM Error Injection
    //  [2] - Single bit, DCCM Error Injection
    //  [1] - Double bit, ICCM Error Injection
    //  [0] - Single bit, ICCM Error Injection
    logic dccm_access_fault;
    logic dccm_wren_fault;
    logic dccm_addr_fault;
    logic iccm_access_fault;
    logic iccm_wren_fault;
    logic iccm_addr_fault;
    logic dccm_double_bit_error;
    logic dccm_single_bit_error;
    logic iccm_double_bit_error;
    logic iccm_single_bit_error;
  } veer_sram_error_injection_mode_t;

  /* verilator lint_off CASEINCOMPLETE */
  `include "dasm.svi"
  /* verilator lint_on CASEINCOMPLETE */

  /*
    This class is responsible for monitoring the trace port as well as VeeR
    internals to provide execution trace dump. The trace is simultaneously
    written in CSV and text format.
  */
  class TraceMonitor;

      local virtual trace_monitor_if trace;
      local gpr_t   gpr;
      local integer tp = 0;
      local integer el = 0;

      function new (virtual trace_monitor_if vif, string exec_log, input string trace_csv);
          this.trace = vif;

          if (exec_log != "") begin
              el = $fopen(exec_log, "w");
              $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value    csr=value     ; mnemonic\n");
          end
          if (trace_csv != "") begin
              tp = $fopen(trace_csv, "w");
          end

          fork
              run();
          join_none
      endfunction

      // Trace monitoring task
      local task automatic run();
          integer commit_count = 0;
          integer cycle_count  = 0;

          logic        wb_valid;
          logic [ 4:0] wb_dest;
          logic [31:0] wb_data;

          logic        wb_csr_valid;
          logic [11:0] wb_csr_dest;
          logic [31:0] wb_csr_data;

          forever begin
              @(posedge trace.clk);
              cycle_count++;

              if (!trace.rst_n) continue;

              if (trace.trace_valid) begin

                  // Trace CSV
                  if (tp) begin
                      $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", trace.trace_valid, 0, trace.trace_address,
                             0, trace.trace_insn, trace.trace_exception, trace.trace_ecause,
                             trace.trace_tval, trace.trace_interrupt);
                  end

                  // Basic trace - no exception register updates
                  // #1 0 ee000000 b0201073 c 0b02       00000000
                  commit_count++;
                  $fwrite(el, "%10d : %8s 0 %h %h%13s %14s ; %s\n", cycle_count, $sformatf("#%0d", commit_count),
                              trace.trace_address, trace.trace_insn,
                              (wb_dest !=0 && wb_valid) ? $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "            ",
                              (wb_csr_valid)? $sformatf("c%h=%h", wb_csr_dest, wb_csr_data) : "             ",
                              dasm(trace.trace_insn, trace.trace_address, wb_dest & {5{wb_valid}}, wb_data, gpr)
                          );
              end
              if(trace.nonblock_load_wvalid) begin
                  $fwrite(el, "%10d : %32s=%h                ; nbL\n", cycle_count, abi_reg[trace.nonblock_load_waddr], trace.nonblock_load_wdata);
                  gpr[trace.nonblock_load_waddr] = trace.nonblock_load_wdata;
              end
              if(trace.div_wvalid) begin
                  $fwrite(el, "%10d : %32s=%h                ; nbD\n", cycle_count, abi_reg[trace.div_waddr], trace.div_wdata);
                  gpr[trace.div_waddr] = trace.div_wdata;
              end
  `ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
              if (`TMR_RECOVERY_FSM.recovery_state_en && `TMR_RECOVERY_FSM.recovery_state != '0) begin
                  if (`TMR_RECOVERY_FSM.recovery_nxstate == HALT_CORES) begin
                      $fwrite(el, "%10d : TMR recovery procedure began\n", cycle_count);
                  end
                  if (`TMR_RECOVERY_FSM.recovery_nxstate == IDLE) begin
                      $fwrite(el, "%10d : TMR recovery procedure finished\n", cycle_count);
                  end
              end
  `endif
              // Delay DEC internals by 1 cycle
              wb_valid      = trace.gpr_wvalid;
              wb_dest       = trace.gpr_waddr;
              wb_data       = trace.gpr_wdata;
              wb_csr_valid  = trace.csr_wvalid;
              wb_csr_dest   = trace.csr_waddr;
              wb_csr_data   = trace.csr_wdata;
          end
      endtask
  endclass : TraceMonitor

endpackage
