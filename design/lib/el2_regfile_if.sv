//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Antmicro <www.antmicro.com>
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


interface el2_regfile_if
import el2_pkg::*;
();
  typedef struct packed {
    // General Purpose Registers
    logic [31:0] ra; // Return address
    logic [31:0] sp; // Stack pointer
    logic [31:0] fp; // Frame pointer
    logic [31:0] a0, a1; // Function arguments 0-1 / Return values 0-1
    logic [31:0] a2, a3, a4, a5, a6, a7; // Function arguments 2-7
  } el2_regfile_gpr_pkt_t;

  typedef struct packed {
    // Important registers chosen for exposure
    logic [31:0] pc, npc; // (Next) Program Counter
    logic [31:0] mstatus; // Machine status
    logic [31:0] mie; // Machine interrupt enable
    logic [31:0] mtvec; // Machine trap-handler base address
    logic [31:0] mscratch; // Scratch register for machine trap handlers
    logic [31:0] mepc; // Machine exception program counter
    logic [31:0] mcause; // Machine trap cause
    logic [31:0] mtval; // Machine bad address or instruction
    logic [31:0] mip; // Machine interrupt pending
    logic [31:0] mcyclel; // Machine cycle counter
    logic [31:0] mcycleh; // Machine cycle counter
    logic [31:0] minstretl; // Machine instructions-retired counter
    logic [31:0] minstreth; // Machine instructions-retired counter
    logic [31:0] mrac; // Region access control
  } el2_regfile_tlu_pkt_t;

  el2_regfile_gpr_pkt_t gpr;
  el2_regfile_tlu_pkt_t tlu;

  modport veer_gpr_rf(output gpr);

  modport veer_tlu_rf(output tlu);

  modport veer_rf_src(output gpr, output tlu);

  modport veer_rf_sink(input gpr, input tlu);

endinterface
