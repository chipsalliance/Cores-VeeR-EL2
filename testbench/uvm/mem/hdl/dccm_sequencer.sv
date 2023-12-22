// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

// FIXME:
// In Verilator, user should always use:
//     uvm_sequencer#(item, item);
// instead standard (other simulators):
//     uvm_sequencer#(item);

`ifdef VERILATOR
class dccm_sequencer extends uvm_sequencer #(dccm_transaction_sequence_item, dccm_transaction_sequence_item);
`else
class dccm_sequencer extends uvm_sequencer #(dccm_transaction_sequence_item);
`endif

  `uvm_component_utils(dccm_sequencer)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

endclass
