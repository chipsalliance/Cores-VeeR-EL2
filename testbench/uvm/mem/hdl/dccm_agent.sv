// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

`include "dccm_transaction_sequence_item.sv"
`include "dccm_sequencer.sv"
`include "dccm_sequence.sv"
`include "dccm_driver.sv"
`include "dccm_monitor.sv"

class dccm_agent extends uvm_agent;

  dccm_driver driver;
  dccm_sequencer sequencer;
  dccm_monitor monitor;

  `uvm_component_utils(dccm_agent)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    monitor = dccm_monitor::type_id::create("monitor", this);

    if (get_is_active() == UVM_ACTIVE) begin
      driver    = dccm_driver::type_id::create("driver", this);
      sequencer = dccm_sequencer::type_id::create("sequencer", this);
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect_phase

endclass : dccm_agent
