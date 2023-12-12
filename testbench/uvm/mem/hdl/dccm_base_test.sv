// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

`include "dccm_agent.sv"
`include "dccm_scoreboard.sv"
class mem_model_base_test extends uvm_test;

  `uvm_component_utils(mem_model_base_test)

  dccm_agent agent;
  dccm_scoreboard scoreboard;

  function new(string name = "mem_model_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    agent = dccm_agent::type_id::create("agent", this);
    scoreboard = dccm_scoreboard::type_id::create("scoreboard", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    agent.monitor.transaction_analisys_port.connect(scoreboard.item_collected_export);
  endfunction : connect_phase

  function void report_phase(uvm_phase phase);
    uvm_report_server svr;
    int errors;
    super.report_phase(phase);

    svr = uvm_report_server::get_server();
    errors = svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR);
    if (errors > 0) begin
      `uvm_info(get_type_name(), "DCCM TEST FAILED!!", UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Found %d errors", errors), UVM_NONE)
    end else begin
      `uvm_info(get_type_name(), "DCCM TEST PASSED!!", UVM_NONE)
    end
  endfunction

endclass : mem_model_base_test
