// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

class mem_wr_rd_test extends mem_model_base_test;

  `uvm_component_utils(mem_wr_rd_test)

  dccm_memtest_sequence memtest;

  function new(string name = "mem_wr_rd_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    memtest = dccm_memtest_sequence::type_id::create();
    // Run the memtest 10 times
    memtest.loops = 10;
  endfunction : build_phase

  task run_phase(uvm_phase phase);

    phase.raise_objection(this);
    memtest.start(agent.sequencer);
    phase.drop_objection(this);

  endtask : run_phase

endclass : mem_wr_rd_test
