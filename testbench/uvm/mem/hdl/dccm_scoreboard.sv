// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

class dccm_scoreboard extends uvm_scoreboard;

  `include "el2_param.vh"
  ;

  dccm_transaction_sequence_item data_queue[$];
  bit [pt.DCCM_FDATA_WIDTH-1:0] sc_mem;

  uvm_analysis_imp #(dccm_transaction_sequence_item, dccm_scoreboard) item_collected_export;
  `uvm_component_utils(dccm_scoreboard)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    item_collected_export = new("item_collected_export", this);
    sc_mem = {(pt.DCCM_FDATA_WIDTH) {1'b1}};
  endfunction : build_phase

  virtual function void write(dccm_transaction_sequence_item pkt);
    pkt.print();
    data_queue.push_back(pkt);
  endfunction : write

  virtual task run_phase(uvm_phase phase);
    dccm_transaction_sequence_item mem_pkt;

    forever begin
      wait (data_queue.size() > 0);
      mem_pkt = data_queue.pop_front();

      if (mem_pkt.wr_en) begin
        sc_mem = mem_pkt.wdata;
        `uvm_info(get_type_name(), $sformatf("------ :: WRITE DATA       :: ------"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Addr: %0h", mem_pkt.addr), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Data: %0h", mem_pkt.wdata), UVM_LOW)
        `uvm_info(get_type_name(), "------------------------------------", UVM_LOW)
      end else if (mem_pkt.rd_en) begin
        if (sc_mem == mem_pkt.rdata) begin
          `uvm_info(get_type_name(), $sformatf("------ :: READ DATA Match :: ------"), UVM_LOW)
          `uvm_info(get_type_name(), $sformatf("Addr: %0h", mem_pkt.addr), UVM_LOW)
          `uvm_info(get_type_name(), $sformatf("Expected Data: %0h Actual Data: %0h", sc_mem,
                                               mem_pkt.rdata), UVM_LOW)
          `uvm_info(get_type_name(), "------------------------------------", UVM_LOW)
        end else begin
          `uvm_error(get_type_name(), "------ :: READ DATA Mismatch :: ------")
          `uvm_error(get_type_name(), $sformatf("Addr: %0h", mem_pkt.addr))
          `uvm_error(get_type_name(), $sformatf(
                     "Expected Data: %0h Actual Data: %0h", sc_mem, mem_pkt.rdata))
          `uvm_error(get_type_name(), "------------------------------------")
        end
      end
    end
  endtask : run_phase
endclass : dccm_scoreboard
