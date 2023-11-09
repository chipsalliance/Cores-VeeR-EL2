class dccm_monitor extends uvm_monitor;

  virtual dccm_interface memory_vif;
  uvm_analysis_port #(dccm_transaction_sequence_item) transaction_analisys_port;
  dccm_transaction_sequence_item transaction;

  `uvm_component_utils(dccm_monitor)

  function new(string name, uvm_component parent);
    super.new(name, parent);
    transaction = new();
    transaction_analisys_port = new("trensaction_analisys_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual dccm_interface)::get(this, "", "memory_vif", memory_vif))
      `uvm_fatal("NOVIF", {"virtual interface must be set for: ", get_full_name(), ".memory_vif"});
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge memory_vif.clk);
      wait (memory_vif.wr_en || memory_vif.rd_en);
      // store control signals and address
      transaction.addr  = memory_vif.addr;
      transaction.wdata = memory_vif.wdata;
      transaction.rd_en = memory_vif.rd_en;
      if (memory_vif.wr_en) begin
        // store write data
        transaction.wr_en = memory_vif.wr_en;
        @(posedge memory_vif.clk);
      end
      if (memory_vif.rd_en) begin
        // it takes 2 clocks to get the data on the output port
        @(posedge memory_vif.clk);
        @(posedge memory_vif.clk);
        // store read data
        transaction.rdata = memory_vif.rdata;
      end
      transaction_analisys_port.write(transaction);
    end
  endtask : run_phase

endclass : dccm_monitor
