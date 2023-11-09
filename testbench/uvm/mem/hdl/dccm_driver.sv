class dccm_driver extends uvm_driver #(dccm_transaction_sequence_item);

  virtual dccm_interface memory_vif;
  `uvm_component_utils(dccm_driver)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual dccm_interface)::get(this, "", "memory_vif", memory_vif))
      `uvm_fatal("NO_VIF", {"virtual interface must be set for: ", get_full_name(), ".memory_vif"});
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive();
      seq_item_port.item_done();
    end
  endtask : run_phase

  virtual task drive();
    memory_vif.wr_en <= 0;
    memory_vif.rd_en <= 0;
    @(posedge memory_vif.clk);

    memory_vif.addr <= req.addr;

    if (req.wr_en) begin  // write operation
      `uvm_info(get_type_name(), $sformatf("WR: 0x%08X <= 0x%08X", req.addr, req.wdata), UVM_LOW)
      memory_vif.wr_en <= 1'b1;  //req.wr_en;
      memory_vif.wdata <= req.wdata;
      @(posedge memory_vif.clk);
    end else if (req.rd_en) begin  //read operation
      memory_vif.rd_en <= 1'b1;  //req.rd_en;
      @(posedge memory_vif.clk);
      memory_vif.rd_en <= 0;
      @(posedge memory_vif.clk);
      req.rdata = memory_vif.rdata;
      `uvm_info(get_type_name(), $sformatf("RD: 0x%08X => 0x%08X", req.addr, req.rdata), UVM_LOW)
    end

  endtask : drive
endclass : dccm_driver
