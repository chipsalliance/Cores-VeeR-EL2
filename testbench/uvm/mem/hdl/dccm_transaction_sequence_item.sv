class dccm_transaction_sequence_item extends uvm_sequence_item;

  `include "el2_param.vh"
  ;

  rand bit [       pt.DCCM_BITS-1:0] addr;
  rand bit [pt.DCCM_FDATA_WIDTH-1:0] wdata;
  bit      [pt.DCCM_FDATA_WIDTH-1:0] rdata;
  // we want to manually control wr_en anf rd_en in the test
  bit                                wr_en;
  bit                                rd_en;

  `uvm_object_utils_begin(dccm_transaction_sequence_item)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(wr_en, UVM_ALL_ON)
    `uvm_field_int(rd_en, UVM_ALL_ON)
    `uvm_field_int(wdata, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "dccm_transation_sequence_item");
    super.new(name);
  endfunction

endclass
