`include "uvm_pkg.sv"

import uvm_pkg::*;

`include "dccm_interface.sv"
`include "dccm_base_test.sv"
`include "dccm_memtest.sv"

module tbench_top;

  bit clk;
  bit reset;

  always #5 clk = ~clk;

  initial begin
    reset = 1;
    #5 reset = 0;
  end

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, tbench_top);
  end

  dccm_interface intf (
      clk,
      reset
  );

  el2_lsu_dccm_mem DUT (
      .clk         (intf.clk),
      .active_clk  (intf.clk),
      .rst_l       (~intf.reset),
      .clk_override(1'b0),
      .scan_mode   (1'b0),

      .dccm_wren      (intf.wr_en),
      .dccm_rden      (intf.rd_en),
      .dccm_wr_addr_hi(intf.addr),
      .dccm_wr_addr_lo(intf.addr),
      .dccm_rd_addr_hi(intf.addr),
      .dccm_rd_addr_lo(intf.addr),
      .dccm_wr_data_hi(intf.wdata),
      .dccm_wr_data_lo(intf.wdata),
      .dccm_rd_data_hi(),            // For aligned read/write this should match the lo part
      .dccm_rd_data_lo(intf.rdata)
  );

  // Debug, dump memory signals on each clock cycle
  always @(posedge intf.clk)
    $display(
        "a:%08X w:%d wd:%08X r:%d rd:%08X",
        intf.addr,
        intf.wr_en,
        intf.wdata,
        intf.rd_en,
        intf.rdata
    );

  initial begin
    uvm_config_db#(virtual dccm_interface)::set(uvm_root::get(), "*", "memory_vif", intf);
  end

  initial begin
    run_test();
  end

endmodule
