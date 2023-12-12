// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

// this sequence wites random random data to random address, then reads it back
class dccm_write_read_sequence extends uvm_sequence #(dccm_transaction_sequence_item);

  `uvm_object_utils(dccm_write_read_sequence)

  function new(string name = "write_read_sequence");
    super.new(name);
  endfunction

  virtual task body();

    // Do randomized write
    req = dccm_transaction_sequence_item::type_id::create("req");
    wait_for_grant();
    req.randomize();
    req.wr_en = 1'b1;
    req.rd_en = 1'b0;
    send_request(req);
    wait_for_item_done();

    // Do read from the same address
    wait_for_grant();
    req.wr_en = 1'b0;
    req.rd_en = 1'b1;
    send_request(req);
    wait_for_item_done();

  endtask
endclass

class dccm_memtest_sequence extends uvm_sequence #(dccm_transaction_sequence_item);

  dccm_write_read_sequence seq;
  int loops;

  `uvm_object_utils(dccm_memtest_sequence)

  function new(string name = "dccm_memtest_sequence");
    super.new(name);
  endfunction

  virtual task body();
    repeat (loops) begin
      `uvm_do(seq)
    end
  endtask
endclass
//=========================================================================
