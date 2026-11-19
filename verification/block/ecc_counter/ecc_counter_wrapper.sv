module ecc_counter_wrapper(
  input  logic       clk_i,      // Clock
  input  logic       rst_ni,     // Async. reset

  input  logic       inc_i,      // Increment
  input  logic       dec_i,      // Decrement
  input  logic       clr_i,      // Clear

  output logic [7:0] cnt_o,      // Count value

  output logic       ecc_error_o,  // ECC correctable error occurred
  output logic       ecc_fatal_o   // ECC uncorrectable error occurred
);
  el2_ecc_counter_8 el2_ecc_counter_8_u(.*);

  logic value;
  logic [3:0] storage;
  always @* begin
    case(storage)
      4'd0: force el2_ecc_counter_8_u.storage[0] = value;
      4'd1: force el2_ecc_counter_8_u.storage[1] = value;
      4'd2: force el2_ecc_counter_8_u.storage[2] = value;
      4'd3: force el2_ecc_counter_8_u.storage[3] = value;
      4'd4: force el2_ecc_counter_8_u.storage[4] = value;
      4'd5: force el2_ecc_counter_8_u.storage[5] = value;
      4'd6: force el2_ecc_counter_8_u.storage[6] = value;
      4'd7: force el2_ecc_counter_8_u.storage[7] = value;
      4'd8: force el2_ecc_counter_8_u.storage[8] = value;
      4'd9: force el2_ecc_counter_8_u.storage[9] = value;
      4'd10: force el2_ecc_counter_8_u.storage[10] = value;
      4'd11: force el2_ecc_counter_8_u.storage[11] = value;
      4'd12: force el2_ecc_counter_8_u.storage[12] = value;
      default: release el2_ecc_counter_8_u.storage;
    endcase
  end
endmodule
