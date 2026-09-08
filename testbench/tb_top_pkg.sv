// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package tb_top_pkg;

`ifndef VERILATOR
  class bitflip_mask_generator #(
      int DATA_AND_ECC_W = 39
  );

    rand logic [DATA_AND_ECC_W-1:0] rand_sram_bitflip_mask;
    logic do_double_bitflip;
    constraint bitflip_c {
      if (do_double_bitflip) {
        $countones(rand_sram_bitflip_mask) == 2;
      } else {
        $countones(rand_sram_bitflip_mask) == 1;
      }
    }

    function new;
      this.rand_sram_bitflip_mask = '0;
      this.do_double_bitflip = 1'b0;
    endfunction

    function logic [DATA_AND_ECC_W-1:0] get_mask(bit do_double_bit = 1'b0);
      this.do_double_bitflip = do_double_bit;
      this.randomize();
      return this.rand_sram_bitflip_mask;
    endfunction

  endclass
`endif

  function static logic [39:0] get_bitflip_mask(bit do_double_bit = 1'b0);
    return 2 << ($urandom % (37)) | 39'(do_double_bit);
  endfunction

  function static logic [38:0] sanitize_x(input logic [38:0] val);
    for (int b = 0; b < 39; b++) begin
      sanitize_x[b] = (val[b] === 1'b1) ? 1'b1 : 1'b0;
    end
  endfunction

  typedef struct packed {
    //  [9] - DCCM Read Enable Fault Injection
    //  [8] - DCCM Write Enable Fault Injection
    //  [7] - DCCM Address Fault Injection
    //  [6] - ICCM Read Enable Fault Injection
    //  [5] - ICCM Write Enable Fault Injection
    //  [4] - ICCM Address Fault Injection
    //  [3] - Double bit, DCCM Error Injection
    //  [2] - Single bit, DCCM Error Injection
    //  [1] - Double bit, ICCM Error Injection
    //  [0] - Single bit, ICCM Error Injection
    logic dccm_rden_fault;
    logic dccm_wren_fault;
    logic dccm_addr_fault;
    logic iccm_rden_fault;
    logic iccm_wren_fault;
    logic iccm_addr_fault;
    logic dccm_double_bit_error;
    logic dccm_single_bit_error;
    logic iccm_double_bit_error;
    logic iccm_single_bit_error;
  } veer_sram_error_injection_mode_t;

endpackage
