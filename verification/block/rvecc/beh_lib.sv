module rvecc_encode  (
                      input [31:0] din,
                      output [6:0] ecc_out
                      );
logic [5:0] ecc_out_temp;

   assign ecc_out_temp[0] = din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
   assign ecc_out_temp[1] = din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
   assign ecc_out_temp[2] = din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
   assign ecc_out_temp[3] = din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_out_temp[4] = din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_out_temp[5] = din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

   assign ecc_out[6:0] = {(^din[31:0])^(^ecc_out_temp[5:0]),ecc_out_temp[5:0]};

endmodule // rvecc_encode

module rvecc_decode  (
                      input         en,
                      input [31:0]  din,
                      input [6:0]   ecc_in,
                      input         sed_ded,    // only do detection and no correction. Used for the I$
                      output [31:0] dout,
                      output [6:0]  ecc_out,
                      output        single_ecc_error,
                      output        double_ecc_error

                      );

   logic [6:0]                      ecc_check;
   logic [38:0]                     error_mask;
   logic [38:0]                     din_plus_parity, dout_plus_parity;

   // Generate the ecc bits
   assign ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
   assign ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
   assign ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
   assign ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

   // This is the parity bit
   assign ecc_check[6] = ((^din[31:0])^(^ecc_in[6:0]));

   assign single_ecc_error = en & (ecc_check[6:0] != 0) & ~sed_ded;   // this will never be on for sed_ded
   assign double_ecc_error = en & (ecc_check[6:0] != 0);  // all errors in the sed_ded case will be recorded as DE

   // Generate the mask for error correctiong
   for (genvar i=1; i<40; i++) begin
      assign error_mask[i-1] = (ecc_check[5:0] == i);
   end

   // Generate the corrected data
   assign din_plus_parity[38:0] = {ecc_in[6], din[31:26], ecc_in[5], din[25:11], ecc_in[4], din[10:4], ecc_in[3], din[3:1], ecc_in[2], din[0], ecc_in[1:0]};

   assign dout_plus_parity[38:0] = single_ecc_error ? (error_mask[38:0] ^ din_plus_parity[38:0]) : din_plus_parity[38:0];
   assign dout[31:0]             = {dout_plus_parity[37:32], dout_plus_parity[30:16], dout_plus_parity[14:8], dout_plus_parity[6:4], dout_plus_parity[2]};
   assign ecc_out[6:0]           = {(dout_plus_parity[38] ^ (ecc_check[6:0] == 7'b1000000)), dout_plus_parity[31], dout_plus_parity[15], dout_plus_parity[7], dout_plus_parity[3], dout_plus_parity[1:0]};

endmodule // rvecc_decode

module rvecc_encode_64  (
                      input [63:0] din,
                      output [6:0] ecc_out
                      );
  assign ecc_out[0] = din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30]^din[32]^din[34]^din[36]^din[38]^din[40]^din[42]^din[44]^din[46]^din[48]^din[50]^din[52]^din[54]^din[56]^din[57]^din[59]^din[61]^din[63];

   assign ecc_out[1] = din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31]^din[32]^din[35]^din[36]^din[39]^din[40]^din[43]^din[44]^din[47]^din[48]^din[51]^din[52]^din[55]^din[56]^din[58]^din[59]^din[62]^din[63];

   assign ecc_out[2] = din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31]^din[32]^din[37]^din[38]^din[39]^din[40]^din[45]^din[46]^din[47]^din[48]^din[53]^din[54]^din[55]^din[56]^din[60]^din[61]^din[62]^din[63];

   assign ecc_out[3] = din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[4] = din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[5] = din[26]^din[27]^din[28]^din[29]^din[30]^din[31]^din[32]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[6] = din[57]^din[58]^din[59]^din[60]^din[61]^din[62]^din[63];

endmodule // rvecc_encode_64


module rvecc_decode_64  (
                      input         en,
                      input [63:0]  din,
                      input [6:0]   ecc_in,
                      output        ecc_error
                      );

   logic [6:0]                      ecc_check;

   // Generate the ecc bits
   assign ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30]^din[32]^din[34]^din[36]^din[38]^din[40]^din[42]^din[44]^din[46]^din[48]^din[50]^din[52]^din[54]^din[56]^din[57]^din[59]^din[61]^din[63];

   assign ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31]^din[32]^din[35]^din[36]^din[39]^din[40]^din[43]^din[44]^din[47]^din[48]^din[51]^din[52]^din[55]^din[56]^din[58]^din[59]^din[62]^din[63];

   assign ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31]^din[32]^din[37]^din[38]^din[39]^din[40]^din[45]^din[46]^din[47]^din[48]^din[53]^din[54]^din[55]^din[56]^din[60]^din[61]^din[62]^din[63];

   assign ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31]^din[32]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[6] = ecc_in[6]^din[57]^din[58]^din[59]^din[60]^din[61]^din[62]^din[63];

   assign ecc_error = en & (ecc_check[6:0] != 0);  // all errors in the sed_ded case will be recorded as DE

 endmodule // rvecc_decode_64


