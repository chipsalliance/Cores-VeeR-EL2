// Top module instantiating
// RVECC Encoder
// RVECC Decoder
// Channel model


module top #(
            parameter DATA_WIDTH = 64,
            localparam ECC_WIDTH = (DATA_WIDTH == 32) ? ($clog2(DATA_WIDTH) + 2) : ($clog2(DATA_WIDTH) + 1),
            localparam CHANNEL_WIDTH = DATA_WIDTH + ECC_WIDTH
            )(
            input logic [DATA_WIDTH-1:0] din_encoder,
            input logic [$clog2(CHANNEL_WIDTH)-1:0] error_pos1, error_pos2,
            input logic decoder_en, sed_ded, single_error_inject, double_error_inject,
            output logic [CHANNEL_WIDTH-1:0] encoded_data, received_data,
            output logic double_ecc_error);

  logic [DATA_WIDTH-1:0] din_decoder, dout_decoder;
  logic [ECC_WIDTH-1:0] ecc_out_encoder, ecc_in_decoder, ecc_out_decoder;

  assign encoded_data = {ecc_out_encoder, din_encoder};
  assign din_decoder = received_data[DATA_WIDTH-1:0];
  assign ecc_in_decoder = received_data[CHANNEL_WIDTH-1:DATA_WIDTH];

  rvecc_encode_64 encoder(.din(din_encoder), .ecc_out(ecc_out_encoder));
  rvecc_decode_64 decoder(.en(decoder_en), .din(din_decoder), .ecc_in(ecc_in_decoder), .ecc_error(double_ecc_error));
  channel_model #(CHANNEL_WIDTH) channel(.din(encoded_data), .single_error_inject(single_error_inject), .double_error_inject(double_error_inject),
                                         .error_pos1(error_pos1), .error_pos2(error_pos2),  .dout(received_data));

endmodule
