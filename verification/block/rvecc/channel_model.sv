module channel_model #(CHANNEL_WIDTH=39) (
 input [CHANNEL_WIDTH-1:0] din,
 input single_error_inject,
 input double_error_inject,
 input [$clog2(CHANNEL_WIDTH)-1:0] error_pos1, error_pos2,
 output logic [CHANNEL_WIDTH-1:0] dout
 );

 always_comb begin
   dout             = din;
   if (single_error_inject)
     dout[error_pos1] = !din[error_pos1];
   else if (double_error_inject) begin
     dout[error_pos1] = !din[error_pos1];
     dout[error_pos2] = !din[error_pos2];
   end
 end

endmodule
