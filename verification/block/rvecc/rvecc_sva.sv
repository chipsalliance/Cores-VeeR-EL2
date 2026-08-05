module rvecc_sva  #(
                    parameter DATA_WIDTH = 32,
                    localparam ECC_WIDTH = (DATA_WIDTH == 32) ? ($clog2(DATA_WIDTH) + 2) : ($clog2(DATA_WIDTH) + 1),
                    localparam CHANNEL_WIDTH = DATA_WIDTH + ECC_WIDTH
                    )(
                      input logic [DATA_WIDTH-1:0] din_encoder,
                      input logic [$clog2(CHANNEL_WIDTH)-1:0] error_pos1, error_pos2,
                      input logic decoder_en, sed_ded, single_error_inject, double_error_inject);

    logic [CHANNEL_WIDTH-1:0] encoded_data, received_data, corrected_data;
    logic single_ecc_error, double_ecc_error;

    logic clk;

    default clocking default_clk @(posedge clk);
    endclocking

    top #(DATA_WIDTH) uut(
                                                    .din_encoder(din_encoder),
                                                    .error_pos1(error_pos1), 
                                                    .error_pos2(error_pos2), 
                                                    .decoder_en(decoder_en),
                                                    .sed_ded(sed_ded),
                                                    .single_error_inject(single_error_inject),
                                                    .double_error_inject(double_error_inject),
                                                    .encoded_data(encoded_data), 
                                                    .received_data(received_data), 
                                                    .corrected_data(corrected_data), 
                                                    .single_ecc_error(single_ecc_error), 
                                                    .double_ecc_error(double_ecc_error));    

    property valid_error_pos(error_pos);
      ((error_pos >= 0) && (error_pos <= (CHANNEL_WIDTH-1)));
    endproperty

    // constrain the valid error positions
    ASSUME_VALID_ERROR_POSITION1:        assume property (valid_error_pos(error_pos1));
    ASSUME_VALID_ERROR_POSITION2:        assume property (valid_error_pos(error_pos2));

    // different error positions for double errors 
    ASSUME_UNIQUE_DOUBLE_ERROR_POSITION: assume property (double_error_inject |-> (error_pos1 != error_pos2));

    // if a single error is injected, don't inject double error at the same time
    ASSUME_SINGLE_OR_DOUBLE_ERROR:       assume property (single_error_inject |-> !double_error_inject);

    // prove that a single injected error causes encoded data to be not equal to received data
    ASSERT_SINGLE_ERROR_PRESENT:    assert property (single_error_inject |-> (encoded_data != received_data));

    // prove that a double injected error causes encoded data to be not equal to received data
    ASSERT_DOUBLE_ERROR_PRESENT:    assert property (double_error_inject |-> (encoded_data != received_data));

    // prove that if no error injected then encoded data matches the received data
    ASSERT_NO_ERROR_PRESENT:        assert property ((!single_error_inject && !double_error_inject) |-> (encoded_data == received_data));

    // prove that no errors detected or corrected when decoder is disabled
    ASSERT_DECODER_ENABLE_FALSE:    assert property (!decoder_en |-> !single_ecc_error && !double_ecc_error);

    // prove that if no errors injected, then no errors are detected when decoder is enabled
    ASSERT_NO_FALSE_DOUBLE_ERROR_DETECTION:              assert property (!single_error_inject && !double_error_inject && decoder_en |-> !double_ecc_error);
    ASSERT_NO_FALSE_SINGLE_ERROR_DETECTION:              assert property (!single_error_inject && !double_error_inject && decoder_en |-> !single_ecc_error);
    
    // prove that all double-errors injected are detected when decoder is enabled
    ASSERT_DOUBLE_ERROR_DETECTION:   assert property (double_error_inject && decoder_en |-> double_ecc_error);
    
    // in single-error and double-error detection mode when decoder is enabled, single_ecc_error should be low
    ASSERT_NO_SINGLE_ERROR_CORRECTION_IN_SED_DED:   assert property (sed_ded && decoder_en |-> !single_ecc_error);

    // in single-error and double-error detection mode when decoder is enabled, all single errors injected should cause double_ecc_error to go to 1 since single_ecc_error will be low
    ASSERT_SINGLE_ERROR_CORRECTION_IN_SED_DED_DOUBLE_ECC_ERROR:   assert property (sed_ded && single_error_inject && decoder_en |-> double_ecc_error);

    // in single-error correction mode when decoder is enabled, all single errors injected should cause single_ecc_error to go to 1
    ASSERT_SINGLE_ERROR_CORRECTION_IN_NO_SED_DED:   assert property (!sed_ded && single_error_inject && decoder_en |-> single_ecc_error);
        
    // use a case splitting optimization to quickly prove that all possible error positions are corrected. A speedup of 2.5x compared to without case splitting.    
    genvar i;
    generate
      for (i = 0; i <= CHANNEL_WIDTH-1; i++) begin : loop_error_pos
        ASSERT_DATA_CORRECTION: assert property ((error_pos1 == i) && !sed_ded && decoder_en && single_error_inject |-> (encoded_data == corrected_data));
      end
    endgenerate  
    
    // cover data is zero
    COVER_ALL_0: cover property (encoded_data == 0);

    // cover data is non-zero
    COVER_NON_0: cover property (encoded_data != 0);

    // cover a few error position combinations
    COVER_ERROR_0_POS: cover property (error_pos1 ==  0);
    COVER_ERROR_CHANNEL_WIDTH_POS: cover property (error_pos1 == (CHANNEL_WIDTH-1));

    // cover single error detection and correction
    COVER_SED_DED_ZERO: cover property (sed_ded == 1'b0);

    // cover single and double error detection
    COVER_SED_DED_ONE: cover property (sed_ded == 1'b1);
    
  endmodule
