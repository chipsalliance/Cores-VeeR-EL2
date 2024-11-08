`define EL2_IC_TAG_PACKED_SRAM_LOGIC(depth,width)                                                                             \
    if (pt.ICACHE_TAG_BYPASS_ENABLE == 1) begin                                                                               \
                                                                                                                              \
       assign wrptr_in = (wrptr == (pt.ICACHE_TAG_NUM_BYPASS-1)) ? '0 : (wrptr + 1'd1);                                       \
                                                                                                                              \
       rvdffs  #(pt.ICACHE_TAG_NUM_BYPASS_WIDTH)  wrptr_ff(                                                                   \
            .*, .clk(active_clk), .en(|write_bypass_en), .din (wrptr_in), .dout(wrptr)                                        \
       );                                                                                                                     \
                                                                                                                              \
       assign ic_b_sram_en              = |ic_tag_clken;                                                                      \
                                                                                                                              \
       assign ic_b_read_en              =  ic_b_sram_en &   (|ic_tag_rden_q);                                                 \
       assign ic_b_write_en             =  ic_b_sram_en &   (|ic_tag_wren_q);                                                 \
       assign ic_tag_clken_final        =  ic_b_sram_en &    ~(|sel_bypass);                                                  \
                                                                                                                              \
       // LSB is pt.ICACHE_TAG_INDEX_LO]                                                                                      \
       assign ic_b_rw_addr = {ic_rw_addr_q};                                                                                  \
                                                                                                                              \
       always_comb begin                                                                                                      \
          any_addr_match = '0;                                                                                                \
                                                                                                                              \
          for (int l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin                                                                \
             any_addr_match |= ic_b_addr_match[l];                                                                            \
          end                                                                                                                 \
       end                                                                                                                    \
                                                                                                                              \
      // it is an error to ever have 2 entries with the same index and both valid                                             \
      for (genvar l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin: BYPASS                                                         \
                                                                                                                              \
         assign ic_b_addr_match[l] = (wb_index_hold[l] ==  ic_b_rw_addr) & index_valid[l];                                    \
                                                                                                                              \
         assign ic_b_clear_en[l]   = ic_b_write_en &   ic_b_addr_match[l];                                                    \
                                                                                                                              \
         assign sel_bypass[l]      = ic_b_read_en  &   ic_b_addr_match[l] ;                                                   \
                                                                                                                              \
         assign write_bypass_en[l] = ic_b_read_en  &  ~any_addr_match & (wrptr == l);                                         \
                                                                                                                              \
         rvdff  #(1)  write_bypass_ff (.*, .clk(active_clk),                                                                  \
                                       .din(write_bypass_en[l]), .dout(write_bypass_en_ff[l]));                               \
         rvdffs #(1)  index_val_ff    (.*, .clk(active_clk), .en(write_bypass_en[l] | ic_b_clear_en[l]),                      \
                                       .din(~ic_b_clear_en[l]), .dout(index_valid[l]));                                       \
         rvdff  #(1)  sel_hold_ff     (.*, .clk(active_clk), .din(sel_bypass[l]), .dout(sel_bypass_ff[l]));                   \
                                                                                                                              \
         rvdffe #(.WIDTH(pt.ICACHE_INDEX_HI-pt.ICACHE_TAG_INDEX_LO+1),.OVERRIDE(1)) ic_addr_index    (                        \
               .*, .en(write_bypass_en[l]), .din(ic_b_rw_addr), .dout(wb_index_hold[l]));                                     \
         rvdffe #(``width) rd_data_hold_ff (                                                                                  \
               .*, .en(write_bypass_en_ff[l]), .din (ic_tag_data_raw_packed_pre[``width-1:0]), .dout(wb_packeddout_hold[l])); \
                                                                                                                              \
      end // block: BYPASS                                                                                                    \
                                                                                                                              \
      always_comb begin                                                                                                       \
       any_bypass = '0;                                                                                                       \
       sel_bypass_data = '0;                                                                                                  \
                                                                                                                              \
       for (int l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin                                                                   \
          any_bypass      |=  sel_bypass_ff[l];                                                                               \
          sel_bypass_data |= (sel_bypass_ff[l]) ? wb_packeddout_hold[l] : '0;                                                 \
       end                                                                                                                    \
                                                                                                                              \
         ic_tag_data_raw_packed   =   any_bypass ?  sel_bypass_data :  ic_tag_data_raw_packed_pre ;                           \
      end // always_comb begin                                                                                                \
                                                                                                                              \
   end // if (pt.ICACHE_BYPASS_ENABLE == 1)                                                                                   \
   else begin                                                                                                                 \
       assign ic_tag_data_raw_packed   =   ic_tag_data_raw_packed_pre ;                                                       \
       assign ic_tag_clken_final       =   |ic_tag_clken;                                                                     \
   end


`define EL2_IC_TAG_SRAM_LOGIC(depth,width)                                                                                    \
    if (pt.ICACHE_TAG_BYPASS_ENABLE == 1) begin                                                                               \
                                                                                                                              \
       assign wrptr_in[i] = (wrptr[i] == (pt.ICACHE_TAG_NUM_BYPASS-1)) ? '0 : (wrptr[i] + 1'd1);                              \
                                                                                                                              \
       rvdffs #(pt.ICACHE_TAG_NUM_BYPASS_WIDTH) wrptr_ff(                                                                     \
           .*, .clk(active_clk), .en(|write_bypass_en[i]), .din (wrptr_in[i]), .dout(wrptr[i])                                \
       );                                                                                                                     \
                                                                                                                              \
       assign ic_b_sram_en[i]              = ic_tag_clken[i];                                                                 \
                                                                                                                              \
       assign ic_b_read_en[i]              =  ic_b_sram_en[i] &   (ic_tag_rden_q[i]);                                         \
       assign ic_b_write_en[i]             =  ic_b_sram_en[i] &   (ic_tag_wren_q[i]);                                         \
       assign ic_tag_clken_final[i]        =  ic_b_sram_en[i] &    ~(|sel_bypass[i]);                                         \
                                                                                                                              \
       // LSB is pt.ICACHE_TAG_INDEX_LO]                                                                                      \
       assign ic_b_rw_addr[i] = {ic_rw_addr_q};                                                                               \
                                                                                                                              \
       always_comb begin                                                                                                      \
          any_addr_match[i] = '0;                                                                                             \
                                                                                                                              \
          for (int l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin                                                                \
             any_addr_match[i] |= (ic_b_addr_match[i][l] & index_valid[i][l]);                                                \
          end                                                                                                                 \
       end                                                                                                                    \
                                                                                                                              \
      // it is an error to ever have 2 entries with the same index and both valid                                             \
      for (genvar l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin: BYPASS                                                         \
                                                                                                                              \
         assign ic_b_addr_match[i][l] = (wb_index_hold[i][l] ==  ic_b_rw_addr[i]) & index_valid[i][l];                        \
                                                                                                                              \
         assign ic_b_clear_en[i][l]   = ic_b_write_en[i] &   ic_b_addr_match[i][l];                                           \
                                                                                                                              \
         assign sel_bypass[i][l]      = ic_b_read_en[i]  &   ic_b_addr_match[i][l] ;                                          \
                                                                                                                              \
         assign write_bypass_en[i][l] = ic_b_read_en[i]  &  ~any_addr_match[i] & (wrptr[i] == l);                             \
                                                                                                                              \
         rvdff  #(1)  write_bypass_ff (.*, .clk(active_clk), .din(write_bypass_en[i][l]), .dout(write_bypass_en_ff[i][l]));   \
         rvdffs #(1)  index_val_ff    (.*, .clk(active_clk), .en(write_bypass_en[i][l] | ic_b_clear_en[i][l]),                \
                                       .din(~ic_b_clear_en[i][l]), .dout(index_valid[i][l]));                                 \
         rvdff  #(1)  sel_hold_ff     (.*, .clk(active_clk), .din(sel_bypass[i][l]), .dout(sel_bypass_ff[i][l]));             \
                                                                                                                              \
         rvdffe #(.WIDTH(pt.ICACHE_INDEX_HI-pt.ICACHE_TAG_INDEX_LO+1),.OVERRIDE(1))  ic_addr_index   (                        \
               .*, .en(write_bypass_en[i][l]), .din (ic_b_rw_addr[i]), .dout(wb_index_hold[i][l])                             \
         );                                                                                                                   \
         rvdffe #(``width) rd_data_hold_ff (                                                                                  \
               .*, .en(write_bypass_en_ff[i][l]), .din (ic_tag_data_raw_pre[i][``width-1:0]), .dout(wb_dout_hold[i][l])       \
         );                                                                                                                   \
                                                                                                                              \
      end // block: BYPASS                                                                                                    \
                                                                                                                              \
      always_comb begin                                                                                                       \
       any_bypass[i] = '0;                                                                                                    \
       sel_bypass_data[i] = '0;                                                                                               \
                                                                                                                              \
       for (int l=0; l<pt.ICACHE_TAG_NUM_BYPASS; l++) begin                                                                   \
          any_bypass[i]      |=  sel_bypass_ff[i][l];                                                                         \
          sel_bypass_data[i] |= (sel_bypass_ff[i][l]) ? wb_dout_hold[i][l] : '0;                                              \
       end                                                                                                                    \
                                                                                                                              \
         ic_tag_data_raw[i]   =   any_bypass[i] ?  sel_bypass_data[i] :  ic_tag_data_raw_pre[i] ;                             \
      end // always_comb begin                                                                                                \
                                                                                                                              \
   end // if (pt.ICACHE_BYPASS_ENABLE == 1)                                                                                   \
   else begin                                                                                                                 \
       assign ic_tag_data_raw[i]   =   ic_tag_data_raw_pre[i] ;                                                               \
       assign ic_tag_clken_final[i]       =   ic_tag_clken[i];                                                                \
   end


`define EL2_PACKED_IC_DATA_SRAM_LOGIC(depth,width,waywidth)                                            \
    if (pt.ICACHE_BYPASS_ENABLE == 1) begin                                                            \
                                                                                                       \
       assign wrptr_in[k] = (wrptr[k] == (pt.ICACHE_NUM_BYPASS-1)) ? '0 : (wrptr[k] + 1'd1);           \
                                                                                                       \
       rvdffs  #(pt.ICACHE_NUM_BYPASS_WIDTH)  wrptr_ff(                                                \
            .*, .clk(active_clk), .en(|write_bypass_en[k]), .din (wrptr_in[k]), .dout(wrptr[k])        \
       );                                                                                              \
                                                                                                       \
       assign ic_b_sram_en[k]              = |ic_bank_way_clken[k];                                    \
                                                                                                       \
                                                                                                       \
       assign ic_b_read_en[k]              =  ic_b_sram_en[k]  &  (|ic_b_sb_rden[k]) ;                 \
       assign ic_b_write_en[k]             =  ic_b_sram_en[k] &   (|ic_b_sb_wren[k]);                  \
       assign ic_bank_way_clken_final[k]   =  ic_b_sram_en[k] &    ~(|sel_bypass[k]);                  \
                                                                                                       \
       assign ic_b_rw_addr[k] = {ic_rw_addr[31:pt.ICACHE_INDEX_HI+1],ic_rw_addr_bank_q[k]};            \
       assign ic_b_rw_addr_index_only[k] = ic_rw_addr_bank_q[k];                                       \
                                                                                                       \
       always_comb begin                                                                               \
          any_addr_match[k] = '0;                                                                      \
                                                                                                       \
          for (int l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin                                             \
             any_addr_match[k] |= ic_b_addr_match[k][l];                                               \
          end                                                                                          \
       end                                                                                             \
                                                                                                       \
      // it is an error to ever have 2 entries with the same index and both valid                      \
      for (genvar l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin: BYPASS                                      \
                                                                                                       \
         // full match up to bit 31                                                                    \
         assign ic_b_addr_match[k][l] = (wb_index_hold[k][l] ==  ic_b_rw_addr[k]) & index_valid[k][l]; \
         assign ic_b_addr_match_index_only[k][l] = (wb_index_hold[k][l][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO] ==  ic_b_rw_addr_index_only[k]) & index_valid[k][l]; \
                                                                                                                              \
         assign ic_b_clear_en[k][l]   = ic_b_write_en[k] &   ic_b_addr_match_index_only[k][l];                                \
                                                                                                                              \
         assign sel_bypass[k][l]      = ic_b_read_en[k]  &   ic_b_addr_match[k][l] ;                                          \
                                                                                                                              \
         assign write_bypass_en[k][l] = ic_b_read_en[k]  &  ~any_addr_match[k] & (wrptr[k] == l);                             \
                                                                                                                              \
         rvdff  #(1)  write_bypass_ff (.*, .clk(active_clk), .din(write_bypass_en[k][l]), .dout(write_bypass_en_ff[k][l]));   \
         rvdffs #(1)  index_val_ff    (.*, .clk(active_clk), .en(write_bypass_en[k][l] | ic_b_clear_en[k][l]),                \
                                       .din(~ic_b_clear_en[k][l]),  .dout(index_valid[k][l])) ;                               \
         rvdff  #(1)  sel_hold_ff     (.*, .clk(active_clk), .din(sel_bypass[k][l]),      .dout(sel_bypass_ff[k][l]));        \
                                                                                                                              \
         rvdffe #((31-pt.ICACHE_DATA_INDEX_LO+1)) ic_addr_index (                                                             \
               .*, .en(write_bypass_en[k][l]), .din (ic_b_rw_addr[k]), .dout(wb_index_hold[k][l])                             \
         );                                                                                                                   \
         rvdffe #((``waywidth*pt.ICACHE_NUM_WAYS)) rd_data_hold_ff (                                                          \
               .*, .en(write_bypass_en_ff[k][l]), .din (wb_packeddout_pre[k]), .dout(wb_packeddout_hold[k][l])                \
         );                                                                                                                   \
                                                                                                                              \
      end // block: BYPASS                                                                                                    \
                                                                                                                              \
      always_comb begin                                                                                                       \
       any_bypass[k] = '0;                                                                                                    \
       sel_bypass_data[k] = '0;                                                                                               \
                                                                                                                              \
       for (int l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin                                                                       \
          any_bypass[k]      |=  sel_bypass_ff[k][l];                                                                         \
            sel_bypass_data[k] |= (sel_bypass_ff[k][l]) ? wb_packeddout_hold[k][l] : '0;                                      \
       end                                                                                                                    \
                                                                                                                              \
         wb_packeddout[k]   =   any_bypass[k] ?  sel_bypass_data[k] :  wb_packeddout_pre[k] ;                                 \
      end // always_comb begin                                                                                                \
                                                                                                                              \
   end // if (pt.ICACHE_BYPASS_ENABLE == 1)                                                                                   \
   else begin                                                                                                                 \
       assign wb_packeddout[k]   =   wb_packeddout_pre[k] ;                                                                   \
       assign ic_bank_way_clken_final[k]   =  |ic_bank_way_clken[k] ;                                                         \
   end



`define EL2_IC_DATA_SRAM_LOGIC(depth,width)                                                                       \
  if (pt.ICACHE_BYPASS_ENABLE == 1) begin                                                                         \
     assign wrptr_in_up[i][k] = (wrptr_up[i][k] == (pt.ICACHE_NUM_BYPASS-1)) ? '0 : (wrptr_up[i][k] + 1'd1);      \
     rvdffs  #(pt.ICACHE_NUM_BYPASS_WIDTH)  wrptr_ff(                                                             \
           .*, .clk(active_clk),  .en(|write_bypass_en_up[i][k]), .din (wrptr_in_up[i][k]), .dout(wrptr_up[i][k]) \
     );                                                                                                           \
     assign ic_b_sram_en_up[i][k]              = ic_bank_way_clken[k][i];                             \
     assign ic_b_read_en_up[i][k]              =  ic_b_sram_en_up[i][k] &   ic_b_sb_rden[k][i];       \
     assign ic_b_write_en_up[i][k]             =  ic_b_sram_en_up[i][k] &   ic_b_sb_wren[k][i];       \
     assign ic_bank_way_clken_final_up[i][k]   =  ic_b_sram_en_up[i][k] &    ~(|sel_bypass_up[i][k]); \
     assign ic_b_rw_addr_up[i][k] = {ic_rw_addr[31:pt.ICACHE_INDEX_HI+1],ic_rw_addr_bank_q[k]};       \
     assign ic_b_rw_addr_index_only_up[i][k] = ic_rw_addr_bank_q[k];                                  \
     always_comb begin                                                                                \
        any_addr_match_up[i][k] = '0;                                                                 \
        for (int l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin                                              \
           any_addr_match_up[i][k] |= ic_b_addr_match_up[i][k][l];                                    \
        end                                                                                           \
     end                                                                                              \
    // it is an error to ever have 2 entries with the same index and both valid                       \
    for (genvar l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin: BYPASS                                       \
       // full match up to bit 31                                                                     \
       assign ic_b_addr_match_up[i][k][l] = (wb_index_hold_up[i][k][l] ==  ic_b_rw_addr_up[i][k]) & index_valid_up[i][k][l];           \
       assign ic_b_addr_match_index_only_up[i][k][l] = (wb_index_hold_up[i][k][l][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO] ==  ic_b_rw_addr_index_only_up[i][k]) & index_valid_up[i][k][l]; \
                                                                                                                                       \
       assign ic_b_clear_en_up[i][k][l]   = ic_b_write_en_up[i][k] &   ic_b_addr_match_index_only_up[i][k][l];                         \
                                                                                                                                       \
       assign sel_bypass_up[i][k][l]      = ic_b_read_en_up[i][k]  &   ic_b_addr_match_up[i][k][l] ;                                   \
                                                                                                                                       \
       assign write_bypass_en_up[i][k][l] = ic_b_read_en_up[i][k]  &  ~any_addr_match_up[i][k] & (wrptr_up[i][k] == l);                \
                                                                                                                                       \
       rvdff  #(1)  write_bypass_ff (.*, .clk(active_clk), .din(write_bypass_en_up[i][k][l]), .dout(write_bypass_en_ff_up[i][k][l]));  \
       rvdffs #(1)  index_val_ff    (.*, .clk(active_clk), .en(write_bypass_en_up[i][k][l] | ic_b_clear_en_up[i][k][l]),               \
                                     .din(~ic_b_clear_en_up[i][k][l]),  .dout(index_valid_up[i][k][l])) ;                              \
       rvdff  #(1)  sel_hold_ff     (.*, .clk(active_clk), .din(sel_bypass_up[i][k][l]), .dout(sel_bypass_ff_up[i][k][l]));            \
       rvdffe #((31-pt.ICACHE_DATA_INDEX_LO+1)) ic_addr_index (                                                                        \
             .*, .en(write_bypass_en_up[i][k][l]), .din (ic_b_rw_addr_up[i][k]), .dout(wb_index_hold_up[i][k][l])                      \
       );                                                                                                                              \
       rvdffe #(``width) rd_data_hold_ff (                                                                                             \
             .*, .en(write_bypass_en_ff_up[i][k][l]), .din (wb_dout_pre_up[i][k]),  .dout(wb_dout_hold_up[i][k][l])                    \
       );                                                                                                                              \
    end                                                                                                                                \
    always_comb begin                                                                             \
     any_bypass_up[i][k] = '0;                                                                    \
     sel_bypass_data_up[i][k] = '0;                                                               \
     for (int l=0; l<pt.ICACHE_NUM_BYPASS; l++) begin                                             \
        any_bypass_up[i][k]      |=  sel_bypass_ff_up[i][k][l];                                   \
        sel_bypass_data_up[i][k] |= (sel_bypass_ff_up[i][k][l]) ? wb_dout_hold_up[i][k][l] : '0;  \
     end                                                                                          \
     wb_dout[i][k]   =   any_bypass_up[i][k] ?  sel_bypass_data_up[i][k] :  wb_dout_pre_up[i][k]; \
     end                                                                                          \
   end                                                                                            \
   else begin                                                                                     \
       assign wb_dout[i][k]                      =   wb_dout_pre_up[i][k];                        \
       assign ic_bank_way_clken_final_up[i][k]   =  ic_bank_way_clken[k][i];                      \
   end
