// Macros for ICache

`define EL2_TIE_OFF_PACKED                                \
   assign el2_mem_export.ic_tag_data_raw_packed_pre = '0; \
   assign el2_mem_export.wb_packeddout_pre = '0;

`define EL2_TIE_OFF_NON_PACKED                     \
   assign el2_mem_export.ic_tag_data_raw_pre = '0; \
   assign el2_mem_export.wb_dout_pre_up = '0;

`define EL2_IC_TAG_PACKED_SRAM(depth,width)                                                       \
   ram_be_``depth``x``width  ic_way_tag (                                                         \
      .CLK (el2_mem_export.clk),                                                                  \
      .ME  (|el2_mem_export.ic_tag_clken_final),                                                  \
      .WE  (|el2_mem_export.ic_tag_wren_q[pt.ICACHE_NUM_WAYS-1:0]),                               \
      .WEM (el2_mem_export.ic_tag_wren_biten_vec[``width-1:0]),                                   \
                                                                                                  \
      .D   ({pt.ICACHE_NUM_WAYS{el2_mem_export.ic_tag_wr_data[``width/pt.ICACHE_NUM_WAYS-1:0]}}), \
      .ADR (el2_mem_export.ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]),              \
      .Q   (el2_mem_export.ic_tag_data_raw_packed_pre[``width-1:0]),                              \
      .ROP ( ),                                                                                   \
                                                                                                  \
      .TEST1    (1'b0),                                                                           \
      .RME      (1'b0),                                                                           \
      .RM       (4'b0000),                                                                        \
                                                                                                  \
      .LS       (1'b0),                                                                           \
      .DS       (1'b0),                                                                           \
      .SD       (1'b0),                                                                           \
                                                                                                  \
      .TEST_RNM (1'b0),                                                                           \
      .BC1      (1'b0),                                                                           \
      .BC2      (1'b0)                                                                            \
   );


`define EL2_IC_TAG_SRAM(depth,width,i)                                              \
   ram_``depth``x``width  ic_way_tag (                                              \
      .CLK (el2_mem_export.clk),                                                    \
      .ME(el2_mem_export.ic_tag_clken_final[i]),                                    \
      .WE (el2_mem_export.ic_tag_wren_q[i]),                                        \
      .D  (el2_mem_export.ic_tag_wr_data[``width-1:0]),                             \
      .ADR(el2_mem_export.ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]), \
      .Q  (el2_mem_export.ic_tag_data_raw_pre[i][``width-1:0]),                     \
      .ROP ( ),                                                                     \
                                                                                    \
      .TEST1    (1'b0),                                                             \
      .RME      (1'b0),                                                             \
      .RM       (4'b0000),                                                          \
                                                                                    \
      .LS       (1'b0),                                                             \
      .DS       (1'b0),                                                             \
      .SD       (1'b0),                                                             \
                                                                                    \
      .TEST_RNM (1'b0),                                                             \
      .BC1      (1'b0),                                                             \
      .BC2      (1'b0)                                                              \
   );


`define EL2_PACKED_IC_DATA_SRAM(depth,width,waywidth,k)                                         \
    ram_be_``depth``x``width  ic_bank_sb_way_data (                                             \
      .CLK   (el2_mem_export.clk),                                                              \
      .WE    (|el2_mem_export.ic_b_sb_wren[k]),              // OR of all the ways in the bank  \
      .WEM   (el2_mem_export.ic_b_sb_bit_en_vec[k]),         // 284 bits of bit enables         \
      .D     ({pt.ICACHE_NUM_WAYS{el2_mem_export.ic_sb_wr_data[k][``waywidth-1:0]}}),           \
      .ADR   (el2_mem_export.ic_rw_addr_bank_q[k][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO]), \
      .Q     (el2_mem_export.wb_packeddout_pre[k]),                                             \
      .ME    (|el2_mem_export.ic_bank_way_clken_final[k]),                                      \
      .ROP   ( ),                                                                               \
      .TEST1 (1'b0),                                                                            \
      .RME   (1'b0),                                                                            \
      .RM    (4'b0000),                                                                         \
                                                                                                \
      .LS    (1'b0),                                                                            \
      .DS    (1'b0),                                                                            \
      .SD    (1'b0),                                                                            \
                                                                                                \
      .TEST_RNM (1'b0),                                                                         \
      .BC1      (1'b0),                                                                         \
      .BC2      (1'b0)                                                                          \
   );


`define EL2_IC_DATA_SRAM(depth,width,i,k)                                                    \
   ram_``depth``x``width ic_bank_sb_way_data (                                               \
      .CLK (el2_mem_export.clk),                                                             \
      .ME(el2_mem_export.ic_bank_way_clken_final_up[i][k]),                                  \
      .WE (el2_mem_export.ic_b_sb_wren[k][i]),                                               \
      .D  (el2_mem_export.ic_sb_wr_data[k][``width-1:0]),                                    \
      .ADR(el2_mem_export.ic_rw_addr_bank_q[k][pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO]), \
      .Q  (el2_mem_export.wb_dout_pre_up[i][k]),                                             \
      .ROP ( ),                                                                              \
      .TEST1   (1'b0),                                                                       \
      .RME     (1'b0),                                                                       \
      .RM      (4'b0000),                                                                    \
                                                                                             \
      .LS       (1'b0),                                                                      \
      .DS       (1'b0),                                                                      \
      .SD       (1'b0),                                                                      \
                                                                                             \
      .TEST_RNM (1'b0),                                                                      \
      .BC1      (1'b0),                                                                      \
      .BC2      (1'b0)                                                                       \
   );
