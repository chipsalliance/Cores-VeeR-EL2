# 15 Veer El2 Core Complex Port List

Table 15-1 lists the core complex signals.
Not all signals are present in a given instantiation.
For example, a core complex can only have one bus interface type (AXI4 or AHB-Lite).
Signals which are asynchronous to the core complex clock (clk) are marked with "(async)" in the 'Description' column.

<table class="docutils data align-default">
<caption><span class="caption-text">Table 15-1 Core Complex Signals</span><a class="headerlink" href="#id1" title="Link to this table">¶</a></caption>
<colgroup>
<col style="width: 61%" />
<col style="width: 5%" />
<col style="width: 33%" />
</colgroup>
<thead>
<tr>
<th>Signal</th>
<th>Dir</th>
<th>Description</th>
</tr>
</thead>
<tbody>
<tr>
<td colspan='3' style="text-align:center;"><b>Clock and Clock Enables</b></td>
</tr>
<tr>
<td>clk</td>
<td>in</td>
<td>Core complex clock</td>
</tr>
<tr>
<td>ifu_bus_clk_en</td>
<td>in</td>
<td>IFU master system bus clock enable</td>
</tr>
<tr>
<td>lsu_bus_clk_en</td>
<td>in</td>
<td>LSU master system bus clock enable</td>
</tr>
<tr>
<td>dbg_bus_clk_en</td>
<td>in</td>
<td>Debug master system bus clock enable</td>
</tr>
<tr>
<td>dma_bus_clk_en</td>
<td>in</td>
<td>DMA slave system bus clock enable</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Reset</b></td>
</tr>
<tr>
<td>rst_l</td>
<td>in</td>
<td>Core complex reset (excl. Debug Module)</td>
</tr>
<tr>
<td>rst_vec[31:1]</td>
<td>in</td>
<td>Core reset vector</td>
</tr>
<tr>
<td>dbg_rst_l</td>
<td>in</td>
<td>Debug Module reset (incl. JTAG synchronizers)</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Interrupts</b></td>
</tr>
<tr>
<td>nmi_int</td>
<td>in</td>
<td>Non-Maskable Interrupt (async)</td>
</tr>
<tr>
<td>nmi_vec[31:1]</td>
<td>in</td>
<td>Non-Maskable Interrupt vector</td>
</tr>
<tr>
<td>soft_int</td>
<td>in</td>
<td>Standard RISC-V software interrupt (async)</td>
</tr>
<tr>
<td>timer_int</td>
<td>in</td>
<td>Standard RISC-V timer interrupt (async)</td>
</tr>
<tr>
<td>extintsrc_req[pt.PIC_TOTAL_INT:1]</td>
<td>in</td>
<td>External interrupts (async)</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Core ID</b></td>
</tr>
<tr>
<td>core_id[31:4]</td>
<td>in</td>
<td>Core ID (mapped to mhartid[31:4])</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>System Bus Interfaces</b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>AXI4</b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Instruction Fetch Unit Master AXI445</b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write address channel signals</b></td>
</tr>
<tr>
<td>
ifu_axi_awvalid</td>
<td>out</td>
<td>Write address valid (hardwired to 0)</td>
</tr>
<tr>
<td>ifu_axi_awready</td>
<td>in</td>
<td>Write address ready</td>
</tr>
<tr>
<td>ifu_axi_awid[pt.IFU_BUS_TAG-1:0]</td>
<td>out</td>
<td>Write address ID</td>
</tr>
<tr>
<td>ifu_axi_awaddr[31:0]</td>
<td>out</td>
<td>Write address</td>
</tr>
<tr>
<td>ifu_axi_awlen[7:0]</td>
<td>out</td>
<td>Burst length</td>
</tr>
<tr>
<td>ifu_axi_awsize[2:0]</td>
<td>out</td>
<td>Burst size</td>
</tr>
<tr>
<td>ifu_axi_awburst[1:0]</td>
<td>out</td>
<td>Burst type</td>
</tr>
<tr>
<td>ifu_axi_awlock</td>
<td>out</td>
<td>Lock type</td>
</tr>
<tr>
<td>ifu_axi_awcache[3:0]</td>
<td>out</td>
<td>Memory type</td>
</tr>
<tr>
<td>ifu_axi_awprot[2:0]</td>
<td>out</td>
<td>Protection type</td>
</tr>
<tr>
<td>ifu_axi_awqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS)</td>
</tr>
<tr>
<td>ifu_axi_awregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write data channel signals</b></td>
</tr>
<tr>
<td> ifu_axi_wvalid</td>
<td>out</td>
<td>Write valid (hardwired to 0)</td>
</tr>
<tr>
<td>ifu_axi_wready</td>
<td>in</td>
<td>Write ready</td>
</tr>
<tr>
<td>ifu_axi_wdata[63:0]</td>
<td>out</td>
<td>Write data</td>
</tr>
<tr>
<td>ifu_axi_wstrb[7:0]</td>
<td>out</td>
<td>Write strobes</td>
</tr>
<tr>
<td>ifu_axi_wlast</td>
<td>out</td>
<td>Write last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write response channel signals</b></td>
</tr>
<tr>
<td> ifu_axi_bvalid</td>
<td>in</td>
<td>Write response valid</td>
</tr>
<tr>
<td>ifu_axi_bready</td>
<td>out</td>
<td>Write response ready (hardwired to 0)</td>
</tr>
<tr>
<td>ifu_axi_bid[pt.IFU_BUS_TAG-1:0]</td>
<td>in</td>
<td>Response ID tag</td>
</tr>
<tr>
<td>ifu_axi_bresp[1:0]</td>
<td>in</td>
<td>Write response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read address channel signals </b></td>
</tr>
<tr>
<td>ifu_axi_arvalid</td>
<td>out</td>
<td>Read address valid</td>
</tr>
<tr>
<td>ifu_axi_arready</td>
<td>in</td>
<td>Read address ready</td>
</tr>
<tr>
<td>ifu_axi_arid[pt.IFU_BUS_TAG-1:0]</td>
<td>out</td>
<td>Read address ID</td>
</tr>
<tr>
<td>ifu_axi_araddr[31:0]</td>
<td>out</td>
<td>Read address</td>
</tr>
<tr>
<td>ifu_axi_arlen[7:0]</td>
<td>out</td>
<td>Burst length (hardwired to 0b0000_0000)</td>
</tr>
<tr>
<td>ifu_axi_arsize[2:0]</td>
<td>out</td>
<td>Burst size (hardwired to 0b011)</td>
</tr>
<tr>
<td>ifu_axi_arburst[1:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b01)</td>
</tr>
<tr>
<td>ifu_axi_arlock</td>
<td>out</td>
<td>Lock type (hardwired to 0)</td>
</tr>
<tr>
<td>ifu_axi_arcache[3:0]</td>
<td>out</td>
<td>Memory type (hardwired to 0b1111)</td>
</tr>
<tr>
<td>ifu_axi_arprot[2:0]</td>
<td>out</td>
<td>Protection type (hardwired to 0b100)</td>
</tr>
<tr>
<td>ifu_axi_arqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS) (hardwired to 0b0000)</td>
</tr>
<tr>
<td>ifu_axi_arregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read data channel signals </b></td>
</tr>
<tr>
<td>ifu_axi_rvalid</td>
<td>in</td>
<td>Read valid</td>
</tr>
<tr>
<td>ifu_axi_rready</td>
<td>out</td>
<td>Read ready</td>
</tr>
<tr>
<td>ifu_axi_rid[pt.IFU_BUS_TAG-1:0]</td>
<td>in</td>
<td>Read ID tag</td>
</tr>
<tr>
<td>ifu_axi_rdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>ifu_axi_rresp[1:0]</td>
<td>in</td>
<td>Read response</td>
</tr>
<tr>
<td>ifu_axi_rlast</td>
<td>in</td>
<td>Read last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Load/Store Unit Master AXI4</b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write address channel signals </b></td>
</tr>
<tr>
<td>lsu_axi_awvalid</td>
<td>out</td>
<td>Write address valid</td>
</tr>
<tr>
<td>lsu_axi_awready</td>
<td>in</td>
<td>Write address ready</td>
</tr>
<tr>
<td>lsu_axi_awid[pt.LSU_BUS_TAG-1:0]</td>
<td>out</td>
<td>Write address ID</td>
</tr>
<tr>
<td>lsu_axi_awaddr[31:0]</td>
<td>out</td>
<td>Write address</td>
</tr>
<tr>
<td>lsu_axi_awlen[7:0]</td>
<td>out</td>
<td>Burst length (hardwired to 0b0000_0000)</td>
</tr>
<tr>
<td>lsu_axi_awsize[2:0]</td>
<td>out</td>
<td>Burst size</td>
</tr>
<tr>
<td>lsu_axi_awburst[1:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b01)</td>
</tr>
<tr>
<td>lsu_axi_awlock</td>
<td>out</td>
<td>Lock type (hardwired to 0)</td>
</tr>
<tr>
<td>lsu_axi_awcache[3:0]</td>
<td>out</td>
<td>Memory type</td>
</tr>
<tr>
<td>lsu_axi_awprot[2:0]</td>
<td>out</td>
<td>Protection type (hardwired to 0b000)</td>
</tr>
<tr>
<td>lsu_axi_awqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS) (hardwired to 0b0000)</td>
</tr>
<tr>
<td>lsu_axi_awregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write data channel signals </b></td>
</tr>
<tr>
<td>lsu_axi_wvalid</td>
<td>out</td>
<td>Write valid</td>
</tr>
<tr>
<td>lsu_axi_wready</td>
<td>in</td>
<td>Write ready</td>
</tr>
<tr>
<td>lsu_axi_wdata[63:0]</td>
<td>out</td>
<td>Write data</td>
</tr>
<tr>
<td>lsu_axi_wstrb[7:0]</td>
<td>out</td>
<td>Write strobes</td>
</tr>
<tr>
<td>lsu_axi_wlast</td>
<td>out</td>
<td>Write last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write response channel signals </b></td>
</tr>
<tr>
<td>lsu_axi_bvalid</td>
<td>in</td>
<td>Write response valid</td>
</tr>
<tr>
<td>lsu_axi_bready</td>
<td>out</td>
<td>Write response ready</td>
</tr>
<tr>
<td>lsu_axi_bid[pt.LSU_BUS_TAG-1:0]</td>
<td>in</td>
<td>Response ID tag</td>
</tr>
<tr>
<td>lsu_axi_bresp[1:0]</td>
<td>in</td>
<td>Write response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read address channel signals </b></td>
</tr>
<tr>
<td>lsu_axi_arvalid</td>
<td>out</td>
<td>Read address valid</td>
</tr>
<tr>
<td>lsu_axi_arready</td>
<td>in</td>
<td>Read address ready</td>
</tr>
<tr>
<td>lsu_axi_arid[pt.LSU_BUS_TAG-1:0]</td>
<td>out</td>
<td>Read address ID</td>
</tr>
<tr>
<td>lsu_axi_araddr[31:0]</td>
<td>out</td>
<td>Read address</td>
</tr>
<tr>
<td>lsu_axi_arlen[7:0]</td>
<td>out</td>
<td>Burst length (hardwired to 0b0000_0000)</td>
</tr>
<tr>
<td>lsu_axi_arsize[2:0]</td>
<td>out</td>
<td>Burst size</td>
</tr>
<tr>
<td>lsu_axi_arburst[1:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b01)</td>
</tr>
<tr>
<td>lsu_axi_arlock</td>
<td>out</td>
<td>Lock type (hardwired to 0)</td>
</tr>
<tr>
<td>lsu_axi_arcache[3:0]</td>
<td>out</td>
<td>Memory type</td>
</tr>
<tr>
<td>lsu_axi_arprot[2:0]</td>
<td>out</td>
<td>Protection type (hardwired to 0b000)</td>
</tr>
<tr>
<td>lsu_axi_arqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS) (hardwired to 0b0000)</td>
</tr>
<tr>
<td>lsu_axi_arregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read data channel signals </b></td>
</tr>
<tr>
<td>lsu_axi_rvalid</td>
<td>in</td>
<td>Read valid</td>
</tr>
<tr>
<td>lsu_axi_rready</td>
<td>out</td>
<td>Read ready</td>
</tr>
<tr>
<td>lsu_axi_rid[pt.LSU_BUS_TAG-1:0]</td>
<td>in</td>
<td>Read ID tag</td>
</tr>
<tr>
<td>lsu_axi_rdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>lsu_axi_rresp[1:0]</td>
<td>in</td>
<td>Read response</td>
</tr>
<tr>
<td>lsu_axi_rlast</td>
<td>in</td>
<td>Read last</td>
</tr>
<tr>
<th colspan='3'>
System Bus (Debug) Master AXI4
</th>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b> Write address channel signals</b></td>
</tr>
<tr>
<td>
sb_axi_awvalid</td>
<td>out</td>
<td>Write address valid</td>
</tr>
<tr>
<td>sb_axi_awready</td>
<td>in</td>
<td>Write address ready</td>
</tr>
<tr>
<td>sb_axi_awid[pt.SB_BUS_TAG-1:0]</td>
<td>out</td>
<td>Write address ID (hardwired to 0)</td>
</tr>
<tr>
<td>sb_axi_awaddr[31:0]</td>
<td>out</td>
<td>Write address</td>
</tr>
<tr>
<td>sb_axi_awlen[7:0]</td>
<td>out</td>
<td>Burst length (hardwired to 0b0000_0000)</td>
</tr>
<tr>
<td>sb_axi_awsize[2:0]</td>
<td>out</td>
<td>Burst size</td>
</tr>
<tr>
<td>sb_axi_awburst[1:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b01)</td>
</tr>
<tr>
<td>sb_axi_awlock</td>
<td>out</td>
<td>Lock type (hardwired to 0)</td>
</tr>
<tr>
<td>sb_axi_awcache[3:0]</td>
<td>out</td>
<td>Memory type (hardwired to 0b1111)</td>
</tr>
<tr>
<td>sb_axi_awprot[2:0]</td>
<td>out</td>
<td>Protection type (hardwired to 0b000)</td>
</tr>
<tr>
<td>sb_axi_awqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS) (hardwired to 0b0000)</td>
</tr>
<tr>
<td>sb_axi_awregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b> Write data channel signals</b></td>
</tr>
<tr>
<td>sb_axi_wvalid</td>
<td>out</td>
<td>Write valid</td>
</tr>
<tr>
<td>sb_axi_wready</td>
<td>in</td>
<td>Write ready</td>
</tr>
<tr>
<td>sb_axi_wdata[63:0]</td>
<td>out</td>
<td>Write data</td>
</tr>
<tr>
<td>sb_axi_wstrb[7:0]</td>
<td>out</td>
<td>Write strobes</td>
</tr>
<tr>
<td>sb_axi_wlast</td>
<td>out</td>
<td>Write last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write response channel signals </b></td>
</tr>
<tr>
<td>sb_axi_bvalid</td>
<td>in</td>
<td>Write response valid</td>
</tr>
<tr>
<td>sb_axi_bready</td>
<td>out</td>
<td>Write response ready</td>
</tr>
<tr>
<td>sb_axi_bid[pt.SB_BUS_TAG-1:0]</td>
<td>in</td>
<td>Response ID tag</td>
</tr>
<tr>
<td>sb_axi_bresp[1:0]</td>
<td>in</td>
<td>Write response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read address channel signals </b></td>
</tr>
<tr>
<td>sb_axi_arvalid</td>
<td>out</td>
<td>Read address valid</td>
</tr>
<tr>
<td>sb_axi_arready</td>
<td>in</td>
<td>Read address ready</td>
</tr>
<tr>
<td>sb_axi_arid[pt.SB_BUS_TAG-1:0]</td>
<td>out</td>
<td>Read address ID (hardwired to 0)</td>
</tr>
<tr>
<td>sb_axi_araddr[31:0]</td>
<td>out</td>
<td>Read address</td>
</tr>
<tr>
<td>sb_axi_arlen[7:0]</td>
<td>out</td>
<td>Burst length (hardwired to 0b0000_0000)</td>
</tr>
<tr>
<td>sb_axi_arsize[2:0]</td>
<td>out</td>
<td>Burst size</td>
</tr>
<tr>
<td>sb_axi_arburst[1:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b01)</td>
</tr>
<tr>
<td>sb_axi_arlock</td>
<td>out</td>
<td>Lock type (hardwired to 0)</td>
</tr>
<tr>
<td>sb_axi_arcache[3:0]</td>
<td>out</td>
<td>Memory type (hardwired to 0b0000)</td>
</tr>
<tr>
<td>sb_axi_arprot[2:0]</td>
<td>out</td>
<td>Protection type (hardwired to 0b000)</td>
</tr>
<tr>
<td>sb_axi_arqos[3:0]</td>
<td>out</td>
<td>Quality of Service (QoS) (hardwired to 0b0000)</td>
</tr>
<tr>
<td>sb_axi_arregion[3:0]</td>
<td>out</td>
<td>Region identifier</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read data channel signals </b></td>
</tr>
<tr>
<td>sb_axi_rvalid</td>
<td>in</td>
<td>Read valid</td>
</tr>
<tr>
<td>sb_axi_rready</td>
<td>out</td>
<td>Read ready</td>
</tr>
<tr>
<td>sb_axi_rid[pt.SB_BUS_TAG-1:0]</td>
<td>in</td>
<td>Read ID tag</td>
</tr>
<tr>
<td>sb_axi_rdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>sb_axi_rresp[1:0]</td>
<td>in</td>
<td>Read response</td>
</tr>
<tr>
<td>sb_axi_rlast</td>
<td>in</td>
<td>Read last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>DMA Slave AXI4 </b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write address channel signals </b></td>
</tr>
<tr>
<td>dma_axi_awvalid</td>
<td>in</td>
<td>Write address valid</td>
</tr>
<tr>
<td>dma_axi_awready</td>
<td>out</td>
<td>Write address ready</td>
</tr>
<tr>
<td>dma_axi_awid[pt.DMA_BUS_TAG-1:0]</td>
<td>in</td>
<td>Write address ID</td>
</tr>
<tr>
<td>dma_axi_awaddr[31:0]</td>
<td>in</td>
<td>Write address</td>
</tr>
<tr>
<td>dma_axi_awlen[7:0]</td>
<td>in</td>
<td>Burst length</td>
</tr>
<tr>
<td>dma_axi_awsize[2:0]</td>
<td>in</td>
<td>Burst size</td>
</tr>
<tr>
<td>dma_axi_awburst[1:0]</td>
<td>in</td>
<td>Burst type</td>
</tr>
<tr>
<td>dma_axi_awprot[2:0]</td>
<td>in</td>
<td>Protection type</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write data channel signals </b></td>
</tr>
<tr>
<td>dma_axi_wvalid</td>
<td>in</td>
<td>Write valid</td>
</tr>
<tr>
<td>dma_axi_wready</td>
<td>out</td>
<td>Write ready</td>
</tr>
<tr>
<td>dma_axi_wdata[63:0]</td>
<td>in</td>
<td>Write data</td>
</tr>
<tr>
<td>dma_axi_wstrb[7:0]</td>
<td>in</td>
<td>Write strobes</td>
</tr>
<tr>
<td>dma_axi_wlast</td>
<td>in</td>
<td>Write last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Write response channel signals </b></td>
</tr>
<tr>
<td>dma_axi_bvalid</td>
<td>out</td>
<td>Write response valid</td>
</tr>
<tr>
<td>dma_axi_bready</td>
<td>in</td>
<td>Write response ready</td>
</tr>
<tr>
<td>dma_axi_bid[pt.DMA_BUS_TAG-1:0]</td>
<td>out</td>
<td>Response ID tag</td>
</tr>
<tr>
<td>dma_axi_bresp[1:0]</td>
<td>out</td>
<td>Write response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read address channel signals </b></td>
</tr>
<tr>
<td>dma_axi_arvalid</td>
<td>in</td>
<td>Read address valid</td>
</tr>
<tr>
<td>dma_axi_arready</td>
<td>out</td>
<td>Read address ready</td>
</tr>
<tr>
<td>dma_axi_arid[pt.DMA_BUS_TAG-1:0]</td>
<td>in</td>
<td>Read address ID</td>
</tr>
<tr>
<td>dma_axi_araddr[31:0]</td>
<td>in</td>
<td>Read address</td>
</tr>
<tr>
<td>dma_axi_arlen[7:0]</td>
<td>in</td>
<td>Burst length</td>
</tr>
<tr>
<td>dma_axi_arsize[2:0]</td>
<td>in</td>
<td>Burst size</td>
</tr>
<tr>
<td>dma_axi_arburst[1:0]</td>
<td>in</td>
<td>Burst type</td>
</tr>
<tr>
<td>dma_axi_arprot[2:0]</td>
<td>in</td>
<td>Protection type</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Read data channel signals </b></td>
</tr>
<tr>
<td>dma_axi_rvalid</td>
<td>out</td>
<td>Read valid</td>
</tr>
<tr>
<td>dma_axi_rready</td>
<td>in</td>
<td>Read ready</td>
</tr>
<tr>
<td>dma_axi_rid[pt.DMA_BUS_TAG-1:0]</td>
<td>out</td>
<td>Read ID tag</td>
</tr>
<tr>
<td>dma_axi_rdata[63:0]</td>
<td>out</td>
<td>Read data</td>
</tr>
<tr>
<td>dma_axi_rresp[1:0]</td>
<td>out</td>
<td>Read response</td>
</tr>
<tr>
<td>dma_axi_rlast</td>
<td>out</td>
<td>Read last</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>AHB-Lite</b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Instruction Fetch Unit Master AHB-Lite </b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Master signals</b></td>
</tr>
<tr>
<td>
haddr[31:0]</td>
<td>out</td>
<td>System address</td>
</tr>
<tr>
<td>hburst[2:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b000)</td>
</tr>
<tr>
<td>hmastlock</td>
<td>out</td>
<td>Locked transfer (hardwired to 0)</td>
</tr>
<tr>
<td>hprot[3:0]</td>
<td>out</td>
<td>Protection control</td>
</tr>
<tr>
<td>hsize[2:0]</td>
<td>out</td>
<td>Transfer size</td>
</tr>
<tr>
<td>htrans[1:0]</td>
<td>out</td>
<td>Transfer type</td>
</tr>
<tr>
<td>hwrite</td>
<td>out</td>
<td>Write transfer</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>slave signals </b></td>
</tr>
<tr>
<td>hrdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>hready</td>
<td>in</td>
<td>Transfer finished</td>
</tr>
<tr>
<td>hresp</td>
<td>in</td>
<td>Slave transfer response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Load/Store Unit Master AHB-Lite </b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Master signals </b></td>
</tr>
<tr>
<td>lsu_haddr[31:0]</td>
<td>out</td>
<td>System address</td>
</tr>
<tr>
<td>lsu_hburst[2:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b000)</td>
</tr>
<tr>
<td>lsu_hmastlock</td>
<td>out</td>
<td>Locked transfer (hardwired to 0)</td>
</tr>
<tr>
<td>lsu_hprot[3:0]</td>
<td>out</td>
<td>Protection control</td>
</tr>
<tr>
<td>lsu_hsize[2:0]</td>
<td>out</td>
<td>Transfer size</td>
</tr>
<tr>
<td>lsu_htrans[1:0]</td>
<td>out</td>
<td>Transfer type</td>
</tr>
<tr>
<td>lsu_hwdata[63:0]</td>
<td>out</td>
<td>Write data</td>
</tr>
<tr>
<td>lsu_hwrite</td>
<td>out</td>
<td>Write transfer</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Slave signals  </b></td>
</tr>
<tr>
<td>lsu_hrdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>lsu_hready</td>
<td>in</td>
<td>Transfer finished</td>
</tr>
<tr>
<td>lsu_hresp</td>
<td>in</td>
<td>Slave transfer response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>System Bus (Debug) Master AHB-Lite </b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Master signals</b></td>
</tr>
<tr>
<td>
sb_haddr[31:0]</td>
<td>out</td>
<td>System address</td>
</tr>
<tr>
<td>sb_hburst[2:0]</td>
<td>out</td>
<td>Burst type (hardwired to 0b000)</td>
</tr>
<tr>
<td>sb_hmastlock</td>
<td>out</td>
<td>Locked transfer (hardwired to 0)</td>
</tr>
<tr>
<td>sb_hprot[3:0]</td>
<td>out</td>
<td>Protection control</td>
</tr>
<tr>
<td>sb_hsize[2:0]</td>
<td>out</td>
<td>Transfer size</td>
</tr>
<tr>
<td>sb_htrans[1:0]</td>
<td>out</td>
<td>Transfer type</td>
</tr>
<tr>
<td>sb_hwdata[63:0]</td>
<td>out</td>
<td>Write data</td>
</tr>
<tr>
<td>sb_hwrite</td>
<td>out</td>
<td>Write transfer</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Slave signals </b></td>
</tr>
<tr>
<td>sb_hrdata[63:0]</td>
<td>in</td>
<td>Read data</td>
</tr>
<tr>
<td>sb_hready</td>
<td>in</td>
<td>Transfer finished</td>
</tr>
<tr>
<td>sb_hresp</td>
<td>in</td>
<td>Slave transfer response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>DMA Slave AHB-Lite  </b></td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Slave signals </b></td>
</tr>
<tr>
<td>dma_haddr[31:0]</td>
<td>in</td>
<td>System address</td>
</tr>
<tr>
<td>dma_hburst[2:0]</td>
<td>in</td>
<td>Burst type</td>
</tr>
<tr>
<td>dma_hmastlock</td>
<td>in</td>
<td>Locked transfer</td>
</tr>
<tr>
<td>dma_hprot[3:0]</td>
<td>in</td>
<td>Protection control</td>
</tr>
<tr>
<td>dma_hsize[2:0]</td>
<td>in</td>
<td>Transfer size</td>
</tr>
<tr>
<td>dma_htrans[1:0]</td>
<td>in</td>
<td>Transfer type</td>
</tr>
<tr>
<td>dma_hwdata[63:0]</td>
<td>in</td>
<td>Write data</td>
</tr>
<tr>
<td>dma_hwrite</td>
<td>in</td>
<td>Write transfer</td>
</tr>
<tr>
<td>dma_hsel</td>
<td>in</td>
<td>Slave select</td>
</tr>
<tr>
<td>dma_hreadyin</td>
<td>in</td>
<td>Transfer finished in</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Master signals </b></td>
</tr>
<tr>
<td>dma_hrdata[63:0]</td>
<td>out</td>
<td>Read data</td>
</tr>
<tr>
<td>dma_hreadyout</td>
<td>out</td>
<td>Transfer finished</td>
</tr>
<tr>
<td>dma_hresp</td>
<td>out</td>
<td>Slave transfer response</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Power Management Unit (PMU) Interface</b></td>
</tr>
<tr>
<td>i_cpu_halt_req</td>
<td>in</td>
<td>PMU halt request to core (async)</td>
</tr>
<tr>
<td>o_cpu_halt_ack</td>
<td>out</td>
<td>Core acknowledgement for PMU halt request</td>
</tr>
<tr>
<td>o_cpu_halt_status</td>
<td>out</td>
<td>Core halted indication</td>
</tr>
<tr>
<td>i_cpu_run_req</td>
<td>in</td>
<td>PMU run request to core (async)</td>
</tr>
<tr>
<td>o_cpu_run_ack</td>
<td>out</td>
<td>Core acknowledgement for PMU run request</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Multi-Processor Controller (MPC) Debug Interface</b></td>
</tr>
<tr>
<td>mpc_debug_halt_req</td>
<td>in</td>
<td>MPC debug halt request to core (async)</td>
</tr>
<tr>
<td>mpc_debug_halt_ack</td>
<td>out</td>
<td>Core acknowledgement for MPC debug halt request</td>
</tr>
<tr>
<td>mpc_debug_run_req</td>
<td>in</td>
<td>MPC debug run request to core (async)</td>
</tr>
<tr>
<td>mpc_debug_run_ack</td>
<td>out</td>
<td>Core acknowledgement for MPC debug run request</td>
</tr>
<tr>
<td>mpc_reset_run_req</td>
<td>in</td>
<td>Core start state control out of reset</td>
</tr>
<tr>
<td>o_debug_mode_status</td>
<td>out</td>
<td>Core in Debug Mode indication</td>
</tr>
<tr>
<td>debug_brkpt_status</td>
<td>out</td>
<td>Hardware/software breakpoint indication</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Performance Counter Activity</b></td>
</tr>
<tr>
<td>dec_tlu_perfcnt0</td>
<td>out</td>
<td>Performance counter 0 incrementing</td>
</tr>
<tr>
<td>dec_tlu_perfcnt1</td>
<td>out</td>
<td>Performance counter 1 incrementing</td>
</tr>
<tr>
<td>dec_tlu_perfcnt2</td>
<td>out</td>
<td>Performance counter 2 incrementing</td>
</tr>
<tr>
<td>dec_tlu_perfcnt3</td>
<td>out</td>
<td>Performance counter 3 incrementing</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Trace Port [46]</b></td>
</tr>
<tr>
<td>trace_rv_i_insn_ip[31:0]</td>
<td>out</td>
<td>Instruction opcode</td>
</tr>
<tr>
<td>trace_rv_i_address_ip[31:0]</td>
<td>out</td>
<td>Instruction address</td>
</tr>
<tr>
<td>trace_rv_i_valid_ip</td>
<td>out</td>
<td>Instruction trace valid</td>
</tr>
<tr>
<td>trace_rv_i_exception_ip</td>
<td>out</td>
<td>Exception</td>
</tr>
<tr>
<td>trace_rv_i_ecause_ip[4:0]</td>
<td>out</td>
<td>Exception cause</td>
</tr>
<tr>
<td>trace_rv_i_interrupt_ip</td>
<td>out</td>
<td>Interrupt exception</td>
</tr>
<tr>
<td>trace_rv_i_tval_ip[31:0]</td>
<td>out</td>
<td>Exception trap value</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Debug JTAG Port</b></td>
</tr>
<tr>
<td>jtag_tck</td>
<td>in</td>
<td>JTAG Test Clock (async)</td>
</tr>
<tr>
<td>jtag_tms</td>
<td>in</td>
<td>JTAG Test Mode Select (async, sync to jtag_tck)</td>
</tr>
<tr>
<td>jtag_tdi</td>
<td>in</td>
<td>JTAG Test Data In (async, sync to jtag_tck)</td>
</tr>
<tr>
<td>jtag_trst_n</td>
<td>in</td>
<td>JTAG Test Reset (async)</td>
</tr>
<tr>
<td>jtag_tdo</td>
<td>out</td>
<td>JTAG Test Data Out (async, sync to jtag_tck)</td>
</tr>
<tr>
<td>jtag_id[31:1]</td>
<td>in</td>
<td>JTAG IDCODE register value (bit 0 tied internally to 1)</td>
</tr>
<tr>
<td colspan='3' style="text-align:center;"><b>Testing</b></td>
</tr>
<tr>
<td>scan_mode</td>
<td>in</td>
<td>May be used to enable logic scan test, if implemented (must be ‘0’
for normal core operation)</td>
</tr>
<tr>
<td>mbist_mode</td>
<td>in</td>
<td>May be used to enable MBIST for core-internal memories, if
implemented (should be tied to ‘0’ if not used)</td>
</tr>
</tbody>
</table>


45 The IFU issues only read, but no write transactions.
However, the IFU write address, data, and response channels are present, but the valid/ready signals are tied off to disable those channels.

46 The core provides trace information for a maximum of one instruction and one interrupt/exception per clock cycle.
Note that the only information provided for interrupts/exceptions is the cause, the interrupt/exception flag, and the trap value.
The core’s trace port busses are minimally sized, but wide enough to deliver all trace information the core may produce in one clock cycle.
Not provided signals for the upper bits of the interface related to the interrupt slot might have to be tied off in the SoC.


