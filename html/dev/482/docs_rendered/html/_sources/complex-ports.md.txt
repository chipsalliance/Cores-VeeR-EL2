# Complex Port List

{numref}`tab-core-complex-signals` lists the core complex signals.
Not all signals are present in a given instantiation.
For example, a core complex can only have one bus interface type (AXI4 or AHB-Lite).
Signals which are asynchronous to the core complex clock (`clk`) are marked with "(async)" in the 'Description' column.

:::{list-table} Core Complex Signals
:name: tab-core-complex-signals

* - **Signal**
  - **Dir**
  - **Description**
* - **Clock and Clock Enables**
  -
  -
* - clk
  - in
  - Core complex clock
* - ifu_bus_clk_en
  - in
  - IFU master system bus clock enable
* - lsu_bus_clk_en
  - in
  - LSU master system bus clock enable
* - dbg_bus_clk_en
  - in
  - Debug master system bus clock enable
* - dma_bus_clk_en
  - in
  - DMA slave system bus clock enable
* - **Reset**
  -
  -
* - rst_l
  - in
  - Core complex reset (excl. Debug Module)
* - rst_vec[31:1]
  - in
  - Core reset vector
* - dbg_rst_l
  - in
  - Debug Module reset (incl. JTAG synchronizers)
* - **Interrupts**
  -
  -
* - nmi_int
  - in
  - Non-Maskable Interrupt (async)
* - nmi_vec[31:1]
  - in
  - Non-Maskable Interrupt vector
* - soft_int
  - in
  - Standard RISC-V software interrupt (async)
* - timer_int
  - in
  - Standard RISC-V timer interrupt (async)
* - extintsrc_req[pt.PIC_TOTAL_INT:1]
  - in
  - External interrupts (async)
* - **Core ID**
  -
  -
* - core_id[31:4]
  - in
  - Core ID (mapped to `mhartid[31:4]`)
* - **System Bus Interfaces**
  -
  -
* - ***AXI4***
  -
  -
* - ***Instruction Fetch Unit Master AXI4*** [^fn-complex-ports-1]
  -
  -
* - *Write address channel signals*
  -
  -
* - ifu_axi_awvalid
  - out
  - Write address valid (hardwired to 0)
* - ifu_axi_awready
  - in
  - Write address ready
* - ifu_axi_awid[pt.IFU_BUS_TAG-1:0]
  - out
  - Write address ID
* - ifu_axi_awaddr[31:0]
  - out
  - Write address
* - ifu_axi_awlen[7:0]
  - out
  - Burst length
* - ifu_axi_awsize[2:0]
  - out
  - Burst size
* - ifu_axi_awburst[1:0]
  - out
  - Burst type
* - ifu_axi_awlock
  - out
  - Lock type
* - ifu_axi_awcache[3:0]
  - out
  - Memory type
* - ifu_axi_awprot[2:0]
  - out
  - Protection type
* - ifu_axi_awqos[3:0]
  - out
  - Quality of Service (QoS)
* - ifu_axi_awregion[3:0]
  - out
  - Region identifier
* - *Write data channel signals*
  -
  -
* - ifu_axi_wvalid
  - out
  - Write valid (hardwired to 0)
* - ifu_axi_wready
  - in
  - Write ready
* - ifu_axi_wdata[63:0]
  - out
  - Write data
* - ifu_axi_wstrb[7:0]
  - out
  - Write strobes
* - ifu_axi_wlast
  - out
  - Write last
* - *Write response channel signals*
  -
  -
* - ifu_axi_bvalid
  - in
  - Write response valid
* - ifu_axi_bready
  - out
  - Write response ready (hardwired to 0)
* - ifu_axi_bid[pt.IFU_BUS_TAG-1:0]
  - in
  - Response ID tag
* - ifu_axi_bresp[1:0]
  - in
  - Write response
* - *Read address channel signals*
  -
  -
* - ifu_axi_arvalid
  - out
  - Read address valid
* - ifu_axi_arready
  - in
  - Read address ready
* - ifu_axi_arid[pt.IFU_BUS_TAG-1:0]
  - out
  - Read address ID
* - ifu_axi_araddr[31:0]
  - out
  - Read address
* - ifu_axi_arlen[7:0]
  - out
  - Burst length (hardwired to 0b0000_0000)
* - ifu_axi_arsize[2:0]
  - out
  - Burst size (hardwired to 0b011)
* - ifu_axi_arburst[1:0]
  - out
  - Burst type (hardwired to 0b01)
* - ifu_axi_arlock
  - out
  - Lock type (hardwired to 0)
* - ifu_axi_arcache[3:0]
  - out
  - Memory type (hardwired to 0b1111)
* - ifu_axi_arprot[2:0]
  - out
  - Protection type (hardwired to 0b100)
* - ifu_axi_arqos[3:0]
  - out
  - Quality of Service (QoS) (hardwired to 0b0000)
* - ifu_axi_arregion[3:0]
  - out
  - Region identifier
* - *Read data channel signals*
  -
  -
* - ifu_axi_rvalid
  - in
  - Read valid
* - ifu_axi_rready
  - out
  - Read ready
* - ifu_axi_rid[pt.IFU_BUS_TAG-1:0]
  - in
  - Read ID tag
* - ifu_axi_rdata[63:0]
  - in
  - Read data
* - ifu_axi_rresp[1:0]
  - in
  - Read response
* - ifu_axi_rlast
  - in
  - Read last
* - ***Load/Store Unit Master AXI4***
  -
  -
* - *Write address channel signals*
  -
  -
* - lsu_axi_awvalid
  - out
  - Write address valid
* - lsu_axi_awready
  - in
  - Write address ready
* - lsu_axi_awid[pt.LSU_BUS_TAG-1:0]
  - out
  - Write address ID
* - lsu_axi_awaddr[31:0]
  - out
  - Write address
* - lsu_axi_awlen[7:0]
  - out
  - Burst length (hardwired to 0b0000_0000)
* - lsu_axi_awsize[2:0]
  - out
  - Burst size
* - lsu_axi_awburst[1:0]
  - out
  - Burst type (hardwired to 0b01)
* - lsu_axi_awlock
  - out
  - Lock type (hardwired to 0)
* - lsu_axi_awcache[3:0]
  - out
  - Memory type
* - lsu_axi_awprot[2:0]
  - out
  - Protection type (hardwired to 0b000)
* - lsu_axi_awqos[3:0]
  - out
  - Quality of Service (QoS) (hardwired to 0b0000)
* - lsu_axi_awregion[3:0]
  - out
  - Region identifier
* - *Write data channel signals*
  -
  -
* - lsu_axi_wvalid
  - out
  - Write valid
* - lsu_axi_wready
  - in
  - Write ready
* - lsu_axi_wdata[63:0]
  - out
  - Write data
* - lsu_axi_wstrb[7:0]
  - out
  - Write strobes
* - lsu_axi_wlast
  - out
  - Write last
* - *Write response channel signals*
  -
  -
* - lsu_axi_bvalid
  - in
  - Write response valid
* - lsu_axi_bready
  - out
  - Write response ready
* - lsu_axi_bid[pt.LSU_BUS_TAG-1:0]
  - in
  - Response ID tag
* - lsu_axi_bresp[1:0]
  - in
  - Write response
* - *Read address channel signals*
  -
  -
* - lsu_axi_arvalid
  - out
  - Read address valid
* - lsu_axi_arready
  - in
  - Read address ready
* - lsu_axi_arid[pt.LSU_BUS_TAG-1:0]
  - out
  - Read address ID
* - lsu_axi_araddr[31:0]
  - out
  - Read address
* - lsu_axi_arlen[7:0]
  - out
  - Burst length (hardwired to 0b0000_0000)
* - lsu_axi_arsize[2:0]
  - out
  - Burst size
* - lsu_axi_arburst[1:0]
  - out
  - Burst type (hardwired to 0b01)
* - lsu_axi_arlock
  - out
  - Lock type (hardwired to 0)
* - lsu_axi_arcache[3:0]
  - out
  - Memory type
* - lsu_axi_arprot[2:0]
  - out
  - Protection type (hardwired to 0b000)
* - lsu_axi_arqos[3:0]
  - out
  - Quality of Service (QoS) (hardwired to 0b0000)
* - lsu_axi_arregion[3:0]
  - out
  - Region identifier
* - *Read data channel signals*
  -
  -
* - lsu_axi_rvalid
  - in
  - Read valid
* - lsu_axi_rready
  - out
  - Read ready
* - lsu_axi_rid[pt.LSU_BUS_TAG-1:0]
  - in
  - Read ID tag
* - lsu_axi_rdata[63:0]
  - in
  - Read data
* - lsu_axi_rresp[1:0]
  - in
  - Read response
* - lsu_axi_rlast
  - in
  - Read last
* - ***System Bus (Debug) Master AXI4***
  -
  -
* - *Write address channel signals*
  -
  -
* - sb_axi_awvalid
  - out
  - Write address valid
* - sb_axi_awready
  - in
  - Write address ready
* - sb_axi_awid[pt.SB_BUS_TAG-1:0]
  - out
  - Write address ID (hardwired to 0)
* - sb_axi_awaddr[31:0]
  - out
  - Write address
* - sb_axi_awlen[7:0]
  - out
  - Burst length (hardwired to 0b0000_0000)
* - sb_axi_awsize[2:0]
  - out
  - Burst size
* - sb_axi_awburst[1:0]
  - out
  - Burst type (hardwired to 0b01)
* - sb_axi_awlock
  - out
  - Lock type (hardwired to 0)
* - sb_axi_awcache[3:0]
  - out
  - Memory type (hardwired to 0b1111)
* - sb_axi_awprot[2:0]
  - out
  - Protection type (hardwired to 0b000)
* - sb_axi_awqos[3:0]
  - out
  - Quality of Service (QoS) (hardwired to 0b0000)
* - sb_axi_awregion[3:0]
  - out
  - Region identifier
* - *Write data channel signals*
  -
  -
* - sb_axi_wvalid
  - out
  - Write valid
* - sb_axi_wready
  - in
  - Write ready
* - sb_axi_wdata[63:0]
  - out
  - Write data
* - sb_axi_wstrb[7:0]
  - out
  - Write strobes
* - sb_axi_wlast
  - out
  - Write last
* - *Write response channel signals*
  -
  -
* - sb_axi_bvalid
  - in
  - Write response valid
* - sb_axi_bready
  - out
  - Write response ready
* - sb_axi_bid[pt.SB_BUS_TAG-1:0]
  - in
  - Response ID tag
* - sb_axi_bresp[1:0]
  - in
  - Write response
* - *Read address channel signals*
  -
  -
* - sb_axi_arvalid
  - out
  - Read address valid
* - sb_axi_arready
  - in
  - Read address ready
* - sb_axi_arid[pt.SB_BUS_TAG-1:0]
  - out
  - Read address ID (hardwired to 0)
* - sb_axi_araddr[31:0]
  - out
  - Read address
* - sb_axi_arlen[7:0]
  - out
  - Burst length (hardwired to 0b0000_0000)
* - sb_axi_arsize[2:0]
  - out
  - Burst size
* - sb_axi_arburst[1:0]
  - out
  - Burst type (hardwired to 0b01)
* - sb_axi_arlock
  - out
  - Lock type (hardwired to 0)
* - sb_axi_arcache[3:0]
  - out
  - Memory type (hardwired to 0b0000)
* - sb_axi_arprot[2:0]
  - out
  - Protection type (hardwired to 0b000)
* - sb_axi_arqos[3:0]
  - out
  - Quality of Service (QoS) (hardwired to 0b0000)
* - sb_axi_arregion[3:0]
  - out
  - Region identifier
* - *Read data channel signals*
  -
  -
* - sb_axi_rvalid
  - in
  - Read valid
* - sb_axi_rready
  - out
  - Read ready
* - sb_axi_rid[pt.SB_BUS_TAG-1:0]
  - in
  - Read ID tag
* - sb_axi_rdata[63:0]
  - in
  - Read data
* - sb_axi_rresp[1:0]
  - in
  - Read response
* - sb_axi_rlast
  - in
  - Read last
* - ***DMA Slave AXI4***
  -
  -
* - *Write address channel signals*
  -
  -
* - dma_axi_awvalid
  - in
  - Write address valid
* - dma_axi_awready
  - out
  - Write address ready
* - dma_axi_awid[pt.DMA_BUS_TAG-1:0]
  - in
  - Write address ID
* - dma_axi_awaddr[31:0]
  - in
  - Write address
* - dma_axi_awlen[7:0]
  - in
  - Burst length
* - dma_axi_awsize[2:0]
  - in
  - Burst size
* - dma_axi_awburst[1:0]
  - in
  - Burst type
* - dma_axi_awprot[2:0]
  - in
  - Protection type
* - *Write data channel signals*
  -
  -
* - dma_axi_wvalid
  - in
  - Write valid
* - dma_axi_wready
  - out
  - Write ready
* - dma_axi_wdata[63:0]
  - in
  - Write data
* - dma_axi_wstrb[7:0]
  - in
  - Write strobes
* - dma_axi_wlast
  - in
  - Write last
* - *Write response channel signals*
  -
  -
* - dma_axi_bvalid
  - out
  - Write response valid
* - dma_axi_bready
  - in
  - Write response ready
* - dma_axi_bid[pt.DMA_BUS_TAG-1:0]
  - out
  - Response ID tag
* - dma_axi_bresp[1:0]
  - out
  - Write response
* - *Read address channel signals*
  -
  -
* - dma_axi_arvalid
  - in
  - Read address valid
* - dma_axi_arready
  - out
  - Read address ready
* - dma_axi_arid[pt.DMA_BUS_TAG-1:0]
  - in
  - Read address ID
* - dma_axi_araddr[31:0]
  - in
  - Read address
* - dma_axi_arlen[7:0]
  - in
  - Burst length
* - dma_axi_arsize[2:0]
  - in
  - Burst size
* - dma_axi_arburst[1:0]
  - in
  - Burst type
* - dma_axi_arprot[2:0]
  - in
  - Protection type
* - *Read data channel signals*
  -
  -
* - dma_axi_rvalid
  - out
  - Read valid
* - dma_axi_rready
  - in
  - Read ready
* - dma_axi_rid[pt.DMA_BUS_TAG-1:0]
  - out
  - Read ID tag
* - dma_axi_rdata[63:0]
  - out
  - Read data
* - dma_axi_rresp[1:0]
  - out
  - Read response
* - dma_axi_rlast
  - out
  - Read last
* - ***AHB-Lite***
  -
  -
* - ***Instruction Fetch Unit Master AHB-Lite***
  -
  -
* - *Master signals*
  -
  -
* - haddr[31:0]
  - out
  - System address
* - hburst[2:0]
  - out
  - Burst type (hardwired to 0b000)
* - hmastlock
  - out
  - Locked transfer (hardwired to 0)
* - hprot[3:0]
  - out
  - Protection control
* - hsize[2:0]
  - out
  - Transfer size
* - htrans[1:0]
  - out
  - Transfer type
* - hwrite
  - out
  - Write transfer
* - *Slave signals*
  -
  -
* - hrdata[63:0]
  - in
  - Read data
* - hready
  - in
  - Transfer finished
* - hresp
  - in
  - Slave transfer response
* - ***Load/Store Unit Master AHB-Lite***
  -
  -
* - *Master signals*
  -
  -
* - lsu_haddr[31:0]
  - out
  - System address
* - lsu_hburst[2:0]
  - out
  - Burst type (hardwired to 0b000)
* - lsu_hmastlock
  - out
  - Locked transfer (hardwired to 0)
* - lsu_hprot[3:0]
  - out
  - Protection control
* - lsu_hsize[2:0]
  - out
  - Transfer size
* - lsu_htrans[1:0]
  - out
  - Transfer type
* - lsu_hwdata[63:0]
  - out
  - Write data
* - lsu_hwrite
  - out
  - Write transfer
* - *Slave signals*
  -
  -
* - lsu_hrdata[63:0]
  - in
  - Read data
* - lsu_hready
  - in
  - Transfer finished
* - lsu_hresp
  - in
  - Slave transfer response
* - ***System Bus (Debug) Master AHB-Lite***
  -
  -
* - *Master signals*
  -
  -
* - sb_haddr[31:0]
  - out
  - System address
* - sb_hburst[2:0]
  - out
  - Burst type (hardwired to 0b000)
* - sb_hmastlock
  - out
  - Locked transfer (hardwired to 0)
* - sb_hprot[3:0]
  - out
  - Protection control
* - sb_hsize[2:0]
  - out
  - Transfer size
* - sb_htrans[1:0]
  - out
  - Transfer type
* - sb_hwdata[63:0]
  - out
  - Write data
* - sb_hwrite
  - out
  - Write transfer
* - *Slave signals*
  -
  -
* - sb_hrdata[63:0]
  - in
  - Read data
* - sb_hready
  - in
  - Transfer finished
* - sb_hresp
  - in
  - Slave transfer response
* - ***DMA Slave AHB-Lite***
  -
  -
* - *Slave signals*
  -
  -
* - dma_haddr[31:0]
  - in
  - System address
* - dma_hburst[2:0]
  - in
  - Burst type
* - dma_hmastlock
  - in
  - Locked transfer
* - dma_hprot[3:0]
  - in
  - Protection control
* - dma_hsize[2:0]
  - in
  - Transfer size
* - dma_htrans[1:0]
  - in
  - Transfer type
* - dma_hwdata[63:0]
  - in
  - Write data
* - dma_hwrite
  - in
  - Write transfer
* - dma_hsel
  - in
  - Slave select
* - dma_hreadyin
  - in
  - Transfer finished in
* - *Master signals*
  -
  -
* - dma_hrdata[63:0]
  - out
  - Read data
* - dma_hreadyout
  - out
  - Transfer finished
* - dma_hresp
  - out
  - Slave transfer response
* - **Power Management Unit (PMU) Interface**
  -
  -
* - i_cpu_halt_req
  - in
  - PMU halt request to core (async)
* - o_cpu_halt_ack
  - out
  - Core acknowledgement for PMU halt request
* - o_cpu_halt_status
  - out
  - Core halted indication
* - i_cpu_run_req
  - in
  - PMU run request to core (async)
* - o_cpu_run_ack
  - out
  - Core acknowledgement for PMU run request
* - **Multi-Processor Controller (MPC) Debug Interface**
  -
  -
* - mpc_debug_halt_req
  - in
  - MPC debug halt request to core (async)
* - mpc_debug_halt_ack
  - out
  - Core acknowledgement for MPC debug halt request
* - mpc_debug_run_req
  - in
  - MPC debug run request to core (async)
* - mpc_debug_run_ack
  - out
  - Core acknowledgement for MPC debug run request
* - mpc_reset_run_req
  - in
  - Core start state control out of reset
* - o_debug_mode_status
  - out
  - Core in Debug Mode indication
* - debug_brkpt_status
  - out
  - Hardware/software breakpoint indication
* - **Performance Counter Activity**
  -
  -
* - dec_tlu_perfcnt0
  - out
  - Performance counter 0 incrementing
* - dec_tlu_perfcnt1
  - out
  - Performance counter 1 incrementing
* - dec_tlu_perfcnt2
  - out
  - Performance counter 2 incrementing
* - dec_tlu_perfcnt3
  - out
  - Performance counter 3 incrementing
* - **Trace Port** [^fn-complex-ports-2]
  -
  -
* - trace_rv_i_insn_ip[31:0]
  - out
  - Instruction opcode
* - trace_rv_i_address_ip[31:0]
  - out
  - Instruction address
* - trace_rv_i_valid_ip
  - out
  - Instruction trace valid
* - trace_rv_i_exception_ip
  - out
  - Exception
* - trace_rv_i_ecause_ip[4:0]
  - out
  - Exception cause
* - trace_rv_i_interrupt_ip
  - out
  - Interrupt exception
* - trace_rv_i_tval_ip[31:0]
  - out
  - Exception trap value
* - **Debug JTAG Port**
  -
  -
* - jtag_tck
  - in
  - JTAG Test Clock (async)
* - jtag_tms
  - in
  - JTAG Test Mode Select (async, sync to jtag_tck)
* - jtag_tdi
  - in
  - JTAG Test Data In (async, sync to jtag_tck)
* - jtag_trst_n
  - in
  - JTAG Test Reset (async)
* - jtag_tdo
  - out
  - JTAG Test Data Out (async, sync to jtag_tck)
* - jtag_id[31:1]
  - in
  - JTAG IDCODE register value (bit 0 tied internally to 1)
* - **Testing**
  -
  -
* - scan_mode
  - in
  - May be used to enable logic scan test, if implemented (must be ‘0’ for normal core operation)
* - mbist_mode
  - in
  - May be used to enable MBIST for core-internal memories, if implemented (should be tied to ‘0’ if not used)
:::

[^fn-complex-ports-1]: The IFU issues only read, but no write transactions.
However, the IFU write address, data, and response channels are present, but the valid/ready signals are tied off to disable those channels.

[^fn-complex-ports-2]: The core provides trace information for a maximum of one instruction and one interrupt/exception per clock cycle.
Note that the only information provided for interrupts/exceptions is the cause, the interrupt/exception flag, and the trap value.
The core’s trace port busses are minimally sized, but wide enough to deliver all trace information the core may produce in one clock cycle.
Not provided signals for the upper bits of the interface related to the interrupt slot might have to be tied off in the SoC.
