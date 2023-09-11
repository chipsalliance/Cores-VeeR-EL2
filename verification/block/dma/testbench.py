# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
import random
import math

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge, Timer
from pyuvm import *

# ==============================================================================


class BusWriteItem(uvm_sequence_item):
    """
    A generic data bus write request / response
    """

    def __init__(self, addr, data, resp=None):
        super().__init__("BusWriteItem")
        self.addr = addr
        self.data = data
        self.resp = resp


class BusReadItem(uvm_sequence_item):
    """
    A generic data bus read request / response
    """

    def __init__(self, addr, data=None, resp=None):
        super().__init__("BusReadItem")
        self.addr = addr
        self.data = data
        self.resp = resp


class MemWriteItem(uvm_sequence_item):
    """
    A generic memory bus write item
    """

    def __init__(self, mem, addr, data):
        super().__init__("MemWriteItem")
        self.mem  = mem
        self.addr = addr
        self.data = data


class MemReadItem(uvm_sequence_item):
    """
    A generic memory bus read item
    """

    def __init__(self, mem, addr, data):
        super().__init__("MemReadItem")
        self.mem  = mem
        self.addr = addr
        self.data = data

# ==============================================================================


def collect_signals(signals, uut, obj, uut_prefix="", obj_prefix=""):
    """
    Collects signal objects from UUT and attaches them to the given object.
    Optionally UUT signals can be prefixed with the uut_prefix and object
    signals with the obj_prefix
    """

    for sig in signals:
        uut_sig = uut_prefix + sig
        obj_sig = obj_prefix + sig
        if hasattr(uut, uut_sig):
            s = getattr(uut, uut_sig)

        else:
            s = None
            logging.error(
                "Module {} does not have a signal '{}'".format(str(uut), sig)
            )

        setattr(obj, obj_sig, s)

# ==============================================================================


class CoreMemoryBFM(uvm_component):
    """
    A BFM for the memory side interface of the DMA module
    """

    SIGNALS = [
        "clk",

        "dma_dccm_req",
        "dma_iccm_req",
        "dma_mem_tag",
        "dma_mem_addr",
        "dma_mem_sz",
        "dma_mem_write",
        "dma_mem_wdata",

        "dccm_dma_rvalid",
        "dccm_dma_ecc_error",
        "dccm_dma_rtag",
        "dccm_dma_rdata",
        "iccm_dma_rvalid",
        "iccm_dma_ecc_error",
        "iccm_dma_rtag",
        "iccm_dma_rdata",

        "dccm_ready",
        "iccm_ready",
    ]

    def __init__(self, name, parent, uut):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

        # Get base addresses and sizes
        self.iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        self.dccm_base = ConfigDB().get(None, "", "DCCM_BASE")

        self.iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")
        self.dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        # Memory content
        self.iccm_data = dict()
        self.dccm_data = dict()

    async def run_phase(self):

        while True:
            await RisingEdge(self.clk)

            # Become busy at random for a random cycle count
            if random.random() < 0.25:
                self.iccm_ready.value = 0
                self.dccm_ready.value = 0

                n = random.randrange(10, 20)
                await ClockCycles(self.clk, n)

                self.iccm_ready.value = 1
                self.dccm_ready.value = 1

            # Sample signals
            tag = int(self.dma_mem_tag)

            # DCCM access
            if self.dma_dccm_req.value:

                # Decode and check address
                addr = int(self.dma_mem_addr.value) - self.dccm_base
                assert addr >= 0 and addr < self.dccm_size

                # Write / read
                if self.dma_mem_write.value:
                    self.dccm_data[addr] = int(self.dma_mem_wdata.value)
                    self.dccm_dma_rvalid.value = 0

                else:
                    self.dccm_dma_rdata = self.dccm_data.get(addr, 0)
                    self.dccm_dma_rtag.value = tag
                    self.dccm_dma_rvalid.value = 1
                    self.dccm_dma_ecc_error.value = 0
            
                await RisingEdge(self.clk)

            # ICCM access
            elif self.dma_iccm_req.value:

                # Decode and check address
                addr = int(self.dma_mem_addr.value) - self.iccm_base
                assert addr >= 0 and addr < self.iccm_size

                # Write / read
                if self.dma_mem_write.value:
                    self.iccm_data[addr] = int(self.dma_mem_wdata.value)
                    self.iccm_dma_rvalid.value = 0

                else:
                    self.iccm_dma_rdata = self.iccm_data.get(addr, 0)
                    self.iccm_dma_rtag.value = tag
                    self.iccm_dma_rvalid.value = 1
                    self.iccm_dma_ecc_error.value = 0

                await RisingEdge(self.clk)


class CoreMemoryMonitor(uvm_component):
    """
    A monitor for ICCM / DCCM interface
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

        # Get base addresses
        self.iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        self.dccm_base = ConfigDB().get(None, "", "DCCM_BASE")

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):

        while True:
            await RisingEdge(self.bfm.clk)

            # DCCM access
            if self.bfm.dma_dccm_req.value and \
               self.bfm.dccm_ready.value:

                if self.bfm.dma_mem_write.value:
                    addr = int(self.bfm.dma_mem_addr.value) - self.dccm_base
                    data = int(self.bfm.dma_mem_wdata.value)
                    self.ap.write(MemWriteItem("DCCM", addr, data))

                    self.logger.debug("DCCM WR: 0x{:08X} 0x{:016X}".format(
                        addr,
                        data))

            # ICCM access
            if self.bfm.dma_iccm_req.value and \
               self.bfm.iccm_ready.value:

                if self.bfm.dma_mem_write.value:
                    addr = int(self.bfm.dma_mem_addr.value) - self.iccm_base
                    data = int(self.bfm.dma_mem_wdata.value)
                    self.ap.write(MemWriteItem("ICCM", addr, data))

                    self.logger.debug("ICCM WR: 0x{:08X} 0x{:016X}".format(
                        addr,
                        data))

            # TODO: Support read accesses

# ==============================================================================

class Axi4LiteBFM(uvm_component):
    """
    A bus functional model for AXI4 Lite subordinate port.

    Does support multi-transfer transactions, does not support overlapped
    transfers.
    """

    SIGNALS = [
        "awvalid",
        "awready",
        "awid",
        "awaddr",
        "awsize",

        "wvalid",
        "wready",
        "wdata",
        "wstrb",

        "bvalid",
        "bready",
        "bresp",
        "bid",

        "arvalid",
        "arready",
        "arid",
        "araddr",
        "arsize",

        "rvalid",
        "rready",
        "rid",
        "rdata",
        "rresp",
        "rlast",
    ]

    def __init__(self, name, parent, uut):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self,
                        uut_prefix="dma_axi_",
                        obj_prefix="axi_")

        collect_signals(["clk", "rst_l"], uut, self)

        # Determine bus parameters
        self.awidth = len(self.axi_awaddr)
        self.dwidth = len(self.axi_wdata)
        self.swidth = len(self.axi_wstrb)

        assert self.swidth == (self.dwidth // 8)

        self.logger.debug("AXI4 Lite BFM:")
        self.logger.debug(" awidth = {}".format(self.awidth))
        self.logger.debug(" dwidth = {}".format(self.dwidth))
        self.logger.debug(" swidth = {}".format(self.swidth))

    @staticmethod
    def collect_bytes(data, strb=None):
        """
        Collects data bytes asserted on a data bus. Uses the strb value to
        determine which octets are valid.
        """

        if strb is not None:
            assert len(data) == 8 * len(strb)

        res = []
        for i in range(len(data) // 8):
            if strb is None or strb.value & (1 << i):
                dat = (int(data.value) >> (8 * i)) & 0xFF
                res.append(dat)

        return bytes(res)

    async def _wait(self, signal, max_cycles=50):
        """
        Waits for a signal to be asserted for at most max_cycles.
        Raises an exception if it does not
        """
        for i in range(max_cycles):
            await RisingEdge(self.clk)
            if signal.value != 0:
                break
        else:
            raise RuntimeError("{} timeout".format(str(signal)))

    async def write(self, addr, data):
        """
        Issues a write transfer and wait for its completion
        """

        # Send write request
        await self._wait(self.axi_awready)
        self.axi_awvalid.value  = 1
        self.axi_awaddr.value   = addr
        self.axi_awid.value     = 1
        self.axi_awsize.value   = int(math.ceil(math.log2(self.dwidth)))

        await RisingEdge(self.clk)
        self.axi_awvalid.value  = 0

        # Send data
        data_len = len(data)
        data_ptr = 0
        while data_len > 0:

            # Wait for ready
            await self._wait(self.axi_wready)
            self.axi_wvalid.value   = 1

            # Get data
            xfer_len  = min(self.swidth, data_len)
            xfer_data = data[data_ptr:data_ptr + xfer_len]
            data_ptr += xfer_len
            data_len -= xfer_len

            # Assert data
            wdata = 0
            wstrb = 0
            for i in range(xfer_len):
                wdata <<= 8
                wstrb <<= 1

                wdata |= xfer_data[-(1+i)]
                wstrb |= 1

            self.axi_wdata.value = wdata
            self.axi_wstrb.value = wstrb

        # Wait for the last ready
        await self._wait(self.axi_wready)

        # Deassert wvalid
        self.axi_wvalid.value = 0

        # Wait for response
        self.axi_bready.value = 1
        await self._wait(self.axi_bvalid)

        bresp = int(self.axi_bresp.value)
        bid   = int(self.axi_bid.value)
        self.axi_bready.value = 0

        self.logger.debug("WR: 0x{:08X} {} 0b{:03b}".format(
            addr,
            ["0x{:02X}".format(b) for b in data],
            bresp
        ))

        return bresp

    async def read(self, addr, data):
        """
        Issues a read transfer
        """

        # Send read request
        await self._wait(self.axi_awready)
        self.axi_arvalid.value  = 1
        self.axi_araddr.value   = addr
        self.axi_arid.value     = 1
        self.axi_arsize.value   = int(math.ceil(math.log2(self.dwidth)))

        await RisingEdge(self.clk)
        self.axi_arvalid.value  = 0

        # Receive data
        self.axi_rready.value = 1

        data  = bytearray()
        rresp = None

        while True:

            # Wait for valid
            await self._wait(self.axi_rvalid)

            # Get the data
            data.extend(self.collect_bytes(self.axi_rdata))

            # Last, finish reception
            if self.axi_rlast.value:
                break

        self.axi_rready.value = 0
        rresp = int(self.axi_rresp.value)

        self.logger.debug("RD: 0x{:08X} {} 0b{:03b}".format(
            addr,
            ["0x{:02X}".format(b) for b in data],
            rresp
        ))

        return bytes(data), rresp

# ==============================================================================


class Axi4LiteSubordinateDriver(uvm_driver):
    """
    A driver component for AXI4 lite subordinate ports. Acts as an AXI Manager.
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                it.resp = await self.bfm.write(it.addr, it.data)

            elif isinstance(it, BusReadItem):
                # FIXME: Assuming that all read requests are 64-bit wide
                data, resp = await self.bfm.read(it.addr, 8)
                it.resp = resp

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class Axi4LiteMonitor(uvm_component):
    """
    A monitor for AXI4 lite bus
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    def _aw_active(self):
        return self.bfm.axi_awready.value != 0 and \
               self.bfm.axi_awvalid.value != 0

    def _w_active(self):
        return self.bfm.axi_wready.value  != 0 and \
               self.bfm.axi_wvalid.value  != 0

    def _ar_active(self):
        return self.bfm.axi_arready.value != 0 and \
               self.bfm.axi_arvalid.value != 0

    def _r_active(self):
        return self.bfm.axi_rready.value  != 0 and \
               self.bfm.axi_rvalid.value  != 0

    def _b_active(self):
        return self.bfm.axi_bready.value  != 0 and \
               self.bfm.axi_bvalid.value  != 0

    def _sample_w(self):
        return self.bfm.collect_bytes(
            self.bfm.axi_wdata,
            self.bfm.axi_wstrb,
        )

    def _sample_r(self):
        return self.bfm.collect_bytes(
            self.bfm.axi_rdata,
        )

    async def watch_write(self):
        """
        Watches the bus for writes
        """
        state = "idle"
        addr  = None
        data  = None
        bresp = None

        # Main loop
        while True:

            # Wait for clock
            await RisingEdge(self.bfm.clk)

            if state == "idle":
                if self._aw_active():
                    state = "wr_addr"
                    addr  = int(self.bfm.axi_awaddr.value)

            elif state == "wr_addr":
                assert not self._aw_active()
                assert not self._b_active()

                if self._w_active():
                    state = "wr_data"
                    data  = bytearray()
                    data.extend(self._sample_w())

            elif state == "wr_data":
                assert not self._aw_active()

                if self._w_active():
                    data.extend(self._sample_w())

                if self._b_active():
                    state = "wr_resp"
                    bresp = int(self.bfm.axi_rresp.value)

            elif state == "wr_resp":
                assert not self._aw_active()
                assert not self._w_active()

                state = "idle"
                self.ap.write(BusWriteItem(addr, bytes(data), bresp))

                self.logger.debug("WR: 0x{:08X} {} 0b{:03b}".format(
                    addr,
                    ["0x{:02X}".format(b) for b in data],
                    bresp
                ))

    async def watch_read(self):
        """
        Watches the bus for reads
        """

        state = "idle"
        addr  = None
        data  = None
        resp  = None

        def check_last():
            if self.bfm.axi_rlast.value:
                state = "idle"
                rresp = int(self.bfm.axi_rresp.value)

                self.ap.write(BusReadItem(addr, bytes(data), rresp))

                self.logger.debug("RD: 0x{:08X} {} 0b{:03b}".format(
                    addr,
                    ["0x{:02X}".format(b) for b in data],
                    rresp
                ))

        # Main loop
        while True:

            # Wait for clock
            await RisingEdge(self.bfm.clk)

            if state == "idle":
                if self._ar_active():
                    state = "rd_addr"
                    addr  = int(self.bfm.axi_araddr.value)

            elif state == "rd_addr":
                assert not self._ar_active()
                assert not self._b_active()

                if self._r_active():
                    state = "rd_data"
                    data  = bytearray()
                    data.extend(self._sample_r())
                    check_last()

            elif state == "rd_data":
                assert not self._ar_active()
                assert not self._b_active()

                if self._r_active():
                    data.extend(self._sample_r())
                    check_last()

    async def run_phase(self):

        # Start read & write watchers
        cocotb.start_soon(self.watch_write())
        cocotb.start_soon(self.watch_read())

# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):

        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 50)

        # ICCM and DCCM addresses / sizes are taken from the default VeeR
        # config.
        ConfigDB().set(None, "*", "ICCM_BASE",       0xEE000000)
        ConfigDB().set(None, "*", "DCCM_BASE",       0xF0040000)

        ConfigDB().set(None, "*", "ICCM_SIZE",       0x10000)
        ConfigDB().set(None, "*", "DCCM_SIZE",       0x10000)

        # Sequencers
        self.axi_seqr = uvm_sequencer("axi_seqr", self)

        # AXI interface
        self.axi_bfm = Axi4LiteBFM("axi_bfm", self, cocotb.top)
        self.axi_drv = Axi4LiteSubordinateDriver("axi_drv", self, bfm=self.axi_bfm)
        self.axi_mon = Axi4LiteMonitor("axi_mon", self, bfm=self.axi_bfm)

        # Core side memory port
        self.mem_bfm = CoreMemoryBFM("mem_bfm", self, cocotb.top)
        self.mem_mon = CoreMemoryMonitor("mem_mon", self, bfm=self.mem_bfm)

    def connect_phase(self):
        self.axi_drv.seq_item_port.connect(self.axi_seqr.seq_item_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Syncrhonize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self):
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("free_clk")

        # Enable clock
        cocotb.top.dma_bus_clk_en.value = 1

        # Issue reset
        await self.do_reset()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
