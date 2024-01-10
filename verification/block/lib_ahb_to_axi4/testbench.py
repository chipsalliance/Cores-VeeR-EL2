# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
import random
import sys
from enum import Enum

import pyuvm
from axi import Axi4LiteMonitor, BusReadItem, BusWriteItem
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Combine, FallingEdge, RisingEdge
from pyuvm import *
from utils import collect_bytes, collect_signals

# ==============================================================================


class AXI4LiteReadyItem(uvm_sequence_item):
    """
    An item describing ready signal assertion / deassertion for an AXI4 lite
    channel(s)
    """

    def __init__(self, channels, ready=True):
        super().__init__("AXI4LiteReadyItem")
        self.channels = channels
        self.ready = ready


class AXI4LiteResponseItem(uvm_sequence_item):
    """
    An item describing a response for an AXI4 lite channel(s)
    """

    def __init__(self, channels):
        super().__init__("AXI4LiteResponseItem")
        self.channels = channels


# ==============================================================================


class AHBLiteManagerBFM(uvm_component):
    """
    AHB Lite bus BFM that operates as a manager.
    """

    SIGNALS = [
        "hclk",
        "hreset",
        "haddr",
        "hburst",
        "hmastlock",
        "hprot",
        "hsize",
        "htrans",
        "hwrite",
        "hwdata",
        "hsel",
        "hrdata",
        "hreadyout",
        "hresp",
    ]

    class HTRANS(Enum):
        IDLE = 0b00
        BUSY = 0b01
        NONSEQ = 0b10
        SEQ = 0b11

    class HBURST(Enum):
        SINGLE = 0b000
        INCR = 0b001
        WRAP4 = 0b010
        INCR4 = 0b011
        WRAP8 = 0b100
        INCR8 = 0b101
        WRAP16 = 0b110
        INCR16 = 0b111

    def __init__(self, name, parent, uut, signal_prefix="", signal_map=None):
        super().__init__(name, parent)

        collect_signals(
            self.SIGNALS,
            uut,
            self,
            uut_prefix=signal_prefix,
            obj_prefix="ahb_",
            signal_map=signal_map,
        )

        # Determine bus parameters
        self.awidth = len(self.ahb_haddr)
        self.dwidth = len(self.ahb_hwdata)  # Assuming hrdata is the same

        # Calculate HSIZE encoding
        self.hsize = {
            64 // self.dwidth: 3,
            128 // self.dwidth: 4,
            256 // self.dwidth: 5,
            512 // self.dwidth: 6,
            1024 // self.dwidth: 7,
        }

        self.logger.debug("AHB Lite manager BFM:")
        self.logger.debug(" awidth = {}".format(self.awidth))
        self.logger.debug(" dwidth = {}".format(self.dwidth))

    async def _wait(self, signal, max_cycles=200):
        """
        Waits for a signal to be asserted for at most max_cycles.
        Raises an exception if it does not
        """

        for i in range(max_cycles):
            await RisingEdge(self.ahb_hclk)
            if signal.value == 1:
                break
        else:
            raise TimeoutError("{} timeout".format(str(signal)))

    async def write(self, addr, data):
        """
        Issues a write transfer. Parameter data must be a list of integers
        where each one represents a full bus data word. The word count must be
        one of multiplies of data bus width supported by AHB Lite.
        """

        lnt = len(data)
        assert lnt in self.hsize

        # Wait for reset deassertion if necessary
        if self.ahb_hreset.value == 0:
            await RisingEdge(self.ahb_hreset)

        # Address phase
        await RisingEdge(self.ahb_hclk)
        self.ahb_hsel.value = 1
        self.ahb_hprot.value = 1  # Indicates a data transfer
        self.ahb_hsize.value = self.hsize[lnt]
        self.ahb_haddr.value = addr
        self.ahb_hwrite.value = 1
        self.ahb_htrans.value = self.HTRANS.NONSEQ.value
        self.ahb_hburst.value = self.HBURST.SINGLE.value
        await self._wait(self.ahb_hreadyout)

        # Data phase
        for i, word in enumerate(data):
            if i != lnt - 1:
                addr += self.dwidth // 8
                self.ahb_haddr.value = addr
                self.ahb_htrans.value = self.HTRANS.SEQ.value
            else:
                self.ahb_htrans.value = self.HTRANS.IDLE.value

            self.ahb_hwdata.value = word
            await self._wait(self.ahb_hreadyout)

    async def read(self, addr, length):
        """
        Issues an AHB read transfer for the given number of bus data words. The
        word count must be one of multiplies of data bus width supported by AHB
        Lite.
        """

        assert length in self.hsize

        # Wait for reset deassertion if necessary
        if self.ahb_hreset.value == 0:
            await RisingEdge(self.ahb_hreset)

        # Address phase
        await RisingEdge(self.ahb_hclk)
        self.ahb_hsel.value = 1
        self.ahb_hprot.value = 1  # Data
        self.ahb_hsize.value = self.hsize[length]
        self.ahb_haddr.value = addr
        self.ahb_hwrite.value = 0
        self.ahb_htrans.value = self.HTRANS.NONSEQ.value
        self.ahb_hburst.value = self.HBURST.SINGLE.value
        await self._wait(self.ahb_hreadyout)

        # Data phase
        for i in range(length):
            if i != length - 1:
                addr += self.dwidth // 8
                self.ahb_haddr.value = addr
                self.ahb_htrans.value = self.HTRANS.SEQ.value
            else:
                self.ahb_htrans.value = self.HTRANS.IDLE.value

            await self._wait(self.ahb_hreadyout)


class AHBLiteManagerDriver(uvm_driver):
    """
    A driver for AHB Lite BFM
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                await self.bfm.write(it.addr, it.data)

            elif isinstance(it, BusReadItem):
                # TODO: Since the intended UUT does not support burst transfers
                # here we are reading only a single data word.
                await self.bfm.read(it.addr, 1)

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class AHBLiteMonitor(uvm_component):
    """
    AHB Lite bus monitor
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def watch(self):
        """
        Watches the bus
        """

        data_stage = False

        hdata = bytearray()
        haddr = None
        htrans = None
        hwrite = None

        while True:
            # Wait for reset deassertion if necessary
            if self.bfm.ahb_hreset.value == 0:
                await RisingEdge(self.bfm.ahb_hreset)

            # Wait for clock edge and hready
            await RisingEdge(self.bfm.ahb_hclk)
            hready = int(self.bfm.ahb_hreadyout)

            if hready:
                # Sample data
                if data_stage:
                    if htrans in [AHBLiteManagerBFM.HTRANS.SEQ, AHBLiteManagerBFM.HTRANS.NONSEQ]:
                        if hwrite:
                            data = collect_bytes(self.bfm.ahb_hwdata)
                        else:
                            data = collect_bytes(self.bfm.ahb_hrdata)
                        hdata += data

                    # Transfer end
                    elif htrans == AHBLiteManagerBFM.HTRANS.IDLE:
                        self.logger.debug(
                            "{}: 0x{:08X} {}".format(
                                "WR" if hwrite else "RD",
                                haddr,
                                ["0x{:02X}".format(b) for b in hdata],
                            )
                        )

                        data_stage = False

                        # Send response
                        if hwrite:
                            cls = BusWriteItem
                        else:
                            cls = BusReadItem

                        self.ap.write(cls(haddr, hdata))

                # Sample bus signals
                htrans = AHBLiteManagerBFM.HTRANS(self.bfm.ahb_htrans.value)
                if not data_stage:
                    if htrans in [AHBLiteManagerBFM.HTRANS.SEQ, AHBLiteManagerBFM.HTRANS.NONSEQ]:
                        hwrite = int(self.bfm.ahb_hwrite.value)
                        haddr = int(self.bfm.ahb_haddr.value)
                        hdata = bytearray()
                        data_stage = True

    async def run_phase(self):
        cocotb.start_soon(self.watch())


# ==============================================================================


class AXI4LiteSubordinateBFM(uvm_component):
    """
    AXI 4 Lite subordinate BFM. Allows low-level per-channel acknowledgement
    control.
    """

    SIGNALS = [
        "clk",
        "rst",
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
    ]

    def __init__(self, name, parent, uut, signal_prefix="", signal_map=None):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(
            self.SIGNALS,
            uut,
            self,
            uut_prefix=signal_prefix,
            obj_prefix="axi_",
            signal_map=signal_map,
        )

        # Determine bus parameters
        self.awidth = len(self.axi_awaddr)
        self.dwidth = len(self.axi_wdata)
        self.swidth = len(self.axi_wstrb)

        assert self.swidth == (self.dwidth // 8)

        self.logger.debug("AXI4 Lite BFM:")
        self.logger.debug(" awidth = {}".format(self.awidth))
        self.logger.debug(" dwidth = {}".format(self.dwidth))
        self.logger.debug(" swidth = {}".format(self.swidth))

        self.axi_awready.value = 0
        self.axi_wready.value = 0
        self.axi_arready.value = 0
        self.axi_rready.value = 0

    async def _wait(self, signal, max_cycles=200):
        """
        Waits for a signal to be asserted for at most max_cycles.
        Raises an exception if it does not
        """

        for i in range(max_cycles):
            await RisingEdge(self.axi_clk)
            if signal.value != 0:
                break
        else:
            raise TimeoutError("{} timeout".format(str(signal)))

    async def set_ready(self, channel, ready):
        """
        Sets/clears ready signal for the given channel on next clock edge
        """
        assert channel in ["aw", "w", "ar", "r"], channel
        await RisingEdge(self.axi_clk)

        sig = "axi_{}ready".format(channel)
        sig = getattr(self, sig)
        sig.value = int(ready)

    async def respond_aw(self):
        self.axi_awready.value = 1
        await self._wait(self.axi_awvalid)

        self.axi_awready.value = 0

    async def respond_w(self):
        self.axi_wready.value = 1
        for i in range(1):
            await self._wait(self.axi_wvalid)

        self.axi_wready.value = 0

    async def respond_b(self):
        await self._wait(self.axi_bready)

        self.axi_bvalid.value = 1
        self.axi_bid.value = 0  # TODO: support providing different BID values
        self.axi_bresp.value = 0  # TODO: support providing different BRESP values

        await RisingEdge(self.axi_clk)
        self.axi_bvalid.value = 0

    async def respond_ar(self):
        self.axi_arready.value = 1
        await self._wait(self.axi_arvalid)

        self.axi_arready.value = 0

    async def respond_r(self):
        await self._wait(self.axi_rready)

        self.axi_rvalid.value = 1
        self.axi_rdata.value = random.randrange(0, (1 << self.dwidth) - 1)

        await RisingEdge(self.axi_clk)
        self.axi_rvalid.value = 0


class AXI4LiteSubordinateDriver(uvm_driver):
    """
    PyUVM driver for AXI 4 Lite subordinate BFM
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        func_map = {
            "aw": self.bfm.respond_aw,
            "w": self.bfm.respond_w,
            "b": self.bfm.respond_b,
            "ar": self.bfm.respond_ar,
            "r": self.bfm.respond_r,
        }

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, AXI4LiteResponseItem):
                tasks = [cocotb.start_soon(func_map[c]()) for c in it.channels]
                await Combine(*tasks)

            elif isinstance(it, AXI4LiteReadyItem):
                tasks = [cocotb.start_soon(self.bfm.set_ready(c, it.ready)) for c in it.channels]
                await Combine(*tasks)

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


# ==============================================================================


class Scoreboard(uvm_component):
    """
    A scoreboard that compares AHB and AXI transfers and checks if they
    refer to the same address and contain the same data.
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.ahb_fifo = uvm_tlm_analysis_fifo("ahb_fifo", self)
        self.ahb_port = uvm_get_port("ahb_port", self)
        self.axi_fifo = uvm_tlm_analysis_fifo("axi_fifo", self)
        self.axi_port = uvm_get_port("axi_port", self)

    def connect_phase(self):
        self.ahb_port.connect(self.ahb_fifo.get_export)
        self.axi_port.connect(self.axi_fifo.get_export)

    def check_phase(self):
        # Check transactions
        while self.ahb_port.can_get() and self.axi_port.can_get():
            self.passed = True

            # Get items
            _, ahb_item = self.ahb_port.try_get()
            _, axi_item = self.axi_port.try_get()

            # Check
            msg = "AHB: {} A:0x{:08X} D:[{}], ".format(
                type(ahb_item).__name__,
                ahb_item.addr,
                ",".join(["0x{:02X}".format(d) for d in ahb_item.data]),
            )

            msg += "AXI: {} A:0x{:08X} D:[{}]".format(
                type(ahb_item).__name__,
                axi_item.addr,
                ",".join(["0x{:02X}".format(d) for d in axi_item.data]),
            )

            if ahb_item.addr != axi_item.addr or ahb_item.data != axi_item.data:
                self.logger.error(msg)
                self.passed = False
            else:
                self.logger.debug(msg)

        # Indicate an error if there is any leftover transaction in any of the
        # queues.
        if self.ahb_port.can_get() or self.axi_port.can_get():
            self.logger.error("Spurious transaction(s) on one of the buses")
            self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 50)
        ConfigDB().set(None, "*", "TEST_BURST_LEN", 10)
        ConfigDB().set(None, "*", "TEST_BURST_GAP", 10)

        # Sequencers
        self.ahb_seqr = uvm_sequencer("ahb_seqr", self)
        self.axi_seqr = uvm_sequencer("axi_seqr", self)

        ConfigDB().set(None, "*", "AHB_SEQR", self.ahb_seqr)
        ConfigDB().set(None, "*", "AXI_SEQR", self.axi_seqr)

        # BFM
        self.ahb_bfm = AHBLiteManagerBFM(
            "ahb_bfm",
            self,
            uut=cocotb.top,
            signal_prefix="ahb_",
            signal_map={
                "hclk": "clk",
                "hreset": "rst_l",
            },
        )

        self.axi_bfm = AXI4LiteSubordinateBFM(
            "axi_bfm",
            self,
            uut=cocotb.top,
            signal_prefix="axi_",
            signal_map={
                "clk": "clk",
                "rst": "rst_l",
            },
        )

        # Driver
        self.ahb_drv = AHBLiteManagerDriver("ahb_drv", self, bfm=self.ahb_bfm)
        self.axi_drv = AXI4LiteSubordinateDriver("axi_drv", self, bfm=self.axi_bfm)

        # Monitor
        self.ahb_mon = AHBLiteMonitor("ahb_mon", self, bfm=self.ahb_bfm)
        self.axi_mon = Axi4LiteMonitor("axi_mon", self, bfm=self.axi_bfm)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.ahb_drv.seq_item_port.connect(self.ahb_seqr.seq_item_export)
        self.axi_drv.seq_item_port.connect(self.axi_seqr.seq_item_export)

        self.ahb_mon.ap.connect(self.scoreboard.ahb_fifo.analysis_export)
        self.axi_mon.ap.connect(self.scoreboard.axi_fifo.analysis_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
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

        # Issue reset
        await self.do_reset()

        # Set common DUT signals
        cocotb.top.bus_clk_en.value = 1
        cocotb.top.ahb_hreadyin.value = 1

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
