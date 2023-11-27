# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
import random

from enum import Enum

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import (
    ClockCycles,
    FallingEdge,
    RisingEdge,
    Combine,
)
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

class AXI4LiteReadyItem(uvm_sequence_item):
    """
    """

    def __init__(self, channels, ready=True):
        super().__init__("AXI4LiteReadyItem")
        self.channels = channels
        self.ready    = ready

class AXI4LiteResponseItem(uvm_sequence_item):
    """
    An item describing a response for an AXI4 lite channel(s)
    """

    def __init__(self, channels):
        super().__init__("AXI4LiteResponseItem")
        self.channels = channels

# ==============================================================================

def collect_signals(signals, uut, obj, uut_prefix="", obj_prefix="", signal_map=None):
    """
    Collects signal objects from UUT and attaches them to the given object.
    Optionally UUT signals can be prefixed with the uut_prefix and object
    signals with the obj_prefix. If signal_map is given it should be a dict
    mapping signal names to actual UUT signal names.
    """

    for sig in signals:
        if signal_map is not None:
            uut_sig = signal_map.get(sig, uut_prefix + sig)
        else:
            uut_sig = uut_prefix + sig
        obj_sig = obj_prefix + sig
        if hasattr(uut, uut_sig):
            s = getattr(uut, uut_sig)

        else:
            s = None
            logging.error("Module {} does not have a signal '{}'".format(str(uut), sig))

        setattr(obj, obj_sig, s)

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
        IDLE    = 0b00
        BUSY    = 0b01
        NONSEQ  = 0b10
        SEQ     = 0b11

    class HBURST(Enum):
        SINGLE  = 0b000
        INCR    = 0b001
        WRAP4   = 0b010
        INCR4   = 0b011
        WRAP8   = 0b100
        INCR8   = 0b101
        WRAP16  = 0b110
        INCR16  = 0b111

    def __init__(self, name, parent, uut, signal_prefix="", signal_map=None):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self, uut_prefix=signal_prefix,
                        obj_prefix="ahb_", signal_map=signal_map)

        # Determine bus parameters
        self.awidth = len(self.ahb_haddr)
        self.dwidth = len(self.ahb_hwdata) # Assuming hrdata is the same

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
            if signal.value != 0:
                break
        else:
            raise RuntimeError("{} timeout".format(str(signal)))

    async def write(self, addr, data):
        """
        Issues a write transfer
        """

        # Wait for reset deassertion if necessary
        if self.ahb_hreset.value == 0:
            await RisingEdge(self.ahb_hreset)

        # Address phase
        await RisingEdge(self.ahb_hclk)
        self.ahb_hsel.value     = 1
        self.ahb_hprot.value    = 1 # Data
        self.ahb_hsize.value    = 3 # 64B
        self.ahb_haddr.value    = addr
        self.ahb_hwrite.value   = 1
        self.ahb_htrans.value   = self.HTRANS.NONSEQ.value
        self.ahb_hburst.value   = self.HBURST.INCR.value # TODO: Others?
        await self._wait(self.ahb_hreadyout)

        # Data phase
        for i, word in enumerate(data):

            if i != len(data) - 1:
                addr += self.dwidth // 8
                self.ahb_haddr.value  = addr
                self.ahb_htrans.value = self.HTRANS.SEQ.value
            else:
                self.ahb_htrans.value = self.HTRANS.IDLE.value

            self.ahb_hwdata.value = word
            await self._wait(self.ahb_hreadyout)

    async def read(self, addr, length):
        """
        Issues an AHB read transfer for the given number of words. The word
        count must be one of miltiplies of data bus width supported by AHB
        Lite.
        """

        hsize = {
            64   // self.dwidth: 3,
            128  // self.dwidth: 4,
            256  // self.dwidth: 5,
            512  // self.dwidth: 6,
            1024 // self.dwidth: 7,
        }
        assert length in hsize

        # Wait for reset deassertion if necessary
        if self.ahb_hreset.value == 0:
            await RisingEdge(self.ahb_hreset)

        # Address phase
        await RisingEdge(self.ahb_hclk)
        self.ahb_hsel.value     = 1
        self.ahb_hprot.value    = 1 # Data
        self.ahb_hsize.value    = hsize[length]
        self.ahb_haddr.value    = addr
        self.ahb_hwrite.value   = 0
        self.ahb_htrans.value   = self.HTRANS.NONSEQ.value
        self.ahb_hburst.value   = self.HBURST.INCR.value # TODO: Others?
        await self._wait(self.ahb_hreadyout)

        # Data phase
        for i in range(length):

            if i != length - 1:
                addr += (self.dwidth // 8)
                self.ahb_haddr.value  = addr
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
                await self.bfm.read(it.addr, 1)

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()

# ==============================================================================

class AXI4LiteSubordinateBFM(uvm_component):
    """
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
        "rlast",
    ]

    def __init__(self, name, parent, uut, signal_prefix="", signal_map=None):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self, uut_prefix=signal_prefix,
                        obj_prefix="axi_", signal_map=signal_map)

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
        self.axi_wready.value  = 0
        self.axi_arready.value = 0
        self.axi_rready.value  = 0

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
            raise RuntimeError("{} timeout".format(str(signal)))

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

        # Assert awready
        self.axi_awready.value = 1
        # Wait for awvalid
        await self._wait(self.axi_awvalid)

        # Sample request
        # TODO:

        # Deassert awready
        self.axi_awready.value = 0

    async def respond_w(self):

        # Assert wready
        self.axi_wready.value = 1

        # Wait for valid, receive data
        for i in range(1):
            await self._wait(self.axi_wvalid)
            # TODO:

        # Deassert wready
        self.axi_wready.value = 0

    async def respond_b(self):

        # Wait for bready
        await self._wait(self.axi_bready)

        # Transmitt acknowledge
        self.axi_bvalid.value   = 1
        self.axi_bid.value      = 0 # TODO
        self.axi_bresp.value    = 0 # TODO

        await RisingEdge(self.axi_clk)
        self.axi_bvalid.value   = 0

#        """
#        Write responder task (AW, W and B channels).
#        """
#        while True:
#
#            # Wait for reset deassertion if necessary
#            if self.axi_rst.value == 0:
#                await RisingEdge(self.axi_rst)
#
#            # Assert awready and wready
#            self.axi_awready.value    = 1
#            self.axi_wready.value     = 1
#
#            # Wait for AW
#            while True:
#                await RisingEdge(self.axi_clk)
#                if self.axi_awvalid.value and self.axi_awready.value:
#                    break
#
#            # Deassert awready
#            self.axi_awready.value = 0
#
#            # Receive data
#            for i in range(1):
#                await self._wait(self.axi_wvalid)
#
#            # Wait for bready
#            await self._wait(self.axi_bready)
#
#            # Transmitt acknowledge
#            self.axi_bvalid.value   = 1
#            self.axi_bid.value      = 0 # TODO
#            self.axi_bresp.value    = 0 # TODO
#
#            await RisingEdge(self.axi_clk)
#            self.axi_bvalid.value   = 0
#
#    async def respond_to_reads(self):
#        """
#        Read responder task (AR and R channels). Returns random data.
#        """
#        while True:
#
#            # Wait for reset deassertion if necessary
#            if self.axi_rst.value == 0:
#                await RisingEdge(self.axi_rst)
#
#            # Assert arready
#            self.axi_arready.value = 1
#
#            # Wait for AR
#            while True:
#                await RisingEdge(self.axi_clk)
#                if self.axi_arvalid.value and self.axi_arready.value:
#                    break
#
#            # Deassert arready
#            self.axi_arready.value = 0
#
#            # Dummy wait to simulate subordinate latency
#            await ClockCycles(self.axi_clk, 5)
#
#            # Wait for rready
#            await self._wait(self.axi_rready)
#
#            # Transmitt data
#            self.axi_rvalid.value   = 1
#            self.axi_rid.value      = 0 # TODO
#            self.axi_rdata.value    = random.randrange(0, (1 << self.dwidth) - 1)
#            self.axi_rresp.value    = 0 # TODO
#            
#            await RisingEdge(self.axi_clk)
#            self.axi_rvalid.value   = 0

class AXI4LiteSubordinateDriver(uvm_driver):
    """
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        func_map = {
            "aw":   self.bfm.respond_aw,
            "w":    self.bfm.respond_w,
            "b":    self.bfm.respond_b,
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


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):

        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 50)
        ConfigDB().set(None, "*", "TEST_BURST_LEN",  10)
        ConfigDB().set(None, "*", "TEST_BURST_GAP",  10)

        # Sequencers
        self.ahb_seqr = uvm_sequencer("ahb_seqr", self)
        self.axi_seqr = uvm_sequencer("axi_seqr", self)

        ConfigDB().set(None, "*", "AHB_SEQR", self.ahb_seqr)
        ConfigDB().set(None, "*", "AXI_SEQR", self.axi_seqr)

        # BFM
        self.ahb_bfm = AHBLiteManagerBFM(
            "ahb_bfm", self, uut=cocotb.top,
            signal_prefix="ahb_", signal_map = {
                "hclk":   "clk",
                "hreset": "rst_l",
            })

        self.axi_bfm = AXI4LiteSubordinateBFM(
            "axi_bfm", self, uut=cocotb.top,
            signal_prefix="axi_", signal_map = {
                "clk":    "clk",
                "rst":    "rst_l",
            })

        # Driver
        self.ahb_drv = AHBLiteManagerDriver("ahb_drv", self, bfm=self.ahb_bfm)
        self.axi_drv = AXI4LiteSubordinateDriver("axi_drv", self, bfm=self.axi_bfm)

#        # Monitor
#        self.mem_mon = MemMonitor("mem_mon", self, dut=cocotb.top)
#
#        # Scoreboard
#        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.ahb_drv.seq_item_port.connect(self.ahb_seqr.seq_item_export)
        self.axi_drv.seq_item_port.connect(self.axi_seqr.seq_item_export)
#        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        pass


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
        cocotb.top.bus_clk_en.value   = 1
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

