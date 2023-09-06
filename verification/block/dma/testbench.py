
#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import *

from cocotbext.axi import AxiBus, AxiLiteMaster

# ==============================================================================


class BusWriteItem(uvm_sequence_item):
    """
    A generic data bus write request / response
    """

    def __init__(self, addr, data):
        super().__init__("BusWriteItem")
        self.addr = addr
        self.data = data


class BusReadItem(uvm_sequence_item):
    """
    A generic data bus read request / response
    """

    def __init__(self, addr, data=None):
        super().__init__("BusReadItem")
        self.addr = addr
        self.data = data

# ==============================================================================


def collect_signals(signals, uut, obj):
    """
    Collects signal objects from UUT and attaches them to the given object
    """

    for sig in signals:
        if hasattr(uut, sig):
            s = getattr(uut, sig)

        else:
            s = None
            logging.error(
                "Module {} does not have a signal '{}'".format(str(uut), sig)
            )

        setattr(obj, sig, s)

# ==============================================================================

class AxiSlaveDriver(uvm_component):
    """
    A driver component for AXI slave ports. Acts as AXI master.
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

        self.axi = AxiLiteMaster(AxiBus.from_prefix(self.dut, "dma_axi"),
                                 clock=self.dut.clk,
                                 reset=self.dut.rst_l,
                                 reset_active_level=False,
                                )

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                await self.axi.write(it.addr, it.data)
            elif isinstance(it, BusReadItem):
                it.data = await self.axi.read(it.addr, 4)
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

        # Sequencers
        self.axi_seqr = uvm_sequencer("axi_seqr", self)

        # AXI interface
        self.axi_drv = AxiSlaveDriver("axi_drv", self, dut=cocotb.top)

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
