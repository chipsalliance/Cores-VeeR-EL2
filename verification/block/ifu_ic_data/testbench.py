import logging
import os

from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, Timer
from pyuvm import *


class Item(uvm_sequence_item):
    """
    A generic item
    """

    def __init__(self):
        super().__init__("Item")


class Sequence(uvm_sequence):
    """
    A generic sequence
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        await Timer(100, "ns")


class Driver(uvm_driver):
    """
    Driver
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        pass


class Monitor(uvm_component):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        pass


class Scoreboard(uvm_component):
    """
    Checks if all decompressed instructions have the expected value
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        self.passed = True

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 1)
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)

        # Sequencers
        self.seqr = uvm_sequencer("seqr", self)

        # Driver
        self.drv = Driver("drv", self)

        # Monitor
        self.mon = Monitor("mon", self)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.drv.seq_item_port.connect(self.seqr.seq_item_export)
        self.mon.ap.connect(self.scoreboard.fifo.analysis_export)


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

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
        await self.run()
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
