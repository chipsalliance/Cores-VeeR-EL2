# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import *

# ==============================================================================


class MemWriteItem(uvm_sequence_item):
    """
    Memory write item
    """

    def __init__(self, addr, data):
        super().__init__("MemWriteItem")
        self.addr = addr
        self.data = data


class MemReadItem(uvm_sequence_item):
    """
    Memory read item
    """

    def __init__(self, addr, data=None):
        super().__init__("MemReadItem")
        self.addr = addr
        self.data = data


# ==============================================================================


class MemDriver(uvm_driver):
    """
    Memory interface driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            # Write
            if isinstance(it, MemWriteItem):
                # Wait for rising edge, do the write
                await RisingEdge(self.dut.clk)
                self.dut.dccm_wren.value = 1

                self.dut.dccm_wr_addr_lo.value = it.addr
                self.dut.dccm_wr_data_lo.value = it.data

                self.dut.dccm_wr_addr_hi.value = it.addr
                self.dut.dccm_wr_data_hi.value = it.data

                # Wait for rising edge, deassert write
                await RisingEdge(self.dut.clk)
                self.dut.dccm_wren.value = 0

            # Read
            elif isinstance(it, MemReadItem):
                # Wait for rising edge, do the read
                await RisingEdge(self.dut.clk)
                self.dut.dccm_rden.value = 1

                self.dut.dccm_rd_addr_lo.value = it.addr
                self.dut.dccm_rd_addr_hi.value = it.addr

                # Wait for rising edge, deassert read
                await RisingEdge(self.dut.clk)
                self.dut.dccm_rden.value = 0

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class MemMonitor(uvm_component):
    """
    Memory interface monitor
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Act on rising edges
            await RisingEdge(self.dut.clk)

            # Since the driver drives both lo and hi with the same values
            # here we sample only lo

            # Write
            if self.dut.dccm_wren.value:
                addr = int(self.dut.dccm_wr_addr_lo)
                data = int(self.dut.dccm_wr_data_lo)
                self.ap.write(MemWriteItem(addr, data))

            # Read
            if self.dut.dccm_rden.value:
                addr = int(self.dut.dccm_rd_addr_lo)

                # Wait additional clock cycle
                await RisingEdge(self.dut.clk)

                data = int(self.dut.dccm_rd_data_lo)
                self.ap.write(MemReadItem(addr, data))


# ==============================================================================


class Scoreboard(uvm_component):
    """
    A scoreboard that tracks memory writes and compares them agains data read
    from the memory. It also checks if both reads and writes took place
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
        did_write = False
        did_read = False
        mem_content = dict()

        # Process items
        while self.port.can_get():
            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # Memory write
            if isinstance(item, MemWriteItem):
                mem_content[item.addr] = item.data
                did_write = True

                self.logger.debug("[0x{:08X}] <= 0x{:08X}".format(item.addr, item.data))

            # Memory read
            elif isinstance(item, MemReadItem):
                data = mem_content.get(item.addr, None)
                did_read = True

                self.logger.debug(
                    "[0x{:08X}] == 0x{:08X} vs. 0x{:08X} {}".format(
                        item.addr, item.data, data, item.data == data
                    )
                )

                if data != item.data:
                    self.logger.error(
                        "Data mismatch, mem[0x{:08X}] is 0x{:08X}, should be 0x{:08X}".format(
                            item.addr, item.data, data
                        )
                    )
                    self.passed = False

        # There were no writes
        if not did_write:
            self.logger.error("There were no writes")
            self.passed = False

        # There were no reads
        if not did_read:
            self.logger.error("There were no reads")
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

        ConfigDB().set(None, "*", "DCCM_BITS", 0x10)
        ConfigDB().set(None, "*", "DCCM_FDATA_WIDTH", 0x20)

        # Sequencers
        self.mem_seqr = uvm_sequencer("mem_seqr", self)

        # Driver
        self.mem_drv = MemDriver("mem_drv", self, dut=cocotb.top)

        # Monitor
        self.mem_mon = MemMonitor("mem_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.mem_drv.seq_item_port.connect(self.mem_seqr.seq_item_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)


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
        self.start_clock("active_clk")

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
