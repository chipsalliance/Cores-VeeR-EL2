# Copyright (c) 2024 Antmicro
# SPDX-License-Identifier: Apache-2.0

import copy
import math
import os
import random
import struct
import subprocess
import textwrap
from dataclasses import dataclass

import pyuvm
from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.triggers import (
    ClockCycles,
    Event,
    FallingEdge,
    First,
    Lock,
    RisingEdge,
    Timer,
)
from cocotb.types import Array, Range
from pyuvm import *

# ==============================================================================


def get_opcode(asm_line, ext="rv32i_zicsr", size=32):
    """
    Generates opcode int based on a line of assembly
    """

    cmd = f"echo '{asm_line}' | riscv64-unknown-elf-as -march={ext} -o /dev/null -al | tail -n 1"

    # Take instruction hex (3rd column) and change its endianess
    out = subprocess.check_output([cmd], shell=True).decode().split()[2]
    out = "".join(textwrap.wrap(out, 2)[::-1])

    assert len(out) == size // 4, f"instruction '{asm_line}' assembled to unexpected width"

    return int(out, 16)


class DebugCmdType(IntEnum):
    GPR = 0
    CSR = 1
    MEMORY = 2


@dataclass
class DebugCmd:
    write: int
    type: DebugCmdType
    addr: int


class IbCtlInputItem(uvm_sequence_item):
    def __init__(self, debug_cmd, ifu_instr):
        super().__init__("IbCtlInputItem")

        self.debug_cmd = debug_cmd
        self.ifu_instr = ifu_instr

    @property
    def debug_instr(self):
        if self.debug_cmd.type == DebugCmdType.GPR:
            if self.debug_cmd.write:
                return get_opcode(f"or x{self.debug_cmd.addr}, x0, x0")
            else:
                return get_opcode(f"or x0, x{self.debug_cmd.addr}, x0")
        elif self.debug_cmd.type == DebugCmdType.CSR:
            if self.debug_cmd.write:
                return get_opcode(f"csrrw x0, {self.debug_cmd.addr}, x0")
            else:
                return get_opcode(f"csrrs x0, {self.debug_cmd.addr}, x0")
        return 0


class IbCtlOutputItem(uvm_sequence_item):
    def __init__(self, instr):
        self.instr = instr
        super().__init__("IbCtlOutputItem")


# ==============================================================================


class IbCtlDriver(uvm_driver):
    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            item = await self.seq_item_port.get_next_item()

            self.dut.dbg_cmd_valid.value = 1
            self.dut.dbg_cmd_write.value = item.debug_cmd.write
            self.dut.dbg_cmd_type.value = int(item.debug_cmd.type)
            self.dut.dbg_cmd_addr.value = item.debug_cmd.addr
            self.dut.ifu_i0_instr.value = item.ifu_instr
            await Timer(period, "ns")

            self.seq_item_port.item_done()


class IbCtlInputMonitor(uvm_component):
    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            # Wait for the driver to set the input signals
            await Timer(period, "ns")

            write = int(self.dut.dbg_cmd_write.value)
            type = int(self.dut.dbg_cmd_type.value)
            addr = int(self.dut.dbg_cmd_addr.value)
            ifu_instr = int(self.dut.ifu_i0_instr.value)

            self.ap.write(IbCtlInputItem(DebugCmd(write, DebugCmdType(type), addr), ifu_instr))


class IbCtlOutputMonitor(uvm_component):
    """
    Monitor for Trigger Logic outputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            # Wait for the driver to set the input signals
            await Timer(period, "ns")

            instr = int(self.dut.dec_i0_instr_d.value)

            self.ap.write(IbCtlOutputItem(instr))


# ==============================================================================


class IbCtlScoreboard(uvm_component):
    def __init__(self, name, parent):
        super().__init__(name, parent)
        self.passed = None

    def build_phase(self):
        self.fifo_inp = uvm_tlm_analysis_fifo("fifo_inp", self)
        self.fifo_out = uvm_tlm_analysis_fifo("fifo_out", self)
        self.port_inp = uvm_get_port("port_inp", self)
        self.port_out = uvm_get_port("port_out", self)

    def connect_phase(self):
        self.port_inp.connect(self.fifo_inp.get_export)
        self.port_out.connect(self.fifo_out.get_export)

    def check_phase(self):
        # Get item pairs
        while True:
            got_inp, item_inp = self.port_inp.try_get()
            got_out, item_out = self.port_out.try_get()

            if not got_inp and got_out:
                self.logger.error("No input item for output item")
                self.passed = False
                break

            if got_inp and not got_out:
                self.logger.error("No output item for input item")
                self.passed = False
                break

            if not got_inp and not got_out:
                break

            if self.passed is None:
                self.passed = True

            if item_inp.debug_instr != item_out.instr:
                self.logger.error(f"Expected {item_inp.debug_instr:08x} got {item_out.instr:08x}")
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class IbCtlSequence(uvm_sequence):
    def __init__(self, name, ops=None):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            write = random.randint(0, 1)
            type = random.choice([DebugCmdType.GPR, DebugCmdType.CSR])
            if type == DebugCmdType.GPR:
                addr = random.randrange(2**5)
            elif type == DebugCmdType.CSR:
                addr = random.randrange(2**12)

            debug_cmd = DebugCmd(
                write=write,
                type=type,
                addr=addr,
            )
            ifu_instr = random.randrange(2**31)

            item = IbCtlInputItem(debug_cmd, ifu_instr)

            await self.start_item(item)
            await self.finish_item(item)


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 1000)

        # Sequencers
        self.seqr = uvm_sequencer("seqr", self)

        # Driver
        self.drv = IbCtlDriver("drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = IbCtlInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = IbCtlOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = IbCtlScoreboard("scoreboard", self)

    def connect_phase(self):
        self.drv.seq_item_port.connect(self.seqr.seq_item_export)

        self.inp_mon.ap.connect(self.scoreboard.fifo_inp.analysis_export)
        self.out_mon.ap.connect(self.scoreboard.fifo_out.analysis_export)


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

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
