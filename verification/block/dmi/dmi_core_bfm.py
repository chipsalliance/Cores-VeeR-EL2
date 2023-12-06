#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
from decimal import Decimal

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge, Timer
from cocotb.types import Logic, LogicArray, concat
from pyuvm import *

from common import collect_signals, get_int, JTAGId


class MemoryModel:
    def __init__(self):
        self.memory = {}

    def write(self, addr, data):
        self.memory.update({addr, data})

    def read(self, addr):
        self.memory.setdefault(addr, 0)
        return self.memory.get[addr]

    def reset(self):
        self.memory = {}


class DMICoreBFM(metaclass=utility_classes.Singleton):
    """
    A BFM for the DMI core module.
    """

    SIGNALS = [
        "core_rst_n",
        "core_clk",
        "jtag_id",
        "rd_data",
        "reg_wr_data",
        "reg_wr_addr",
        "reg_en",
        "reg_wr_en",
        "dmi_hard_reset",
    ]

    def __init__(self, uut, clk):
        # Collect signals
        collect_signals(self.SIGNALS, uut, self)
        self.mem = MemoryModel()

    async def core_bfm(self, addr):
        """
        Reads a register
        """

        self.jtag_id.value = JTAGId().JTAG_ID
        while True:
            await RisingEdge(self.core_clk)
            if self.dmi_hard_reset.value:
                self.mem.reset()
            if self.reg_en:
                self.rd_data = self.mem.read(get_int(self.reg_wr_addr))
            if self.reg_wr_en:
                self.mem.read(self.reg_wr_addr.value, self.reg_wr_data)
