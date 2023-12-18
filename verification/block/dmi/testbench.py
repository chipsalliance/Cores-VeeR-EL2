#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
from decimal import Decimal

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from dmi_agent import DMIAgent
from jtag_agent import JTAGAgent
from jtag_predictor import JTAGPredictor
from pyuvm import *


class Scoreboard(uvm_scoreboard):
    def build_phase(self):
        self.jtag_rsp_fifo = uvm_tlm_analysis_fifo("jtag_rsp_fifo", self)
        self.jtag_rsp_get_port = uvm_get_port("jtag_rsp_get_port", self)
        self.jtag_rsp_export = self.jtag_rsp_fifo.analysis_export

        self.dmi_rsp_fifo = uvm_tlm_analysis_fifo("dmi_rsp_fifo", self)
        self.dmi_rsp_get_port = uvm_get_port("dmi_rsp_get_port", self)
        self.dmi_rsp_export = self.dmi_rsp_fifo.analysis_export

    def connect_phase(self):
        self.jtag_rsp_get_port.connect(self.jtag_rsp_fifo.get_export)
        self.dmi_rsp_get_port.connect(self.dmi_rsp_fifo.get_export)

    def check_phase(self):
        self.logger.debug("Entering Scoreboard check phase")
        self.check_jtag()
        self.check_dmi()

    def check_dmi(self):
        passed = True
        while self.dmi_rsp_get_port.can_get():
            _, item = self.dmi_rsp_get_port.try_get()

            values, dmi_type = item
            rd_data, dmi_rdata, dmi_addr, dmi_en, pred_en = values

            if pred_en != dmi_en:
                self.logger.error("Unexpected state of DMI enable signal")
                passed = False

            self.logger.debug("Checking DMI {} at address {}".format(dmi_type, str(hex(dmi_addr))))
            if dmi_en and (rd_data != dmi_rdata):
                self.logger.error(
                    "Read data does not match expected data ({} vs {})".format(
                        str(hex(rd_data)), str(hex(dmi_rdata))
                    )
                )
                passed = False

        assert passed

    def check_jtag(self):
        passed = True
        while self.jtag_rsp_get_port.can_get():
            _, item = self.jtag_rsp_get_port.try_get()

            out_ports = item[0]
            predicted_ports = item[1]

            for i, s in enumerate(["tdo", "tdoEnable"]):
                out = out_ports[i]
                predicted = predicted_ports[i]

                self.logger.debug(
                    "Current check of {} (actual: {} vs expected: {})".format(s, out, predicted)
                )
                if out != predicted:
                    self.logger.error("Unexpected state of {} ({} vs {})".format(s, out, predicted))
                    passed = False

        assert passed


class BaseEnvironment(uvm_env):
    def __init__(self, name, test_obj):
        super().__init__(name, test_obj)

    def build_phase(self):
        # Config
        # JTAG clock must be at least twice as fast as core clock
        ConfigDB().set(None, "*", "TEST_JTAG_CLK_PERIOD", 3)
        ConfigDB().set(None, "*", "TEST_CORE_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "AWIDTH", 7)

        self.jtag_agent = JTAGAgent("jtag_agent", self)
        self.dmi_agent = DMIAgent("dmi_agent", self)
        self.predictor = JTAGPredictor(cocotb.top)
        self.scoreboard = Scoreboard("scoreboard", self)

        ConfigDB().set(None, "*", "JTAG_PREDICTOR", self.predictor)

    def connect_phase(self):
        self.jtag_agent.monitor.ap.connect(self.scoreboard.jtag_rsp_export)
        self.dmi_agent.monitor.ap.connect(self.scoreboard.dmi_rsp_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        # Synchronize pyuvm logging level with cocotb logging level.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = BaseEnvironment("env", self)

    def start_clock(self, name, period):
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self, signals, timeLength="100e-9", isActiveHigh=True):
        assert isinstance(signals, list)

        for s in signals:
            signal = getattr(cocotb.top, s)
            signal.value = int(isActiveHigh)

        await Timer(Decimal(timeLength), units="sec")

        for s in signals:
            signal = getattr(cocotb.top, s)
            signal.value = not int(isActiveHigh)

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        core_period = ConfigDB().get(None, "", "TEST_CORE_CLK_PERIOD")
        jtag_period = ConfigDB().get(None, "", "TEST_JTAG_CLK_PERIOD")
        self.start_clock("core_clk", core_period)
        self.start_clock("tck", jtag_period)
        clk = getattr(cocotb.top, "core_clk")

        # Issue reset
        resetLength = "100e-9"
        await self.do_reset(
            signals=["trst_n", "core_rst_n"], timeLength=resetLength, isActiveHigh=False
        )

        await ClockCycles(clk, 2)
        await self.run()
        await ClockCycles(clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
