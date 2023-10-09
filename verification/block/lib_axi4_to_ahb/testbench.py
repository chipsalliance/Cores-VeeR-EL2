# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import logging
import os
from decimal import Decimal

import cocotb
from ahb_lite_agent import AHBLiteAgent
from ahb_lite_pkg import AHB_LITE_RESPONSE_CODES, AHB_LITE_TRANSFER_TYPE_ENCODING
from axi_pkg import AXI_READ_RESPONSE_CODES, AXI_WRITE_RESPONSE_CODES
from axi_r_agent import AXIReadChannelAgent
from axi_w_agent import AXIWriteChannelAgent
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from pyuvm import (
    ConfigDB,
    uvm_component,
    uvm_env,
    uvm_get_port,
    uvm_report_object,
    uvm_test,
    uvm_tlm_analysis_fifo,
)


class Scoreboard(uvm_component):
    def build_phase(self):
        self.axi_w_req_fifo = uvm_tlm_analysis_fifo("axi_w_req_fifo", self)
        self.axi_w_rsp_fifo = uvm_tlm_analysis_fifo("axi_w_rsp_fifo", self)
        self.axi_w_req_get_port = uvm_get_port("axi_w_req_get_port", self)
        self.axi_w_rsp_get_port = uvm_get_port("axi_w_rsp_get_port", self)
        self.axi_w_req_export = self.axi_w_req_fifo.analysis_export
        self.axi_w_rsp_export = self.axi_w_rsp_fifo.analysis_export

        self.axi_r_req_fifo = uvm_tlm_analysis_fifo("axi_r_req_fifo", self)
        self.axi_r_rsp_fifo = uvm_tlm_analysis_fifo("axi_r_rsp_fifo", self)
        self.axi_r_req_get_port = uvm_get_port("axi_r_req_get_port", self)
        self.axi_r_rsp_get_port = uvm_get_port("axi_r_rsp_get_port", self)
        self.axi_r_req_export = self.axi_r_req_fifo.analysis_export
        self.axi_r_rsp_export = self.axi_r_rsp_fifo.analysis_export

        self.ahb_req_fifo = uvm_tlm_analysis_fifo("ahb_req_fifo", self)
        self.ahb_rsp_fifo = uvm_tlm_analysis_fifo("ahb_rsp_fifo", self)
        self.ahb_req_get_port = uvm_get_port("ahb_req_get_port", self)
        self.ahb_rsp_get_port = uvm_get_port("ahb_rsp_get_port", self)
        self.ahb_req_export = self.ahb_req_fifo.analysis_export
        self.ahb_rsp_export = self.ahb_rsp_fifo.analysis_export

    def connect_phase(self):
        self.axi_w_req_get_port.connect(self.axi_w_req_fifo.get_export)
        self.axi_w_rsp_get_port.connect(self.axi_w_rsp_fifo.get_export)

        self.axi_r_req_get_port.connect(self.axi_r_req_fifo.get_export)
        self.axi_r_rsp_get_port.connect(self.axi_r_rsp_fifo.get_export)

        self.ahb_req_get_port.connect(self.ahb_req_fifo.get_export)
        self.ahb_rsp_get_port.connect(self.ahb_rsp_fifo.get_export)

    def check_phase(self):
        passed = True
        self.logger.info("Check Phase")
        axi_w_transactions = self.check_axi_write()
        axi_r_transactions = self.check_axi_read()
        ahb_transactions = self.check_ahb()

        ahb_w_transactions = []
        ahb_r_transactions = []
        for transaction in ahb_transactions:
            if transaction["TYPE"] == "WRITE":
                ahb_w_transactions.append(transaction)
            else:
                ahb_r_transactions.append(transaction)

        assert len(axi_w_transactions) == len(ahb_w_transactions)
        assert len(axi_r_transactions) == len(ahb_r_transactions)

        num_w_transactions = len(axi_w_transactions)
        for id in range(num_w_transactions):
            self.logger.info(f"AXI Wrote {axi_w_transactions[id]}")
            self.logger.info(f"AHB Wrote {ahb_w_transactions[id]}")
            assert axi_w_transactions[id] == ahb_w_transactions[id]

        num_r_transactions = len(axi_r_transactions)
        for id in range(num_r_transactions):
            self.logger.info(f"AXI Read {axi_r_transactions[id]}")
            self.logger.info(f"AHB Read {ahb_r_transactions[id]}")
            assert axi_r_transactions[id] == ahb_r_transactions[id]

        assert passed

    def check_axi_write(self):
        axi_w_req_list = []
        while self.axi_w_req_get_port.can_get():
            _, item = self.axi_w_req_get_port.try_get()
            axi_w_req_dict = {}

            awvalid = item[0]
            awaddr = item[2]
            wvalid = item[5]
            wdata = item[6]

            if awvalid:
                axi_w_req_dict["ADDRESS"] = awaddr
            elif wvalid:
                axi_w_req_dict["DATA"] = wdata
            else:
                raise ValueError("Unexpected item in monitor queue.")

            axi_w_req_list.append(axi_w_req_dict)

        # For each request there should be one data item
        transaction_requests = axi_w_req_list[0::2]
        transaction_data = axi_w_req_list[1::2]
        assert len(transaction_requests) == len(transaction_data)

        num_transactions = len(transaction_data)
        axi_w_transactions = []
        for id in range(num_transactions):
            axi_w_transaction = {}
            axi_w_transaction["TYPE"] = "WRITE"
            axi_w_transaction["ADDRESS"] = transaction_requests[id]["ADDRESS"]
            axi_w_transaction["DATA"] = transaction_data[id]["DATA"]
            axi_w_transactions.append(axi_w_transaction)

        # Check if each transaction is confirmed
        axi_w_rsp_list = []
        while self.axi_w_rsp_get_port.can_get():
            _, item = self.axi_w_rsp_get_port.try_get()
            axi_w_rsp_dict = {}

            bvalid = item[2]
            bresp = item[3]

            assert bvalid == 1
            assert bresp == AXI_WRITE_RESPONSE_CODES.OKAY
            axi_w_rsp_dict["STATUS"] = "OKAY"
            axi_w_rsp_list.append(axi_w_rsp_dict)

        assert len(transaction_requests) == len(axi_w_rsp_list)

        self.logger.debug(f"AXI WRITE TRANSACTIONS {axi_w_transactions}")
        return axi_w_transactions

    def check_axi_read(self):
        axi_r_req_list = []
        while self.axi_r_req_get_port.can_get():
            _, item = self.axi_r_req_get_port.try_get()
            axi_r_req_dict = {}

            arvalid = item[0]
            araddr = item[2]

            assert arvalid == 1
            axi_r_req_dict["TYPE"] = "READ"
            axi_r_req_dict["ADDRESS"] = araddr
            axi_r_req_list.append(axi_r_req_dict)

        self.logger.debug(f"AXI READ REQUESTS: {axi_r_req_list}")

        axi_r_rsp_list = []
        while self.axi_r_rsp_get_port.can_get():
            _, item = self.axi_r_rsp_get_port.try_get()
            axi_r_rsp_dict = {}

            rvalid = item[1]
            rdata = item[3]
            rresp = item[4]

            assert rvalid == 1
            assert rresp == AXI_READ_RESPONSE_CODES.OKAY

            axi_r_rsp_dict["TYPE"] = "READ RESPONSE"
            axi_r_rsp_dict["DATA"] = int(rdata)
            axi_r_rsp_list.append(axi_r_rsp_dict)

        assert len(axi_r_req_list) == len(axi_r_rsp_list)

        axi_r_transactions = []
        num_transactions = len(axi_r_req_list)
        for id in range(num_transactions):
            axi_r_transaction = {}
            axi_r_transaction["TYPE"] = "READ"
            axi_r_transaction["ADDRESS"] = axi_r_req_list[id]["ADDRESS"]
            axi_r_transaction["DATA"] = axi_r_rsp_list[id]["DATA"]
            axi_r_transactions.append(axi_r_transaction)

        self.logger.debug(f"AXI READ TRANSACTIONS {axi_r_transactions}")

        return axi_r_transactions

    def check_ahb(self):
        ahb_rsp_list = []
        is_even = True
        ahb_rsp_dict = {}
        while self.ahb_rsp_get_port.can_get():
            _, item = self.ahb_rsp_get_port.try_get()

            haddr = item[0]
            htrans = item[5]
            hwrite = item[6]
            hwdata = item[7]

            if is_even:
                assert htrans == AHB_LITE_TRANSFER_TYPE_ENCODING.NONSEQ

                if hwrite:
                    ahb_rsp_dict["TYPE"] = "WRITE"
                    ahb_rsp_dict["DATA"] = int(hwdata)
                else:
                    ahb_rsp_dict["TYPE"] = "READ"

                ahb_rsp_dict["ADDRESS"] = int(haddr)

            if not is_even:
                ahb_rsp_list.append(ahb_rsp_dict)
                ahb_rsp_dict = {}

            is_even = not is_even

        self.logger.debug(f"ahb_rsp_list {ahb_rsp_list}")

        ahb_req_list = []
        is_even = True
        ahb_req_dict = {}
        while self.ahb_req_get_port.can_get():
            _, item = self.ahb_req_get_port.try_get()

            hrdata = item[0]
            hready = item[1]
            hresp = item[2]

            assert hready == 1
            assert hresp == AHB_LITE_RESPONSE_CODES.OKAY

            if not is_even:
                ahb_req_dict["DATA"] = int(hrdata)
                ahb_req_list.append(ahb_req_dict)
                ahb_req_dict = {}

            is_even = not is_even

        self.logger.debug(f"ahb_req_list {ahb_req_list}")

        assert len(ahb_rsp_list) == len(ahb_req_list)

        ahb_transactions = []
        num_transactions = len(ahb_rsp_list)
        for id in range(num_transactions):
            ahb_transaction = {}
            if ahb_rsp_list[id]["TYPE"] == "WRITE":
                ahb_transaction = ahb_rsp_list[id]
                ahb_transactions.append(ahb_transaction)
                continue
            else:
                ahb_transaction["TYPE"] = "READ"
                ahb_transaction["ADDRESS"] = ahb_rsp_list[id]["ADDRESS"]
                ahb_transaction["DATA"] = ahb_req_list[id]["DATA"]
                ahb_transactions.append(ahb_transaction)

        self.logger.debug(f"AHB Transactions {ahb_transactions}")
        return ahb_transactions


class BaseEnvironment(uvm_env):
    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "AXI_DATA_WIDTH", 64)
        ConfigDB().set(None, "*", "DUT_PRTY", cocotb.top.PRTY.value)
        ConfigDB().set(None, "*", "DUT_TAG", cocotb.top.TAG.value)
        ConfigDB().set(None, "*", "DUT_ID", cocotb.top.ID.value)

        ConfigDB().set(None, "*", "NUM_TRANSACTIONS_PER_TEST", 32)

        self.agent_axi_w = AXIWriteChannelAgent("axi_w_agent", self)
        self.agent_axi_r = AXIReadChannelAgent("axi_r_agent", self)
        self.agent_ahb = AHBLiteAgent("ahb_lite_agent", self)

        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.agent_axi_w.monitor.ap_req.connect(self.scoreboard.axi_w_req_export)
        self.agent_axi_w.monitor.ap_rsp.connect(self.scoreboard.axi_w_rsp_export)

        self.agent_axi_r.monitor.ap_req.connect(self.scoreboard.axi_r_req_export)
        self.agent_axi_r.monitor.ap_rsp.connect(self.scoreboard.axi_r_rsp_export)

        self.agent_ahb.monitor.ap_req.connect(self.scoreboard.ahb_req_export)
        self.agent_ahb.monitor.ap_rsp.connect(self.scoreboard.ahb_rsp_export)


class BaseTest(uvm_test):
    """ """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        # Synchronize pyuvm logging level with cocotb logging level.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = BaseEnvironment("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self, signalName, timeLength="100e-9", isActiveHigh=True):
        signal = getattr(cocotb.top, signalName)
        signal.value = int(isActiveHigh)
        self.config()
        await Timer(Decimal(timeLength), units="sec")
        signal.value = not int(isActiveHigh)

    def config(self):
        cocotb.top.scan_mode.value = 0
        cocotb.top.bus_clk_en.value = 1
        cocotb.top.clk_override.value = 0
        cocotb.top.dec_tlu_force_halt.value = 0

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("free_clk")
        clk = getattr(cocotb.top, "clk")

        # Issue reset
        resetLength = "10e-9"
        await self.do_reset(signalName="rst_l", timeLength=resetLength, isActiveHigh=False)

        await ClockCycles(clk, 2)
        await self.run()
        await ClockCycles(clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
