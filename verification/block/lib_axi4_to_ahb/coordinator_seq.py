# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

import cocotb
from ahb_lite_pkg import AHB_LITE_NOTIFICATION
from ahb_lite_seq import AHBLiteAcceptReadSeq, AHBLiteAcceptWriteSeq
from axi_r_seq import AXIReadTransactionRequestSeq
from axi_w_seq import (
    AXIWriteDataSeq,
    AXIWriteResponseSeq,
    AXIWriteTransactionRequestSeq,
)
from cocotb.triggers import RisingEdge
from pyuvm import ConfigDB, uvm_root, uvm_sequence


class CoordinatorSeq(uvm_sequence):
    async def axi_write(self, axi_seqr, ahb_seqr):
        axi_trq_seq = AXIWriteTransactionRequestSeq()
        axi_w_seq = AXIWriteDataSeq()
        axi_wresp_seq = AXIWriteResponseSeq()

        # Write Request
        await axi_trq_seq.start(axi_seqr)
        await self.delay(5)

        # Write Data
        await axi_w_seq.start(axi_seqr)

        # Handle AHB Response
        await self.ahb_response_handler(ahb_seqr=ahb_seqr, is_read=False)

        # Write Response
        await axi_wresp_seq.start(axi_seqr)

    async def axi_read(self, axi_seqr, ahb_seqr):
        axi_trq_seq = AXIReadTransactionRequestSeq()

        # Read Request
        await axi_trq_seq.start(axi_seqr)
        await self.delay(5)

        # Handle AHB Response
        await self.ahb_response_handler(ahb_seqr=ahb_seqr, is_read=True)
        await self.delay(5)

    async def delay(self, i):
        for _ in range(i):
            await RisingEdge(cocotb.top.clk)

    async def ahb_response_handler(self, ahb_seqr, is_read=True):
        ahb_read_response_seq = AHBLiteAcceptReadSeq("ahb_accept_read")
        ahb_write_response_seq = AHBLiteAcceptWriteSeq("ahb_accept_write")

        response = await ahb_seqr.seq_item_export.get_response()
        expected_response = (
            AHB_LITE_NOTIFICATION.AHB_LITE_READ if is_read else AHB_LITE_NOTIFICATION.AHB_LITE_WRITE
        )

        if response == expected_response:
            info_string = "CoordinatorSeq: AHB READ" if is_read else "CoordinatorSeq: AHB WRITE"
            uvm_root().logger.info(info_string)
            if is_read:
                await ahb_read_response_seq.start(ahb_seqr)
            else:
                await ahb_write_response_seq.start(ahb_seqr)
        else:
            raise ValueError(f"Expected response: {expected_response}. Got: {response}.")


class TestWriteChannelSeq(CoordinatorSeq):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "ahb_seqr")
        axi_seqr = ConfigDB().get(None, "", "axi_w_seqr")

        NUM_TRANSACTIONS_PER_TEST = ConfigDB().get(None, "", "NUM_TRANSACTIONS_PER_TEST")
        for _ in range(NUM_TRANSACTIONS_PER_TEST):
            await self.axi_write(axi_seqr=axi_seqr, ahb_seqr=ahb_seqr)
            await self.delay(10)


class TestReadChannelSeq(CoordinatorSeq):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "ahb_seqr")
        axi_seqr = ConfigDB().get(None, "", "axi_r_seqr")

        NUM_TRANSACTIONS_PER_TEST = ConfigDB().get(None, "", "NUM_TRANSACTIONS_PER_TEST")
        for _ in range(NUM_TRANSACTIONS_PER_TEST):
            await self.axi_read(axi_seqr=axi_seqr, ahb_seqr=ahb_seqr)
            await self.delay(10)


class TestBothChannelsSeq(CoordinatorSeq):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "ahb_seqr")
        axi_w_seqr = ConfigDB().get(None, "", "axi_w_seqr")
        axi_r_seqr = ConfigDB().get(None, "", "axi_r_seqr")
        NUM_TRANSACTIONS_PER_TEST = ConfigDB().get(None, "", "NUM_TRANSACTIONS_PER_TEST")

        test_all_q = []
        for _ in range(NUM_TRANSACTIONS_PER_TEST):
            rw = random.randint(0, 1)
            test_all_q += ["READ"] if rw else ["WRITE"]
        uvm_root().logger.info(f"TestBothChannelsSeq: Test Sequence: {test_all_q}")

        for i in range(NUM_TRANSACTIONS_PER_TEST):
            if test_all_q[i] == "READ":
                await self.axi_read(axi_seqr=axi_r_seqr, ahb_seqr=ahb_seqr)
            elif test_all_q[i] == "WRITE":
                await self.axi_write(axi_seqr=axi_w_seqr, ahb_seqr=ahb_seqr)
            else:
                raise ValueError("Unexpected value in sequence. Should be READ or WRITE.")
