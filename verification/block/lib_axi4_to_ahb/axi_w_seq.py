# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

from axi_pkg import AXI_AXSIZE_ENCODING
from cocotb.types import LogicArray
from pyuvm import ConfigDB, uvm_sequence_item

from common import BaseSeq


class AXIWriteBaseSeqItem(uvm_sequence_item):
    def __init__(self, name):
        super().__init__(name)
        self.AXI_DATA_WIDTH = ConfigDB().get(None, "", "AXI_DATA_WIDTH")
        self.AXI_NUM_STRB_BITS = int(self.AXI_DATA_WIDTH / 8)

        self.axi_awvalid = 0
        self.axi_awid = 0
        self.axi_awaddr = 0
        self.axi_awsize = int(AXI_AXSIZE_ENCODING.MAX_8B_TRANSFER)
        self.axi_awprot = 0
        self.axi_wvalid = 0
        self.axi_wdata = 0
        self.axi_wstrb = LogicArray("1" * self.AXI_NUM_STRB_BITS)
        self.axi_wlast = 0
        self.axi_bready = 0

    def randomize(self):
        pass

    def __eq__(self, other):
        pass

    def __str__(self):
        return self.__class__.__name__


class AXIWriteTransactionRequestSeqItem(AXIWriteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_awvalid = 1

    def randomize(self):
        self.axi_awid = random.randint(0, 1)
        self.axi_awaddr = 8 * random.randint(8, 32)


class AXIWriteDataSeqItem(AXIWriteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_wvalid = 1
        self.axi_wstrb = LogicArray("1" * self.AXI_NUM_STRB_BITS)

    def randomize(self):
        self.axi_wdata = random.randint(0, 255)


class AXIWriteLastDataSeqItem(AXIWriteDataSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_wlast = 1


class AXIWriteResponseWriteSeqItem(AXIWriteBaseSeqItem):
    def __init__(
        self,
        name,
    ):
        super().__init__(name)
        self.axi_bready = 1


class AXIWriteInactiveSeqItem(AXIWriteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_awsize = 0
        self.axi_wstrb = 0


class AXIWriteTransactionRequestSeq(BaseSeq):
    async def body(self):
        items = [
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
            AXIWriteTransactionRequestSeqItem("AXIWriteTransactionRequestSeqItem"),
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
        ]
        await self.run_items(items)


class AXIWriteDataSeq(BaseSeq):
    async def body(self):
        items = [
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
            AXIWriteLastDataSeqItem("AXIWriteLastDataSeqItem"),
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
        ]
        await self.run_items(items)


class AXIWriteResponseSeq(BaseSeq):
    async def body(self):
        items = [
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
            AXIWriteResponseWriteSeqItem("AXIWriteLastDataSeqItem"),
            AXIWriteInactiveSeqItem("AXIWriteInactiveSeqItem"),
        ]
        await self.run_items(items)
