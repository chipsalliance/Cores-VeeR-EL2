# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

from axi_pkg import AXI_AXSIZE_ENCODING
from pyuvm import ConfigDB, uvm_sequence_item

from common import BaseSeq


class AXIReadBaseSeqItem(uvm_sequence_item):
    def __init__(self, name):
        super().__init__(name)
        self.AXI_DATA_WIDTH = ConfigDB().get(None, "", "AXI_DATA_WIDTH")
        self.AXI_NUM_STRB_BITS = int(self.AXI_DATA_WIDTH / 8)

        self.axi_arvalid = 0
        self.axi_arid = 0
        self.axi_araddr = 0
        self.axi_arsize = int(AXI_AXSIZE_ENCODING.MAX_8B_TRANSFER)
        self.axi_arprot = 0
        self.axi_rready = 0

    def randomize(self):
        pass

    def __eq__(self, other):
        pass

    def __str__(self):
        return self.__class__.__name__


class AXIReadTransactionRequestSeqItem(AXIReadBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_arvalid = 1

    def randomize(self):
        self.axi_araddr = 8 * random.randint(8, 32)


class AXIReadResponseReadSeqItem(AXIReadBaseSeqItem):
    def __init__(
        self,
        name,
    ):
        super().__init__(name)
        self.axi_rready = 1


class AXIReadInactiveSeqItem(AXIReadBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.axi_arsize = 0


class AXIReadTransactionRequestSeq(BaseSeq):
    async def body(self):
        items = [
            AXIReadTransactionRequestSeqItem("AXIReadTransactionRequestSeqItem"),
            AXIReadInactiveSeqItem("AXIReadInactiveSeqItem"),
        ]
        await self.run_items(items)


class AXIReadTransactionResponseSeq(BaseSeq):
    async def body(self):
        items = [
            AXIReadResponseReadSeqItem("AXIReadLastDataSeqItem"),
            AXIReadInactiveSeqItem("AXIReadInactiveSeqItem"),
        ]
        await self.run_items(items)
