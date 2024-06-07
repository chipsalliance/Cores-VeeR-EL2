# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

from ahb_lite_pkg import AHB_LITE_RESPONSE_CODES
from pyuvm import uvm_sequence_item

from common import BaseSeq


class AHBLiteBaseSeqItem(uvm_sequence_item):
    def __init__(self, name):
        super().__init__(name)
        self.ahb_hrdata = 0
        self.ahb_hready = 0
        self.ahb_hresp = 0

    def randomize(self):
        pass

    def __eq__(self, other):
        pass

    def __str__(self):
        return self.__class__.__name__


class AHBLiteInactiveSeqItem(AHBLiteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)


class AHBLiteReadyReadSeqItem(AHBLiteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.ahb_hready = 1
        self.ahb_hresp = AHB_LITE_RESPONSE_CODES.OKAY

    def randomize(self):
        self.ahb_hrdata = random.randint(0, 255)


class AHBLiteReadyWriteSeqItem(AHBLiteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.ahb_hready = 1
        self.ahb_hresp = AHB_LITE_RESPONSE_CODES.OKAY


class AHBLiteReadyNoDataSeqItem(AHBLiteBaseSeqItem):
    def __init__(self, name):
        super().__init__(name)
        self.ahb_hready = 1
        self.ahb_hresp = AHB_LITE_RESPONSE_CODES.OKAY


class AHBLiteAcceptWriteSeq(BaseSeq):
    async def body(self):
        items = [
            AHBLiteReadyNoDataSeqItem("AHBLiteReadyNoDataSeqItem"),
            AHBLiteReadyWriteSeqItem("AHBLiteReadyWriteSeqItem"),
        ]
        await self.run_items(items)


class AHBLiteAcceptReadSeq(BaseSeq):
    async def body(self):
        items = [
            AHBLiteReadyNoDataSeqItem("AHBLiteReadyNoDataSeqItem"),
            AHBLiteReadyReadSeqItem("AHBLiteReadyReadSeqItem"),
        ]
        await self.run_items(items)
