# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
from cocotb.triggers import ClockCycles, FallingEdge, Timer
from pyuvm import uvm_sequence_item, uvm_sequence, ConfigDB

# Is = (
# clk_override,
# dec_tlu_core_ecc_disable,
# ic_rw_addr,
# ic_wr_en,
# ic_tag_valid,
# ic_rd_en,
# ic_debug_addr,
# ic_debug_rd_en,
# ic_debug_wr_en,
# ic_debug_tag_array,
# ic_debug_way,
# ic_tag_data_raw_packed_pre,
# ic_tag_data_raw_pre,
# ic_debug_wr_data,
# scan_mode
# )


# Os = (
# ic_tag_clken_final,
# ic_tag_wren_q,
# ic_tag_wren_biten_vec,
# ic_tag_wr_data,
# ic_rw_addr_q,
# ictag_debug_rd_data,
# ic_rd_hit,
# ic_tag_perr
# )

class IcTagBaseSeqItem(uvm_sequence_item):
    def __init__(self, name):
        super().__init__(name)
        self.clk_override = 0
        self.dec_tlu_core_ecc_disable = 0
        self.ic_rw_addr = 0
        self.ic_wr_en = 0
        self.ic_tag_valid = 0
        self.ic_rd_en = 0
        self.ic_debug_addr = 0
        self.ic_debug_rd_en = 0
        self.ic_debug_wr_en = 0
        self.ic_debug_tag_array = 0
        self.ic_debug_way = 0
        self.ic_tag_data_raw_packed_pre = 0
        self.ic_tag_data_raw_pre = 0
        self.ic_debug_wr_data = 0
        self.scan_mode = 0
        # self.ic_tag_clken_final = 0
        # self.ic_tag_wren_q = 0
        # self.ic_tag_wren_biten_vec = 0
        # self.ic_tag_wr_data = 0
        # self.ic_rw_addr_q = 0
        # self.ictag_debug_rd_data = 0
        # self.ic_rd_hit = 0
        # self.ic_tag_perr = 0

    def randomize(self):
        self.clk_override = random.randint(0, 1)
        self.dec_tlu_core_ecc_disable = random.randint(0, 1)
        self.ic_rw_addr = random.randint(0, 1)
        self.ic_wr_en = random.randint(0, 1)
        self.ic_tag_valid = random.randint(0, 1)
        self.ic_rd_en = random.randint(0, 1)
        self.ic_debug_addr = random.randint(0, 1)
        self.ic_debug_rd_en = random.randint(0, 1)
        self.ic_debug_wr_en = random.randint(0, 1)
        self.ic_debug_tag_array = random.randint(0, 1)
        self.ic_debug_way = random.randint(0, 1)
        self.ic_tag_data_raw_packed_pre = random.randint(0, 1)
        self.ic_tag_data_raw_pre = random.randint(0, 1)
        self.ic_debug_wr_data = random.randint(0, 1)
        self.scan_mode = random.randint(0, 1)

    def __eq__(self, other):
        pass

    def __str__(self):
        return self.__class__.__name__


class IcTagBasicSeq(uvm_sequence):
    async def body(self):
        items = [IcTagBaseSeqItem("first"), IcTagBaseSeqItem("second")]
        await self.run_items(items)


class Sequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        await Timer(100, "ns")
        # seq = IcTagBasicSeq()
        # seqr = ConfigDB().get(None, "", "seqr")
        # await seq.start(seqr)
