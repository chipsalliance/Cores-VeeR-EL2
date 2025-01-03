# Copyright (c) 2025 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from pyuvm import UVMQueue, utility_classes

# Is = (
#     clk_override,
#     dec_tlu_core_ecc_disable,
#     ic_rw_addr,
#     ic_wr_en,
#     ic_tag_valid,
#     ic_rd_en,
#     ic_debug_addr,
#     ic_debug_rd_en,
#     ic_debug_wr_en,
#     ic_debug_tag_array,
#     ic_debug_way,
#     ic_tag_data_raw_packed_pre,
#     ic_tag_data_raw_pre,
#     ic_debug_wr_data,
#     scan_mode,
# )

# Os = (
#     ic_tag_clken_final,
#     ic_tag_wren_q,
#     ic_tag_wren_biten_vec,
#     ic_tag_wr_data,
#     ic_rw_addr_q,
#     ictag_debug_rd_data,
#     ic_rd_hit,
#     ic_tag_perr,
# )

def onehot2id(onehot_val):
    import math
    return math.ceil(math.log2(onehot_val))

class IcTagBFM(metaclass=utility_classes.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk
        self.req_driver_q = UVMQueue(maxsize=1)
        self.rsp_monitor_q = UVMQueue()
        self.cache = CacheMemory(2)

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def drive(self):
        ICACHE_NUM_WAYS = 2
        while True:
            # if self.rst_n.value == 0:
            #     self.dut.clk_override.value = 0
            #     self.dut.dec_tlu_core_ecc_disable.value = 0
            #     self.dut.ic_rw_addr.value = 0
            #     self.dut.ic_wr_en.value = 0
            #     self.dut.ic_tag_valid.value = 0
            #     self.dut.ic_rd_en.value = 0
            #     self.dut.ic_debug_addr.value = 0
            #     self.dut.ic_debug_rd_en.value = 0
            #     self.dut.ic_debug_wr_en.value = 0
            #     self.dut.ic_debug_tag_array.value = 0
            #     self.dut.ic_debug_way.value = 0
            #     self.dut.ic_tag_data_raw_packed_pre.value = 0
            #     self.dut.ic_tag_data_raw_pre.value = 0
            #     self.dut.ic_debug_wr_data.value = 0
            #     self.dut.scan_mode.value = 0

            try:
                (
                    clk_override,
                    dec_tlu_core_ecc_disable,
                    ic_rw_addr,
                    ic_wr_en,
                    ic_tag_valid,
                    ic_rd_en,
                    ic_debug_addr,
                    ic_debug_rd_en,
                    ic_debug_wr_en,
                    ic_debug_tag_array,
                    ic_debug_way,
                    ic_tag_data_raw_packed_pre,
                    ic_tag_data_raw_pre,
                    ic_debug_wr_data,
                    scan_mode,
                ) = self.req_driver_q.get_nowait()
                self.dut.clk_override.value = clk_override
                self.dut.dec_tlu_core_ecc_disable.value = dec_tlu_core_ecc_disable
                self.dut.ic_rw_addr.value = ic_rw_addr
                self.dut.ic_wr_en.value = ic_wr_en
                self.dut.ic_tag_valid.value = ic_tag_valid
                self.dut.ic_rd_en.value = ic_rd_en
                self.dut.ic_debug_addr.value = ic_debug_addr
                self.dut.ic_debug_rd_en.value = ic_debug_rd_en
                self.dut.ic_debug_wr_en.value = ic_debug_wr_en
                self.dut.ic_debug_tag_array.value = ic_debug_tag_array
                self.dut.ic_debug_way.value = ic_debug_way
                self.dut.ic_debug_wr_data.value = ic_debug_wr_data
                self.dut.scan_mode.value = scan_mode

                await RisingEdge(self.clk)
                ic_tag_clken_final = self.dut.ic_tag_clken_final.value
                ic_tag_wren_q = self.dut.ic_tag_wren_q.value
                ic_tag_wren_biten_vec = self.dut.ic_tag_wren_biten_vec.value
                ic_tag_wr_data = self.dut.ic_tag_wr_data.value
                ic_rw_addr_q = self.dut.ic_rw_addr_q.value
                ictag_debug_rd_data = self.dut.ictag_debug_rd_data.value
                ic_rd_hit = self.dut.ic_rd_hit.value
                ic_tag_perr = self.dut.ic_tag_perr.value

                # TODO: Handle debug path
                if ic_tag_wren_q:
                    cache_way = onehot2id(ic_tag_wren_q)
                    self.cache.write(ic_rw_addr_q, cache_way, ic_tag_wr_data, ic_tag_wren_biten_vec)

                for i in range(ICACHE_NUM_WAYS):
                    self.dut.ic_tag_data_raw_pre[i].value = self.cache.read(ic_rw_addr_q, cache_way)
                self.dut.ic_tag_data_raw_packed_pre.value = self.cache.read_packed(ic_rw_addr_q)

                await RisingEdge(self.clk)

                values = (
                    clk_override,
                    dec_tlu_core_ecc_disable,
                    ic_rw_addr,
                    ic_wr_en,
                    ic_tag_valid,
                    ic_rd_en,
                    ic_debug_addr,
                    ic_debug_rd_en,
                    ic_debug_wr_en,
                    ic_debug_tag_array,
                    ic_debug_way,
                    ic_tag_data_raw_packed_pre,
                    ic_tag_data_raw_pre,
                    ic_debug_wr_data,
                    scan_mode,
                    self.dut.ic_tag_data_raw_pre.value,
                    self.dut.ic_tag_data_raw_packed_pre.value,
                    ic_tag_clken_final,
                    ic_tag_wren_q,
                    ic_tag_wren_biten_vec,
                    ic_tag_wr_data,
                    ic_rw_addr_q,
                    ictag_debug_rd_data,
                    ic_rd_hit,
                    ic_tag_perr,
                )

                await self.rsp_monitor_q.put(values)

            except QueueEmpty:
                pass

    def start_bfm(self):
        cocotb.start_soon(self.drive())


class SimpleMemory:

    def __init__(self, init_content={}):
        self.mem = init_content

    def write(self, addr, data, data_mask):
        self.mem[addr] = data & data_mask

    def read(self, addr):
        """
        Reads from uninitialized cells will return 0
        """
        if addr in self.mem:
            return self.mem[addr]
        else:
            return 0


class CacheMemory:

    def __init__(self, N):
        self.cache = [SimpleMemory() for i in range(N)]

    def read(self, addr, n):
        return self.cache[n].read(addr)

    def write(self, addr, n, data, mask):
        """
        Mask is provided as packed
        """
        unpacked_mask = (mask >> 26 * n) & 0x3FF_FFFF
        self.cache[n].write(addr, data, unpacked_mask)

    def read_packed(self, addr):
        """
        Assumes that data is 26 bits wide
        """
        packed_data = 0
        for i in len(self.cache):
            packed_data |= self.cache[i].read(addr) << 26 * i
