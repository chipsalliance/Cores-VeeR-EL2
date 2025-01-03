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
        self.rsp_driver_q = UVMQueue(maxsize=1)
        self.rsp_monitor_q = UVMQueue()
        self.cache = CacheMemory(2)

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def drive(self):
        while True:
            if self.rst_n.value == 0:
                self.dut.clk_override.value = 0
                self.dut.dec_tlu_core_ecc_disable.value = 0
                self.dut.ic_rw_addr.value = 0
                self.dut.ic_wr_en.value = 0
                self.dut.ic_tag_valid.value = 0
                self.dut.ic_rd_en.value = 0
                self.dut.ic_debug_addr.value = 0
                self.dut.ic_debug_rd_en.value = 0
                self.dut.ic_debug_wr_en.value = 0
                self.dut.ic_debug_tag_array.value = 0
                self.dut.ic_debug_way.value = 0
                self.dut.ic_tag_data_raw_packed_pre.value = 0
                self.dut.ic_tag_data_raw_pre.value = 0
                self.dut.ic_debug_wr_data.value = 0
                self.dut.scan_mode.value = 0
                await RisingEdge(self.rst_n)
                await RisingEdge(self.clk)
            try:
                item = await self.req_driver_q.get()

                # Drive inputs
                self.dut.clk_override.value = item.clk_override
                self.dut.dec_tlu_core_ecc_disable.value = item.dec_tlu_core_ecc_disable
                self.dut.ic_rw_addr.value = item.ic_rw_addr
                self.dut.ic_wr_en.value = item.ic_wr_en
                self.dut.ic_tag_valid.value = item.ic_tag_valid
                self.dut.ic_rd_en.value = item.ic_rd_en
                self.dut.ic_debug_addr.value = item.ic_debug_addr
                self.dut.ic_debug_rd_en.value = item.ic_debug_rd_en
                self.dut.ic_debug_wr_en.value = item.ic_debug_wr_en
                self.dut.ic_debug_tag_array.value = item.ic_debug_tag_array
                self.dut.ic_debug_way.value = item.ic_debug_way
                self.dut.ic_debug_wr_data.value = item.ic_debug_wr_data
                self.dut.scan_mode.value = item.scan_mode

                # Read outputs
                ic_tag_clken_final = int(self.dut.ic_tag_clken_final.value)
                ic_tag_wren_q = int(self.dut.ic_tag_wren_q.value)
                ic_tag_wren_biten_vec = int(self.dut.ic_tag_wren_biten_vec.value)
                ic_tag_wr_data = int(self.dut.ic_tag_wr_data.value)
                ic_rw_addr_q = int(self.dut.ic_rw_addr_q.value)
                ictag_debug_rd_data = int(self.dut.ictag_debug_rd_data.value)
                ic_rd_hit = int(self.dut.ic_rd_hit.value)
                ic_tag_perr = int(self.dut.ic_tag_perr.value)

                # Write to cache model
                if ic_tag_wren_q:
                    cache_way = onehot2id(ic_tag_wren_q)
                    self.cache.write(ic_rw_addr_q, cache_way, ic_tag_wr_data, ic_tag_wren_biten_vec)

                # Read from cache
                # Cocotb+Verilator auto-pack the ic_tag_data_raw_pre signal
                self.dut.ic_tag_data_raw_pre.value = self.cache.read_packed(ic_rw_addr_q)
                self.dut.ic_tag_data_raw_packed_pre.value = self.cache.read_packed(ic_rw_addr_q)

                await RisingEdge(self.clk)

                values = (
                    item.clk_override,
                    item.dec_tlu_core_ecc_disable,
                    item.ic_rw_addr,
                    item.ic_wr_en,
                    item.ic_tag_valid,
                    item.ic_rd_en,
                    item.ic_debug_addr,
                    item.ic_debug_rd_en,
                    item.ic_debug_wr_en,
                    item.ic_debug_tag_array,
                    item.ic_debug_way,
                    item.ic_tag_data_raw_packed_pre,
                    item.ic_tag_data_raw_pre,
                    item.ic_debug_wr_data,
                    item.scan_mode,
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

                self.rsp_monitor_q.put_nowait(values)

                # Signal item done
                await self.rsp_driver_q.put("")
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
        self.cache = [SimpleMemory(init_content={0:0x1000+i, 1:0x1004+i}) for i in range(N)]

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
        for i in range(len(self.cache)):
            packed_data |= self.cache[i].read(addr) << 26 * i
        return packed_data
