# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import math
import os
import random
import struct

import pyuvm
from axi import Axi4LiteMonitor, BusReadItem, BusWriteItem
from cocotb.clock import Clock
from cocotb.triggers import (
    ClockCycles,
    Event,
    FallingEdge,
    First,
    Lock,
    RisingEdge,
    Timer,
)
from pyuvm import *
from utils import collect_bytes, collect_signals

# ==============================================================================


class MemWriteItem(uvm_sequence_item):
    """
    A generic memory bus write item
    """

    def __init__(self, mem, addr, data, size=64, resp=None):
        super().__init__("MemWriteItem")
        self.mem = mem
        self.addr = addr
        self.data = data
        self.size = size
        self.resp = resp


class MemReadItem(uvm_sequence_item):
    """
    A generic memory bus read item
    """

    def __init__(self, mem, addr, data, size=64, resp=None):
        super().__init__("MemReadItem")
        self.mem = mem
        self.addr = addr
        self.data = data
        self.size = size
        self.resp = resp


class DebugWriteItem(uvm_sequence_item):
    """
    A debug bus write item
    """

    def __init__(self, addr, data, size=32, fail=False):
        super().__init__("DebugWriteItem")
        self.addr = addr
        self.data = data
        self.size = size
        self.fail = fail


class DebugReadItem(uvm_sequence_item):
    """
    A debug bus read item
    """

    def __init__(self, addr, data=None, size=32, fail=False):
        super().__init__("DebugReadItem")
        self.addr = addr
        self.data = data
        self.size = size
        self.fail = fail


# ==============================================================================


class CoreMemoryBFM(uvm_component):
    """
    A BFM for the memory side interface of the DMA module
    """

    SIGNALS = [
        "clk",
        "dma_dccm_req",
        "dma_iccm_req",
        "dma_mem_tag",
        "dma_mem_addr",
        "dma_mem_sz",
        "dma_mem_write",
        "dma_mem_wdata",
        "dccm_dma_rvalid",
        "dccm_dma_ecc_error",
        "dccm_dma_rtag",
        "dccm_dma_rdata",
        "iccm_dma_rvalid",
        "iccm_dma_ecc_error",
        "iccm_dma_rtag",
        "iccm_dma_rdata",
        "dccm_ready",
        "iccm_ready",
    ]

    def __init__(self, name, parent, uut):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

        # Memory content
        self.iccm_data = dict()
        self.dccm_data = dict()

    def build_phase(self):
        # Get base addresses and sizes
        self.iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        self.dccm_base = ConfigDB().get(None, "", "DCCM_BASE")

        self.iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")
        self.dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        # Get parameters
        self.iccm_busy = ConfigDB().get(self, "", "ICCM_BUSY_PROB")
        self.dccm_busy = ConfigDB().get(self, "", "DCCM_BUSY_PROB")

        self.busy_range = (
            ConfigDB().get(self, "", "MEM_BUSY_MIN"),
            ConfigDB().get(self, "", "MEM_BUSY_MAX"),
        )

        self.ecc_err_rate = ConfigDB().get(self, "", "ECC_ERROR_RATE")

    async def iccm_busy_task(self):
        """
        A task that randomly makes ICCM busy
        """

        while True:
            await RisingEdge(self.clk)

            # Become busy at random for a random cycle count
            if random.random() < self.iccm_busy:
                self.iccm_ready.value = 0

                n = random.randrange(*self.busy_range)
                await ClockCycles(self.clk, n)

                self.iccm_ready.value = 1

    async def dccm_busy_task(self):
        """
        A task that randomly makes DCCM busy
        """

        while True:
            await RisingEdge(self.clk)

            # Become busy at random for a random cycle count
            if random.random() < self.dccm_busy:
                self.dccm_ready.value = 0

                n = random.randrange(*self.busy_range)
                await ClockCycles(self.clk, n)

                self.dccm_ready.value = 1

    async def responder(self):
        """
        A task for handling read / write responses
        """

        while True:
            await RisingEdge(self.clk)

            # Sample signals
            tag = int(self.dma_mem_tag)

            # DCCM access
            if self.dma_dccm_req.value:
                # Decode and check address
                addr = int(self.dma_mem_addr.value) - self.dccm_base
                assert addr >= 0 and addr < self.dccm_size

                # Write / read
                if self.dma_mem_write.value:
                    self.dccm_data[addr] = int(self.dma_mem_wdata.value)

                else:
                    if addr not in self.dccm_data:
                        self.dccm_data[addr] = random.randrange(0, (1 << 64) - 1)

                    self.dccm_dma_rdata.value = self.dccm_data[addr]
                    self.dccm_dma_rtag.value = tag
                    self.dccm_dma_rvalid.value = 1
                    self.dccm_dma_ecc_error.value = random.random() < self.ecc_err_rate

                await RisingEdge(self.clk)
                self.dccm_dma_rvalid.value = 0

            # ICCM access
            elif self.dma_iccm_req.value:
                # Decode and check address
                addr = int(self.dma_mem_addr.value) - self.iccm_base
                assert addr >= 0 and addr < self.iccm_size

                # Write / read
                if self.dma_mem_write.value:
                    self.iccm_data[addr] = int(self.dma_mem_wdata.value)

                else:
                    if addr not in self.iccm_data:
                        self.iccm_data[addr] = random.randrange(0, (1 << 64) - 1)

                    self.iccm_dma_rdata.value = self.iccm_data[addr]
                    self.iccm_dma_rtag.value = tag
                    self.iccm_dma_rvalid.value = 1
                    self.iccm_dma_ecc_error.value = random.random() < self.ecc_err_rate

                await RisingEdge(self.clk)
                self.iccm_dma_rvalid.value = 0

    async def run_phase(self):
        # Initially make ICCM and DCCM ready
        self.iccm_ready.value = 1
        self.dccm_ready.value = 1

        # Start tasks
        cocotb.start_soon(self.iccm_busy_task())
        cocotb.start_soon(self.dccm_busy_task())
        cocotb.start_soon(self.responder())


class CoreMemoryMonitor(uvm_component):
    """
    A monitor for ICCM / DCCM interface
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

        # Get base addresses
        self.iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        self.dccm_base = ConfigDB().get(None, "", "DCCM_BASE")

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        req_pending = False

        while True:
            await RisingEdge(self.bfm.clk)

            # Monitor reads which happen one cycle after a request
            if req_pending and not req_wr:
                if is_iccm:
                    addr = req_addr - self.iccm_base
                    data = int(self.bfm.iccm_dma_rdata.value)
                    resp = int(self.bfm.iccm_dma_ecc_error.value)
                    self.ap.write(MemReadItem("ICCM", addr, data, req_size, resp))
                    self.logger.debug("ICCM RD: 0x{:08X} 0x{:016X} {}".format(addr, data, resp))

                if is_dccm:
                    addr = req_addr - self.dccm_base
                    data = int(self.bfm.dccm_dma_rdata.value)
                    resp = int(self.bfm.dccm_dma_ecc_error.value)
                    self.ap.write(MemReadItem("DCCM", addr, data, req_size, resp))
                    self.logger.debug("DCCM RD: 0x{:08X} 0x{:016X} {}".format(addr, data, resp))

            req_pending = False

            # We have a request
            is_iccm = self.bfm.dma_iccm_req.value
            is_dccm = self.bfm.dma_dccm_req.value

            if is_iccm or is_dccm:
                req_pending = True

                req_addr = int(self.bfm.dma_mem_addr.value)
                req_data = int(self.bfm.dma_mem_wdata.value)
                req_wr = int(self.bfm.dma_mem_write.value)
                req_size = int(self.bfm.dma_mem_sz.value)

                # Writes
                if req_wr and is_iccm:
                    addr = req_addr - self.iccm_base
                    self.ap.write(MemWriteItem("ICCM", addr, req_data, req_size))
                    self.logger.debug("ICCM WR: 0x{:08X} 0x{:016X}".format(addr, req_data))

                if req_wr and is_dccm:
                    addr = req_addr - self.dccm_base
                    self.ap.write(MemWriteItem("DCCM", addr, req_data, req_size))
                    self.logger.debug("DCCM WR: 0x{:08X} 0x{:016X}".format(addr, req_data))


# ==============================================================================


class Axi4LiteBFM(uvm_component):
    """
    A bus functional model for AXI4 Lite subordinate port.

    Does support multi-transfer transactions, supports overlapped transactions
    for writes
    """

    SIGNALS = [
        "clk",
        "rst",
        "awvalid",
        "awready",
        "awid",
        "awaddr",
        "awsize",
        "wvalid",
        "wready",
        "wdata",
        "wstrb",
        "bvalid",
        "bready",
        "bresp",
        "bid",
        "arvalid",
        "arready",
        "arid",
        "araddr",
        "arsize",
        "rvalid",
        "rready",
        "rid",
        "rdata",
        "rresp",
        "rlast",
    ]

    class Transfer:
        """
        Represents a pending AXI transfer
        """

        def __init__(self, tid):
            self.tid = tid
            self.addr = None
            self.data = None

            self.pending = False

    def __init__(self, name, parent, uut, signal_map):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(
            self.SIGNALS, uut, self, uut_prefix="dma_axi_", obj_prefix="axi_", signal_map=signal_map
        )

        # Determine bus parameters
        self.awidth = len(self.axi_awaddr)
        self.dwidth = len(self.axi_wdata)
        self.swidth = len(self.axi_wstrb)

        assert self.swidth == (self.dwidth // 8)

        self.logger.debug("AXI4 Lite BFM:")
        self.logger.debug(" awidth = {}".format(self.awidth))
        self.logger.debug(" dwidth = {}".format(self.dwidth))
        self.logger.debug(" swidth = {}".format(self.swidth))

        self.xfer_lock = Lock()

        self.wr_xfers = {i: self.Transfer(i) for i in range(1 << len(self.axi_awid))}

    async def _wait(self, signal, max_cycles=200):
        """
        Waits for a signal to be asserted for at most max_cycles.
        Raises an exception if it does not
        """
        for i in range(max_cycles):
            await RisingEdge(self.axi_clk)
            if signal.value != 0:
                break
        else:
            raise RuntimeError("{} timeout".format(str(signal)))

    async def write(self, addr, data):
        """
        Issues a write transfer, does not wait until it completes
        """

        # Wait for a free transfer id
        while True:
            await RisingEdge(self.axi_clk)

            async with self.xfer_lock:
                awid = None
                for tid, xfr in self.wr_xfers.items():
                    if not xfr.pending:
                        awid = tid
                        break

                if awid is not None:
                    xfer = self.wr_xfers[awid]
                    xfer.pending = True
                    xfer.addr = addr
                    xfer.data = data
                    break

        # Send write request
        await self._wait(self.axi_awready)
        self.axi_awvalid.value = 1
        self.axi_awaddr.value = addr
        self.axi_awid.value = awid
        self.axi_awsize.value = int(math.ceil(math.log2(self.dwidth)))

        await RisingEdge(self.axi_clk)
        self.axi_awvalid.value = 0

        # Send data
        data_len = len(data)
        data_ptr = 0
        while data_len > 0:
            # Wait for ready
            await self._wait(self.axi_wready)
            self.axi_wvalid.value = 1

            # Get data
            xfer_len = min(self.swidth, data_len)
            xfer_data = data[data_ptr : data_ptr + xfer_len]
            data_ptr += xfer_len
            data_len -= xfer_len

            # Assert data
            wdata = 0
            wstrb = 0
            for i in range(xfer_len):
                wdata <<= 8
                wstrb <<= 1

                wdata |= xfer_data[-(1 + i)]
                wstrb |= 1

            self.axi_wdata.value = wdata
            self.axi_wstrb.value = wstrb

        # Wait for the last ready
        await self._wait(self.axi_wready)

        # Deassert wvalid
        self.axi_wvalid.value = 0

    async def write_handler(self):
        """
        A handler for write transfer completion
        """

        # Accept responses
        self.axi_bready.value = 1

        while True:
            # Wait for response
            await RisingEdge(self.axi_clk)
            if not self.axi_bvalid.value:
                continue

            bresp = int(self.axi_bresp.value)
            bid = int(self.axi_bid.value)

            # Find a pending transfer
            async with self.xfer_lock:
                xfer = self.wr_xfers.get(bid, None)
                if not xfer:
                    self.logger.error("Write response for a non-pending tid {}".format(bid))
                    continue

                xfer.pending = False

                addr = xfer.addr
                data = xfer.data

            self.logger.debug(
                "WR: 0x{:08X} {} 0b{:03b}".format(addr, ["0x{:02X}".format(b) for b in data], bresp)
            )

    async def read(self, addr, data):
        """
        Issues a read transfer and waits for its completion
        """

        # Send read request
        await self._wait(self.axi_awready)
        self.axi_arvalid.value = 1
        self.axi_araddr.value = addr
        self.axi_arid.value = 1
        self.axi_arsize.value = int(math.ceil(math.log2(self.dwidth)))

        await RisingEdge(self.axi_clk)
        self.axi_arvalid.value = 0

        # Receive data
        self.axi_rready.value = 1

        data = bytearray()
        rresp = None

        while True:
            # Wait for valid
            await self._wait(self.axi_rvalid)

            # Get the data
            data.extend(collect_bytes(self.axi_rdata))

            # Last, finish reception
            if self.axi_rlast.value:
                break

        self.axi_rready.value = 0
        rresp = int(self.axi_rresp.value)

        self.logger.debug(
            "RD: 0x{:08X} {} 0b{:03b}".format(addr, ["0x{:02X}".format(b) for b in data], rresp)
        )

        return bytes(data), rresp

    async def run_phase(self):
        # Start read & write handlers
        cocotb.start_soon(self.write_handler())


# ==============================================================================


class Axi4LiteSubordinateDriver(uvm_driver):
    """
    A driver component for AXI4 lite subordinate ports. Acts as an AXI Manager.
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                await self.bfm.write(it.addr, it.data)

            elif isinstance(it, BusReadItem):
                # FIXME: Assuming that all read requests are 64-bit wide
                await self.bfm.read(it.addr, 8)

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


# ==============================================================================


class DebugInterfaceBFM(uvm_component):
    """
    A DFM for DMA debug interface
    """

    SIGNALS = [
        "clk",
        "dbg_cmd_addr",
        "dbg_cmd_wrdata",
        "dbg_cmd_valid",
        "dbg_cmd_write",
        "dbg_cmd_type",
        "dbg_cmd_size",
        "dbg_dma_bubble",
        "dma_dbg_ready",
        "dma_dbg_cmd_done",
        "dma_dbg_cmd_fail",
        "dma_dbg_rddata",
    ]

    def __init__(self, name, parent, uut):
        super().__init__(name, parent)

        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

    def build_phase(self):
        self.busy_prob = ConfigDB().get(self, "", "DBG_BUSY_PROB")
        self.busy_range = (
            ConfigDB().get(self, "", "DBG_BUSY_MIN"),
            ConfigDB().get(self, "", "DBG_BUSY_MAX"),
        )

    async def _wait(self, signal, max_cycles=150):
        """
        Waits for a signal to be asserted for at most max_cycles.
        Raises an exception if it does not
        """
        for i in range(max_cycles):
            await RisingEdge(self.clk)
            if signal.value != 0:
                break
        else:
            raise RuntimeError("{} timeout".format(str(signal)))

    async def write(self, addr, data):
        """
        Performs a debug interface write. Waits for completion and returns
        status code
        """

        # Wait for ready
        await self._wait(self.dma_dbg_ready)

        # Issue the command
        self.dbg_cmd_valid.value = 1
        self.dbg_cmd_write.value = 1
        self.dbg_cmd_size.value = 2  # Apparently 0=8, 1=16, 2=32
        self.dbg_cmd_addr.value = addr
        self.dbg_cmd_wrdata.value = struct.unpack("<I", data)[0]

        await RisingEdge(self.clk)

        self.dbg_cmd_valid.value = 0

        # Wait for done
        await self._wait(self.dma_dbg_cmd_done)

        return int(self.dma_dbg_cmd_fail.value)

    async def read(self, addr):
        """
        Performs a debug interface write. Waits for completion and returns
        data and status code
        """

        # Wait for ready
        await self._wait(self.dma_dbg_ready)

        # Issue the command
        self.dbg_cmd_valid.value = 1
        self.dbg_cmd_write.value = 0
        self.dbg_cmd_size.value = 2  # Apparently 0=8, 1=16, 2=32
        self.dbg_cmd_addr.value = addr

        await RisingEdge(self.clk)

        self.dbg_cmd_valid.value = 0

        # Wait for done
        await self._wait(self.dma_dbg_cmd_done)

        return struct.pack("<I", self.dma_dbg_rddata.value), int(self.dma_dbg_cmd_fail.value)

    async def run_phase(self):
        """
        The run phase implements a loop that randomly deasserts the pipeline
        bubble mark to block debug requests.
        """

        # The only supported dbg_cmd_type is 2 (memory)
        self.dbg_cmd_type.value = 2
        # Permanently mark the pipeline bubble TODO: Randomize that
        self.dbg_dma_bubble.value = 1

        # Main loop
        while True:
            await RisingEdge(self.clk)

            # Become busy at random for a random cycle count by deasserting
            # the bubble mark
            if random.random() < self.busy_prob:
                self.dbg_dma_bubble.value = 0

                n = random.randrange(*self.busy_range)
                await ClockCycles(self.clk, n)

                self.dbg_dma_bubble.value = 1


# ==============================================================================


class DebugInterfaceDriver(uvm_driver):
    """
    A driver for the DMA debug interface
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                it.resp = await self.bfm.write(it.addr, it.data)
            elif isinstance(it, BusReadItem):
                it.data, it.resp = await self.bfm.read(it.addr)

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class DebugInterfaceMonitor(uvm_component):
    """
    A monitor for the DMA debug interface
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        pending = 0
        prev_rdy = 0
        curr_rdy = 0

        while True:
            await RisingEdge(self.bfm.clk)

            # FIXME: It appears that when ready gets deasserted on the same
            # clock edge where valid gets asserted the module accepts the
            # command while it should not. The code below stretches the
            # ready by 1 clock cycle
            prev_rdy = curr_rdy
            curr_rdy = self.bfm.dma_dbg_ready.value

            # Sample request data on ready & valid.
            is_rdy = prev_rdy or curr_rdy
            if is_rdy and self.bfm.dbg_cmd_valid.value:
                cmd_addr = int(self.bfm.dbg_cmd_addr.value)
                cmd_write = int(self.bfm.dbg_cmd_write.value)
                cmd_type = int(self.bfm.dbg_cmd_type.value)
                cmd_size = int(self.bfm.dbg_cmd_size.value)
                cmd_wrdata = int(self.bfm.dbg_cmd_wrdata.value)

                pending += 1

                # Map size to bits
                cmd_size = 8 * (1 << cmd_size)

            # Sample read data and send item on done
            if self.bfm.dma_dbg_cmd_done.value:
                cmd_rddata = int(self.bfm.dma_dbg_rddata.value)
                cmd_fail = int(self.bfm.dma_dbg_cmd_fail.value)

                # No pending transfer
                if not pending:
                    self.logger.error("dma_dbg_cmd_done == 1 but there was not valid request")
                    continue

                pending -= 1

                # The module supports only type = 0x2 (memory)
                if cmd_type != 0x2:
                    self.logger.error("dma_cmd_type != 0x2")
                    continue

                # Write
                if cmd_write:
                    item = DebugWriteItem(cmd_addr, cmd_wrdata, cmd_size, cmd_fail)
                    self.ap.write(item)

                    self.logger.debug(
                        "WR: 0x{:08X}: 0x{:08X} ({}){}".format(
                            cmd_addr, cmd_wrdata, cmd_size, "" if not cmd_fail else " failed!"
                        )
                    )

                # Read
                else:
                    item = DebugReadItem(cmd_addr, cmd_rddata, cmd_size, cmd_fail)
                    self.ap.write(item)

                    self.logger.debug(
                        "RD: 0x{:08X}: 0x{:08X} ({}){}".format(
                            cmd_addr, cmd_rddata, cmd_size, "" if not cmd_fail else " failed!"
                        )
                    )


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 10)
        ConfigDB().set(None, "*", "TEST_BURST_LEN", 10)
        ConfigDB().set(None, "*", "TEST_BURST_GAP", 10)

        # ICCM and DCCM addresses / sizes are taken from the default VeeR
        # config.
        ConfigDB().set(None, "*", "ICCM_BASE", 0xEE000000)
        ConfigDB().set(None, "*", "DCCM_BASE", 0xF0040000)
        ConfigDB().set(None, "*", "PIC_BASE", 0xF00C0000)

        ConfigDB().set(None, "*", "ICCM_SIZE", 0x10000)
        ConfigDB().set(None, "*", "DCCM_SIZE", 0x10000)
        ConfigDB().set(None, "*", "PIC_SIZE", 0x20)

        ConfigDB().set(None, "*", "ADDR_ALIGN", len(cocotb.top.dma_axi_wdata) // 8)

        # Sequencers
        self.axi_seqr = uvm_sequencer("axi_seqr", self)
        self.dbg_seqr = uvm_sequencer("dbg_seqr", self)

        # AXI interface
        self.axi_bfm = Axi4LiteBFM(
            "axi_bfm",
            self,
            uut=cocotb.top,
            signal_map={
                "clk": "clk",
                "rst": "rst_l",
            },
        )

        self.axi_drv = Axi4LiteSubordinateDriver("axi_drv", self, bfm=self.axi_bfm)
        self.axi_mon = Axi4LiteMonitor("axi_mon", self, bfm=self.axi_bfm)

        # Debug interface
        self.dbg_bfm = DebugInterfaceBFM("dbg_bfm", self, cocotb.top)
        self.dbg_drv = DebugInterfaceDriver("dbg_drv", self, bfm=self.dbg_bfm)
        self.dbg_mon = DebugInterfaceMonitor("dbg_mon", self, bfm=self.dbg_bfm)

        # Core side memory port
        self.mem_bfm = CoreMemoryBFM("mem_bfm", self, cocotb.top)
        self.mem_mon = CoreMemoryMonitor("mem_mon", self, bfm=self.mem_bfm)

        # Component config
        ConfigDB().set(self.mem_bfm, "", "ICCM_BUSY_PROB", 0.05)
        ConfigDB().set(self.mem_bfm, "", "DCCM_BUSY_PROB", 0.05)

        ConfigDB().set(self.mem_bfm, "", "MEM_BUSY_MIN", 10)
        ConfigDB().set(self.mem_bfm, "", "MEM_BUSY_MAX", 25)

        ConfigDB().set(self.mem_bfm, "", "ECC_ERROR_RATE", 0.0)

        ConfigDB().set(self.dbg_bfm, "", "DBG_BUSY_PROB", 0.05)
        ConfigDB().set(self.dbg_bfm, "", "DBG_BUSY_MIN", 10)
        ConfigDB().set(self.dbg_bfm, "", "DBG_BUSY_MAX", 25)

    def connect_phase(self):
        self.axi_drv.seq_item_port.connect(self.axi_seqr.seq_item_export)
        self.dbg_drv.seq_item_port.connect(self.dbg_seqr.seq_item_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Syncrhonize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self):
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("free_clk")

        # Enable clock
        cocotb.top.dma_bus_clk_en.value = 1

        # Issue reset
        await self.do_reset()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
