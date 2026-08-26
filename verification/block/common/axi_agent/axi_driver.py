#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotbext.axi import AxiMaster
from pyuvm import *

from .axi_item import AxiTransaction, AxiTransactionType

__all__ = ["AxiDriver"]

# ==============================================================================


class AxiDriver(uvm_driver):
    """
    AXI master driver.

    Instantiates AxiMaster from cocotbext-axi and passes received items to it.
    """

    def __init__(self, *args, **kwargs):
        bfm_args = kwargs["bfm_args"]
        del kwargs["bfm_args"]
        self.axi_master = AxiMaster(**bfm_args)
        self.pending_writes = Event("pending writes")
        self.pending_reads = Event("pending reads")
        super().__init__(*args, **kwargs)

    async def _write_waiter(self):
        """
        Waits until pending writes finish. Clears the pending writes flag
        afterwards
        """
        self.raise_objection()
        await self.axi_master.write_if.wait()
        self.pending_writes.clear()
        self.drop_objection()

    async def _read_waiter(self):
        """
        Waits until pending reads finish. Clears the pending writes flag
        afterwards
        """
        self.raise_objection()
        await self.axi_master.read_if.wait()
        self.pending_reads.clear()
        self.drop_objection()

    async def run_phase(self):

        while True:
            item = await self.seq_item_port.get_next_item()
            assert isinstance(item, AxiTransaction), type(item)

            if item.type == AxiTransactionType.WRITE:
                kwargs = {
                    "address": item.address,
                    "data": item.data,
                    "awid": item.id,
                    "burst": item.burst,
                    "size": item.size,
                    # TODO: Other fields
                }

                if item.is_blocking:
                    item.resp = await self.axi_master.write(**kwargs)

                else:
                    item.resp = None
                    self.axi_master.init_write(**kwargs)
                    if not self.pending_writes.is_set():
                        self.pending_writes.set()
                        cocotb.start_soon(self._write_waiter())

            elif item.type == AxiTransactionType.READ:
                kwargs = {
                    "address": item.address,
                    "length": item.length,
                    "arid": item.id,
                    "burst": item.burst,
                    "size": item.size,
                    # TODO: Other fields
                }

                if item.is_blocking:
                    item.resp = await self.axi_master.read(**kwargs)

                else:
                    item.resp = None
                    self.axi_master.init_read(**kwargs)
                    if not self.pending_reads.is_set():
                        self.pending_reads.set()
                        cocotb.start_soon(self._read_waiter())

            else:
                assert False, item.type

            self.seq_item_port.item_done()
