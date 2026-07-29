#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotbext.axi import AxiMaster
from pyuvm import *

from . import AxiTransaction, AxiTransactionType

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
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            item = await self.seq_item_port.get_next_item()
            assert isinstance(item, AxiTransaction), type(item)

            if item.type == AxiTransactionType.WRITE:
                item.resp = await self.axi_master.write(
                    address=item.address,
                    data=item.data,
                    awid=item.id,
                    burst=item.burst,
                    size=item.size,
                    # TODO: Other fields
                )

            elif item.type == AxiTransactionType.READ:
                item.resp = await self.axi_master.read(
                    address=item.address,
                    length=item.length,
                    arid=item.id,
                    burst=item.burst,
                    size=item.size,
                    # TODO: Other fields
                )

            else:
                assert False, item.type

            self.seq_item_port.item_done()
