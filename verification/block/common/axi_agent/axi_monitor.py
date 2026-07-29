#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotb.queue import QueueEmpty
from cocotb.triggers import First
from cocotb.utils import get_sim_time
from cocotbext.axi.axi_channels import (
    AxiARMonitor,
    AxiAWMonitor,
    AxiBMonitor,
    AxiRMonitor,
    AxiWMonitor,
)
from pyuvm import *

from .axi_item import *

__all__ = ["AxiWriteMonitor", "AxiReadMonitor", "AxiMonitor"]

# ==============================================================================


class AxiWriteMonitor(uvm_monitor):
    """
    AXI Write channels monitor
    """

    def __init__(self, *args, **kwargs):
        self.bfm_args = kwargs["bfm_args"]
        del kwargs["bfm_args"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        bus = self.bfm_args["bus"]
        args = self.bfm_args.copy()

        # Create monitors, connect them to relevant buses
        args["bus"] = bus.write.aw
        self.aw_mon = AxiAWMonitor(**args)

        args["bus"] = bus.write.w
        self.w_mon = AxiWMonitor(**args)

        args["bus"] = bus.write.b
        self.b_mon = AxiBMonitor(**args)

        self.aw_ap = uvm_analysis_port("aw_ap", self)  # AW
        self.w_ap = uvm_analysis_port("w_ap", self)  # W
        self.b_ap = uvm_analysis_port("b_ap", self)  # B
        self.tr_ap = uvm_analysis_port("tr_ap", self)  # Transactions

    async def run_phase(self):
        pending = dict()
        current = None
        w_items = []

        while True:

            # Wait for any monitor to receive something
            await First(
                self.aw_mon.active_event.wait(),
                self.w_mon.active_event.wait(),
                self.b_mon.active_event.wait(),
            )

            # Get timestamp. FIXME: This may be off from the actual item
            # reported by a cocotbext-axi monitor
            timestamp = get_sim_time(units="ps")

            # Got AW
            try:
                aw_item = self.aw_mon.recv_nowait()
                self.logger.debug(str(aw_item))

                aw_uvm_item = AxiAWItem(aw_item, timestamp)
                self.aw_ap.write(aw_uvm_item)

                # Create a new pending transaction
                tr = AxiWriteTransaction()
                tr.aw = aw_uvm_item

                # Append any previously connected W items
                tr.w = w_items
                w_items = []

                # Store the transaction
                awid = int(aw_item.awid)
                if awid not in pending:
                    pending[awid] = []

                pending[awid].append(tr)
                current = tr

            except QueueEmpty:
                pass

            # Got W
            try:
                w_item = self.w_mon.recv_nowait()
                self.logger.debug(str(w_item))

                w_uvm_item = AxiWItem(w_item, timestamp)
                self.w_ap.write(w_uvm_item)

                if current is None:
                    w_items.append(w_uvm_item)
                else:
                    current.w.append(w_uvm_item)

            except QueueEmpty:
                pass

            # Got B
            try:
                b_item = self.b_mon.recv_nowait()
                self.logger.debug(str(b_item))

                b_uvm_item = AxiBItem(b_item, timestamp)
                self.b_ap.write(b_uvm_item)

                # Find pending transaction
                bid = int(b_item.bid)
                trs = pending.get(bid, None)
                if not trs:
                    self.logger.error(f"No pending transaction for BID {b_item.bid}")

                else:
                    # Remove the transaction from the pending list
                    tr = trs.pop(0)
                    if len(trs) == 0:
                        del pending[bid]

                    # Finalize and send the transaction item
                    tr.b = b_uvm_item
                    self.logger.debug(str(tr))
                    self.tr_ap.write(tr)

            except QueueEmpty:
                pass


# ==============================================================================


class AxiReadMonitor(uvm_monitor):
    """
    AXI Read channels monitor
    """

    def __init__(self, *args, **kwargs):
        self.bfm_args = kwargs["bfm_args"]
        del kwargs["bfm_args"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        bus = self.bfm_args["bus"]
        args = self.bfm_args.copy()

        # Create monitors, connect them to relevant buses
        args["bus"] = bus.read.ar
        self.ar_mon = AxiARMonitor(**args)

        args["bus"] = bus.read.r
        self.r_mon = AxiRMonitor(**args)

        self.ar_ap = uvm_analysis_port("ar_ap", self)  # AR
        self.r_ap = uvm_analysis_port("r_ap", self)  # R
        self.tr_ap = uvm_analysis_port("tr_ap", self)  # Transactions

    async def run_phase(self):
        pending = dict()

        while True:

            # Wait for any monitor to receive something
            await First(self.ar_mon.active_event.wait(), self.r_mon.active_event.wait())

            # Get timestamp. FIXME: This may be off from the actual item
            # reported by a cocotbext-axi monitor
            timestamp = get_sim_time(units="ps")

            # Got AR
            try:
                ar_item = self.ar_mon.recv_nowait()
                self.logger.debug(str(ar_item))

                ar_uvm_item = AxiAWItem(ar_item, timestamp)
                self.ar_ap.write(ar_uvm_item)

                # Create a new pending transaction
                tr = AxiReadTransaction()
                tr.ar = ar_uvm_item

                # Store the transaction
                arid = int(ar_item.arid)
                if arid not in pending:
                    pending[arid] = []

                pending[arid].append(tr)

            except QueueEmpty:
                pass

            # Got R
            try:
                r_item = self.r_mon.recv_nowait()
                self.logger.debug(str(r_item))

                r_uvm_item = AxiRItem(r_item, timestamp)
                self.r_ap.write(r_uvm_item)

                # Find pending transaction
                rid = int(r_item.rid)
                trs = pending.get(rid, None)
                if not trs:
                    self.logger.error(f"No pending transaction for RID {b_item.rid}")

                else:

                    # Append response item
                    tr = trs[0]
                    tr.r.append(r_uvm_item)

                    # Last item, finalize the transaction
                    if r_item.rlast == 1:

                        # Remove the transaction from the pending list
                        trs.pop(0)
                        if len(trs) == 0:
                            del pending[rid]

                        # Send the transaction item
                        self.logger.debug(str(tr))
                        self.tr_ap.write(tr)

            except QueueEmpty:
                pass


# ==============================================================================


class AxiMonitor(uvm_monitor, uvm_export_base):
    """
    AXI bus monitor
    """

    def __init__(self, *args, **kwargs):
        self.bfm_args = kwargs["bfm_args"]
        del kwargs["bfm_args"]
        super().__init__(*args, **kwargs)

    def build_phase(self):

        # Create monitors
        self.wr_mon = AxiWriteMonitor("WriteMonitor", self, bfm_args=self.bfm_args)
        self.rd_mon = AxiReadMonitor("ReadMonitor", self, bfm_args=self.bfm_args)

        # Create ports
        self.aw_ap = uvm_analysis_port("aw_ap", self)  # AW
        self.w_ap = uvm_analysis_port("w_ap", self)  # W
        self.b_ap = uvm_analysis_port("b_ap", self)  # B
        self.ar_ap = uvm_analysis_port("ar_ap", self)  # AR
        self.r_ap = uvm_analysis_port("r_ap", self)  # R
        self.tr_ap = uvm_analysis_port("tr_ap", self)  # Transactions

    def connect_phase(self):

        # Passthru AXI channels
        self.wr_mon.aw_ap.connect(self.aw_ap)
        self.wr_mon.w_ap.connect(self.w_ap)
        self.wr_mon.b_ap.connect(self.b_ap)

        self.rd_mon.ar_ap.connect(self.ar_ap)
        self.rd_mon.r_ap.connect(self.r_ap)

        # Connect transaction ports of both monitors to self
        self.wr_mon.tr_ap.connect(self)
        self.rd_mon.tr_ap.connect(self)

    def write(self, item):

        # Send incoming write or read transaction item to the transaction port
        self.tr_ap.write(item)
