# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotb.triggers import RisingEdge
from pyuvm import *
from utils import collect_bytes

# ==============================================================================


class BusWriteItem(uvm_sequence_item):
    """
    A generic data bus write request / response
    """

    def __init__(self, addr, data, resp=None):
        super().__init__("BusWriteItem")
        self.addr = addr
        self.data = data
        self.resp = resp


class BusReadItem(uvm_sequence_item):
    """
    A generic data bus read request / response
    """

    def __init__(self, addr, data=None, resp=None):
        super().__init__("BusReadItem")
        self.addr = addr
        self.data = data
        self.resp = resp


# ==============================================================================


class Axi4LiteMonitor(uvm_component):
    """
    A monitor for AXI4 lite bus
    """

    class Transfer:
        def __init__(self, tid, addr=None):
            self.tid = tid
            self.addr = addr
            self.data = bytearray()

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    def _aw_active(self):
        return self.bfm.axi_awready.value != 0 and self.bfm.axi_awvalid.value != 0

    def _w_active(self):
        return self.bfm.axi_wready.value != 0 and self.bfm.axi_wvalid.value != 0

    def _ar_active(self):
        return self.bfm.axi_arready.value != 0 and self.bfm.axi_arvalid.value != 0

    def _r_active(self):
        return self.bfm.axi_rready.value != 0 and self.bfm.axi_rvalid.value != 0

    def _b_active(self):
        return self.bfm.axi_bready.value != 0 and self.bfm.axi_bvalid.value != 0

    def _sample_w(self):
        return collect_bytes(
            self.bfm.axi_wdata,
            self.bfm.axi_wstrb,
        )

    def _sample_r(self):
        return collect_bytes(
            self.bfm.axi_rdata,
        )

    async def watch_write(self):
        """
        Watches the bus for writes
        """
        xfers = dict()
        awid = None

        # Main loop
        while True:
            # Wait for clock
            await RisingEdge(self.bfm.axi_clk)

            # A new write request
            if self._aw_active():
                addr = int(self.bfm.axi_awaddr.value)
                awid = int(self.bfm.axi_awid.value)

                if awid in xfers:
                    self.logger.error(
                        "Write request for a pending transaction, awid={}".format(awid)
                    )

                else:
                    xfers[awid] = self.Transfer(awid, addr)

            # Data (for the last seen awid)
            if self._w_active():
                if awid not in xfers:
                    self.logger.error("Data write but no transaction is pending")

                else:
                    xfer = xfers[awid]
                    xfer.data = self._sample_w()

            # Write completion
            if self._b_active():
                bresp = int(self.bfm.axi_bresp.value)
                bid = int(self.bfm.axi_bid.value)

                if bid not in xfers:
                    self.logger.error("Response for a non-pending transaction, bid={}".format(bid))

                else:
                    xfer = xfers[bid]
                    del xfers[bid]

                    self.ap.write(BusWriteItem(xfer.addr, xfer.data, bresp))

                    self.logger.debug(
                        "WR: 0x{:08X} {} 0b{:03b}".format(
                            xfer.addr, ["0x{:02X}".format(b) for b in xfer.data], bresp
                        )
                    )

    async def watch_read(self):
        """
        Watches the bus for reads
        """
        xfers = dict()

        # Main loop
        while True:
            # Wait for clock
            await RisingEdge(self.bfm.axi_clk)

            # A new read request
            if self._ar_active():
                addr = int(self.bfm.axi_araddr.value)
                arid = int(self.bfm.axi_arid.value)

                if arid in xfers:
                    self.logger.error(
                        "Read request for a pending transaction, arid={}".format(awid)
                    )

                else:
                    xfers[arid] = self.Transfer(arid, addr)

            # Read completion
            if self._r_active():
                rresp = int(self.bfm.axi_rresp.value)
                rid = int(self.bfm.axi_rid.value)

                if rid not in xfers:
                    self.logger.error("Data read but no transaction is pending")

                else:
                    xfer = xfers[rid]
                    xfer.data = self._sample_r()

                    del xfers[rid]

                    self.ap.write(BusReadItem(xfer.addr, xfer.data, rresp))

                    self.logger.debug(
                        "RD: 0x{:08X} {} 0b{:03b}".format(
                            xfer.addr, ["0x{:02X}".format(b) for b in xfer.data], rresp
                        )
                    )

    async def run_phase(self):
        # Start read & write watchers
        cocotb.start_soon(self.watch_write())
        cocotb.start_soon(self.watch_read())
