# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum

AXI_W_CHAN_DRV_SIGNALS = [
    "axi_awvalid",
    "axi_awid",
    "axi_awaddr",
    "axi_awsize",
    "axi_awprot",
    "axi_wvalid",
    "axi_wdata",
    "axi_wstrb",
    "axi_wlast",
    "axi_bready",
]

AXI_W_CHAN_RSP_SIGNALS = [
    "axi_awready",
    "axi_wready",
    "axi_bvalid",
    "axi_bresp",
    "axi_bid",
]

AXI_W_CHAN_SIGNALS = AXI_W_CHAN_DRV_SIGNALS + AXI_W_CHAN_RSP_SIGNALS

AXI_R_CHAN_DRV_SIGNALS = [
    "axi_arvalid",
    "axi_arid",
    "axi_araddr",
    "axi_arsize",
    "axi_arprot",
    "axi_rready",
]

AXI_R_CHAN_RSP_SIGNALS = [
    "axi_arready",
    "axi_rvalid",
    "axi_rid",
    "axi_rdata",
    "axi_rresp",
    "axi_rlast",
]

AXI_R_CHAN_SIGNALS = AXI_R_CHAN_DRV_SIGNALS + AXI_R_CHAN_RSP_SIGNALS


class AXI_WRITE_RESPONSE_CODES(IntEnum):
    OKAY = 0
    EXOKAY = 1
    SLVERR = 2
    DECERR = 3
    DEFER = 4
    TRANSFAULT = 5
    RESERVED = 6
    UNSUPPORTED = 7


class AXI_READ_RESPONSE_CODES(IntEnum):
    OKAY = 0
    EXOKAY = 1
    SLVERR = 2
    DECERR = 3
    PREFETCHED = 4
    TRANSFAULT = 5
    OKAYDIRTY = 6
    RESERVED = 7


class AXI_AXSIZE_ENCODING(IntEnum):
    MAX_1B_TRANSFER = 0
    MAX_2B_TRANSFER = 1
    MAX_4B_TRANSFER = 2
    MAX_8B_TRANSFER = 3
    MAX_16B_TRANSFER = 4
    MAX_32B_TRANSFER = 5
    MAX_64B_TRANSFER = 6
    MAX_128B_TRANSFER = 7


class AXI_NOTIFICATION(IntEnum):
    AXI_FREE = 1
    AXI_BUSY = 2
    AXI_AREAD_HANDSHAKE = 3
    AXI_READ_HANDSHAKE = 4
