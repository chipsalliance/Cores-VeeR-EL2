# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0


from enum import IntEnum

AHB_DRV_SIGNALS = [
    "ahb_hrdata",
    "ahb_hready",
    "ahb_hresp",
]

AHB_RSP_SIGNALS = [
    "ahb_haddr",
    "ahb_hburst",
    "ahb_hmastlock",
    "ahb_hprot",
    "ahb_hsize",
    "ahb_htrans",
    "ahb_hwrite",
    "ahb_hwdata",
]


class AHB_LITE_RESPONSE_CODES(IntEnum):
    OKAY = 0


class AHB_LITE_TRANSFER_TYPE_ENCODING(IntEnum):
    IDLE = 0
    BUSY = 1
    NONSEQ = 2
    SEQ = 3


class AHB_LITE_NOTIFICATION(IntEnum):
    AHB_LITE_WRITE = 1
    AHB_LITE_READ = 2
    AHB_LITE_IDLE = 3
