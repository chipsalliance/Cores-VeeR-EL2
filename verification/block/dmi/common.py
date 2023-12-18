#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotb.types import LogicArray, Range, concat
from pyuvm import *

# ==============================================================================


class BaseSeq(uvm_sequence):
    async def run_items(self, items):
        for item in items:
            await self.start_item(item)
            item.randomize()
            await self.finish_item(item)


class Defaults:
    # DMI defaults
    DMI_STAT = LogicArray(0, Range(11, "downto", 10))
    ABITS = LogicArray(7, Range(9, "downto", 4))
    VERSION = LogicArray(1, Range(3, "downto", 0))
    DTMCS = concat(concat(DMI_STAT, ABITS), VERSION)

    # JTAG defaults
    REVISION_CODE = LogicArray(0x0, range(4))
    MANUFACTURERS_ID_CODE = LogicArray(0x0, range(11))
    DEVICE_ID_CODE = LogicArray(0x0, range(16))
    JTAG_ID = concat(concat(REVISION_CODE, DEVICE_ID_CODE), MANUFACTURERS_ID_CODE)


def collect_signals(signals, uut, obj):
    """
    Collects signal objects from UUT and attaches them to the given object
    """

    for sig in signals:
        if hasattr(uut, sig):
            s = getattr(uut, sig)

        else:
            s = None
            logging.error("Module {} does not have a signal '{}'".format(str(uut), sig))

        setattr(obj, sig, s)


def get_int(signal):
    if isinstance(signal, LogicArray):
        return signal.integer
    else:
        try:
            sig = int(signal)
        except ValueError:
            sig = 0
        return sig
