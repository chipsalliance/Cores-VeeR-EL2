#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import enum
import random

from cocotbext.axi.axi_channels import (
    AxiARTransaction,
    AxiAWTransaction,
    AxiBTransaction,
    AxiRTransaction,
    AxiWTransaction,
)
from cocotbext.axi.constants import *
from pyuvm import *

__all__ = [
    "AxiAWItem",
    "AxiWItem",
    "AxiBItem",
    "AxiARItem",
    "AxiRItem",
    "AxiWriteTransaction",
    "AxiReadTransaction",
    "AxiTransactionType",
    "AxiTransaction",
]

# ==============================================================================


class AxiWrapperItem(uvm_sequence_item):
    """
    A PyUVM wrapper over cocotbext-axi transaction item
    """

    def __init__(self, item, timestamp=0, name=None):
        super().__init__(self.__class__.__name__ if name is None else name)
        self.item = item
        self.timestamp = timestamp

    def __eq__(self, other):
        if not isinstance(other, self.__class__):
            return False

        for key in self.item._signals:
            this = getattr(self.item, key)
            that = getattr(other.item, key)
            if this != that:
                return False

        return True

    def __str__(self):
        return str(self.item)


AxiAWItem = type("AxiAWItem", (AxiWrapperItem,), dict())
AxiWItem = type("AxiWItem", (AxiWrapperItem,), dict())
AxiBItem = type("AxiBItem", (AxiWrapperItem,), dict())
AxiARItem = type("AxiARItem", (AxiWrapperItem,), dict())
AxiRItem = type("AxiRItem", (AxiWrapperItem,), dict())

# ==============================================================================


class AxiWriteTransaction(uvm_sequence_item):

    def __init__(self, name="AxiWriteTransaction"):
        super().__init__(name)
        self.aw = None
        self.w = []
        self.b = None

    def __eq__(self, other):
        if not isinstance(other, self.__class__):
            return False

        return self.aw == other.aw and self.w == other.w and self.b == other.b

    def __str__(self):
        lines = [str(self.aw)]
        lines += [str(w) for w in self.w]
        lines += [str(self.b)]
        return "\n".join(lines)


class AxiReadTransaction(uvm_sequence_item):

    def __init__(self, name="AxiReadTransaction"):
        super().__init__(name)
        self.ar = None
        self.r = []

    def __eq__(self, other):
        if not isinstance(other, self.__class__):
            return False

        return self.ar == other.ar and self.r == other.r

    def __str__(self):
        lines = [str(self.ar)]
        lines += [str(r) for r in self.r]
        return "\n".join(lines)


# ==============================================================================


class AxiTransactionType(enum.IntEnum):
    READ = 0
    WRITE = 1


class AxiTransaction(uvm_sequence_item):
    def __init__(self, name="AxiTransaction"):
        super().__init__(name)
        self.is_blocking = True

        self.type = None
        self.address = None
        self.data = None
        self.length = None
        self.id = 0
        self.burst = AxiBurstType.INCR
        self.size = None
        self.resp = None
        # TODO: Other fields

    # TODO: Randomization
    #
    # def randomize(self, address_width=32, id_width=1):
    #     self.type    = random.choice([AxiItemType.WRITE, AxiItemType.READ])
    #     self.address = random.randrange(1 << address_width)
    #     self.id      = random.randrange(1 << id_width)
    #     self.size    = random.choice()
