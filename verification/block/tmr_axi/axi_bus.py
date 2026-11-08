#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

from cocotbext.axi import (
    AxiARBus,
    AxiAWBus,
    AxiBBus,
    AxiBus,
    AxiRBus,
    AxiReadBus,
    AxiWBus,
    AxiWriteBus,
)
from cocotbext.axi.stream import StreamBus

# ==============================================================================


class StreamBusWithUpsets(StreamBus):
    """
    A proxy class that allows injecting upsets to the bus
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.upsets = dict()

    def drive(self, obj, strict=False):

        # Call the base method
        super().drive(obj, strict)

        # Drive upsets with no delay effectively overwriting what's given in
        # obj
        self.upset()

    def upset(self):
        """
        Drives upsets to the bus
        """
        for key, value in self.upsets.items():
            sig = self._signals.get(key, None)
            if sig is not None:
                sig.value = value
                sig._log.debug(f"upsetting to {value}")


# ==============================================================================


SAxiAWBus = type(
    "SAxiAWBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_o" if "ready" in s else "_i") for s in AxiAWBus._signals},
        "_optional_signals": {
            s: s + ("_o" if "ready" in s else "_i") for s in AxiAWBus._optional_signals
        },
    },
)

SAxiWBus = type(
    "SAxiWBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_o" if "ready" in s else "_i") for s in AxiWBus._signals},
        "_optional_signals": {
            s: s + ("_o" if "ready" in s else "_i") for s in AxiWBus._optional_signals
        },
    },
)

SAxiBBus = type(
    "SAxiBBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_i" if "ready" in s else "_o") for s in AxiBBus._signals},
        "_optional_signals": {
            s: s + ("_i" if "ready" in s else "_o") for s in AxiBBus._optional_signals
        },
    },
)


class SAxiWriteBus(AxiWriteBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        aw = SAxiAWBus.from_prefix(entity, prefix, **kwargs)
        w = SAxiWBus.from_prefix(entity, prefix, **kwargs)
        b = SAxiBBus.from_prefix(entity, prefix, **kwargs)
        return cls(aw, w, b)


SAxiARBus = type(
    "SAxiARBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_o" if "ready" in s else "_i") for s in AxiARBus._signals},
        "_optional_signals": {
            s: s + ("_o" if "ready" in s else "_i") for s in AxiARBus._optional_signals
        },
    },
)

SAxiRBus = type(
    "SAxiRBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_i" if "ready" in s else "_o") for s in AxiRBus._signals},
        "_optional_signals": {
            s: s + ("_i" if "ready" in s else "_o") for s in AxiRBus._optional_signals
        },
    },
)


class SAxiReadBus(AxiReadBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        ar = SAxiARBus.from_prefix(entity, prefix, **kwargs)
        r = SAxiRBus.from_prefix(entity, prefix, **kwargs)
        return cls(ar, r)


class SAxiBus(AxiBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        write = SAxiWriteBus.from_prefix(entity, prefix, **kwargs)
        read = SAxiReadBus.from_prefix(entity, prefix, **kwargs)
        return cls(write, read)


# ==============================================================================


MAxiAWBus = type(
    "MAxiAWBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_i" if "ready" in s else "_o") for s in AxiAWBus._signals},
        "_optional_signals": {
            s: s + ("_i" if "ready" in s else "_o") for s in AxiAWBus._optional_signals
        },
    },
)

MAxiWBus = type(
    "MAxiWBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_i" if "ready" in s else "_o") for s in AxiWBus._signals},
        "_optional_signals": {
            s: s + ("_i" if "ready" in s else "_o") for s in AxiWBus._optional_signals
        },
    },
)

MAxiBBus = type(
    "MAxiBBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_o" if "ready" in s else "_i") for s in AxiBBus._signals},
        "_optional_signals": {
            s: s + ("_o" if "ready" in s else "_i") for s in AxiBBus._optional_signals
        },
    },
)


class MAxiWriteBus(AxiWriteBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        aw = MAxiAWBus.from_prefix(entity, prefix, **kwargs)
        w = MAxiWBus.from_prefix(entity, prefix, **kwargs)
        b = MAxiBBus.from_prefix(entity, prefix, **kwargs)
        return cls(aw, w, b)


MAxiARBus = type(
    "MAxiARBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_i" if "ready" in s else "_o") for s in AxiARBus._signals},
        "_optional_signals": {
            s: s + ("_i" if "ready" in s else "_o") for s in AxiARBus._optional_signals
        },
    },
)

MAxiRBus = type(
    "MAxiRBus",
    (StreamBusWithUpsets,),
    {
        "_signals": {s: s + ("_o" if "ready" in s else "_i") for s in AxiRBus._signals},
        "_optional_signals": {
            s: s + ("_o" if "ready" in s else "_i") for s in AxiRBus._optional_signals
        },
    },
)


class MAxiReadBus(AxiReadBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        ar = MAxiARBus.from_prefix(entity, prefix, **kwargs)
        r = MAxiRBus.from_prefix(entity, prefix, **kwargs)
        return cls(ar, r)


class MAxiBus(AxiBus):
    @classmethod
    def from_prefix(cls, entity, prefix, **kwargs):
        write = MAxiWriteBus.from_prefix(entity, prefix, **kwargs)
        read = MAxiReadBus.from_prefix(entity, prefix, **kwargs)
        return cls(write, read)
