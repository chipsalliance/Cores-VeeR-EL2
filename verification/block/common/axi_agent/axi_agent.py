#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import enum
from pyuvm import *

from . import AxiDriver, AxiMonitor

__all__ = ["AxiAgentType", "AxiAgent"]

# ==============================================================================

class AxiAgentType(enum.IntEnum):
    MASTER = 0
    SLAVE  = 1

class AxiAgent(uvm_agent):

    def __init__(self, *args, **kwargs):
        self.type     = kwargs["type"]
        self.bfm_args = kwargs["bfm_args"]

        del kwargs["type"]
        del kwargs["bfm_args"]

        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.sequencer = uvm_sequencer("sequencer", self)
        self.driver    = AxiDriver("driver", self, bfm_args=self.bfm_args)
        self.monitor   = AxiMonitor("monitor", self, bfm_args=self.bfm_args)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.sequencer.seq_item_export)
