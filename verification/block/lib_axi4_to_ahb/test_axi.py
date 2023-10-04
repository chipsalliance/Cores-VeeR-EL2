# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from cocotb.queue import QueueFull
from coordinator_seq import TestBothChannelsSeq
from testbench import BaseTest

# FIXME       : This test is expected to fail.
# Reason      : Handshake sequence is non-compliant with specification
# Faulty code : axi4_to_ahb.sv#L248-256
#
# Issue #1 BVALID/BREADY Handshake
# Handshake is meant to occur on the Write Response Channel in order:
# * subordinate asserts BVALID
# * manager responds with BREADY
# Quote: "The Subordinate must not wait for the Manager to assert BREADY
# before asserting BVALID"
# Source: AMBA AXI Protocol Specification A3.5.1 Write transaction dependencies
#
# In RTL:
#
# assign axi_bvalid  = slave_valid & slave_ready & slave_opc[3];
# assign slave_ready = axi_bready & axi_rready;
#
# BVALID is calculated from BREADY and RREADY, which is wrong for 2 reasons:
# * BVALID should not depend on RREADY
# * BVALID should be asserted before BREADY. BREADY should depend on BVALID.
#
# Issue #2 RVALID/RREADY Handshake
# Handshake is meant to occur on the Read Response Channel in order:
# * subordinate asserts RVALID
# * manager responds with RREADY
# Quote: "The Subordinate must not wait for the Manager to assert RREADY
# before asserting RVALID"
# Source: AMBA AXI Protocol Specification A3.5.2 Read transaction dependencies
#
# In RTL:
# assign axi_rvalid  = slave_valid & slave_ready & (slave_opc[3:2] == 2'b0);
# assign slave_ready = axi_bready & axi_rready;
#
# RVALID is calculated from BREADY and RREADY, which is wrong for 2 reasons:
# * RVALID should not depend on BREADY
# * RVALID should be asserted before RREADY. RREADY should depend on RVALID.


@pyuvm.test(expect_error=(TimeoutError, QueueFull))
class TestAXI(BaseTest):
    def end_of_elaboration_phase(self):
        self.seq = TestBothChannelsSeq.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()
