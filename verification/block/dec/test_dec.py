# Copyright (c) 2025 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import pyuvm
from pyuvm import ConfigDB
from testbench import BaseEnv, BaseTest, DecSequence
from testbench import DecTmrGprRecoverySequence, DecTmrCsrRecoverySequence

# =============================================================================


class DecTluCtlTest(BaseTest):
    def __init__(self, test_name, name, parent, env_class=BaseEnv, seq_class=DecSequence, seq_kwarg=None):
        self.test_name = test_name
        self.seq_class = seq_class
        self.seq_kwarg = dict() if seq_kwarg is None else seq_kwarg
        super().__init__(name, parent, env_class)
        ConfigDB().set(None, "*", "TEST", self.test_name)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = self.seq_class("stimulus", **self.seq_kwarg)

    async def run(self):
        await self.seq.start(self.env.dec_seqr)


@pyuvm.test()
class TestMeihap(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("meihap", name, parent, env_class)


@pyuvm.test()
class TestMtdata(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("mtdata", name, parent, env_class)


@pyuvm.test()
class TestCsrAccess(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("csr_access", name, parent, env_class)


@pyuvm.test()
class TestDebugICCache(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("debug_ic_cache", name, parent, env_class)


@pyuvm.test()
class TestDebugCSRs(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("debug_csrs_access", name, parent, env_class)


@pyuvm.test()
class TestMeicidpl(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("meicidpl", name, parent, env_class)

@pyuvm.test()
class TestTmrGprRetrieve(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("recovery_gpr_access", name, parent, env_class,
            seq_class=DecTmrGprRecoverySequence, seq_kwarg={"mode": "retrieve"})

@pyuvm.test()
class TestTmrGprRestore(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("recovery_gpr_access", name, parent, env_class,
            seq_class=DecTmrGprRecoverySequence, seq_kwarg={"mode": "restore"})

@pyuvm.test()
class TestTmrCsrRetrieve(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("recovery_csr_access", name, parent, env_class,
            seq_class=DecTmrCsrRecoverySequence, seq_kwarg={"mode": "retrieve"})

@pyuvm.test()
class TestTmrCsrRestore(DecTluCtlTest):
    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__("recovery_csr_access", name, parent, env_class,
            seq_class=DecTmrCsrRecoverySequence, seq_kwarg={"mode": "restore"})
