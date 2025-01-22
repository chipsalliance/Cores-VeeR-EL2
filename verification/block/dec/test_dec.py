# Copyright (c) 2025 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import pyuvm
from pyuvm import ConfigDB
from testbench import BaseEnv, BaseTest, DecSequence

# =============================================================================


class DecTluCtlTest(BaseTest):
    def __init__(self, test_name, name, parent, env_class=BaseEnv):
        self.test_name = test_name
        super().__init__(name, parent, env_class)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        ConfigDB().set(None, "*", "TEST", self.test_name)
        self.seq = DecSequence("stimulus")

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
