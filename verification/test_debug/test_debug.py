#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import pytest
import subprocess

class TestDebug():
    def test_debug(self):
        print("This test returns true")
        assert True == True
