#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import pytest
import os
import subprocess


class TestCocotb():

    @pytest.mark.parametrize("MODULE", ["test_exu_alu.test_exu_alu"])
    def test_pyuvm(self, MODULE):

        py_command = [" ".join(
            [
                "python -m pytest -sv test_exu_alu/test.py"
            ]
        )]

        py_command = " ".join(py_command)

        print(f"\n----- PyTest -----")
        print(f":: py_command >> {py_command}")
        p = subprocess.run(py_command, shell=True,
                           executable="/bin/bash", bufsize=0)
        print(f"\n------------------")

        print(f"----- Subprocess Summary -----")
        print(f"p.check_returncode")
        p.check_returncode()
        print(f"------------------------------")
