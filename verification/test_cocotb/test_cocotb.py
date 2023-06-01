import pytest
import os
import subprocess


class TestCocotb():

    @pytest.mark.parametrize("MODULE", ["test_base.test_base"])
    def test_pyuvm(self, MODULE):

        py_command = [f"MODULE={MODULE}"]
        py_command += [" ".join(
            [
                "make -f",
                os.environ["RV_ROOT"]+"/tools/Makefile verilator-cocotb"
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
