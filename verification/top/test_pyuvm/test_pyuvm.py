import pytest
import os
import subprocess


class TestPyUVM():

    @pytest.mark.parametrize("UVM_TEST", ["test_irq.test_irq"])
    def test_pyuvm(self, UVM_TEST, coverage_opt):

        os.environ["UVM_TEST"] = UVM_TEST
        py_command = []
        py_command += [f"COVERAGE={coverage_opt}"]
        py_command += [
            "make all",
        ]
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