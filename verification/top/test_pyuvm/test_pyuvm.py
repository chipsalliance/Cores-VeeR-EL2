import pytest
import os
import subprocess


class TestPyUVM():

    @pytest.mark.parametrize("UVM_TEST", ["test_irq.test_irq"])
    def test_pyuvm(self, UVM_TEST, coverage_opt, sim_opt, conf_params):

        os.environ["UVM_TEST"] = UVM_TEST
        py_command = []
        py_command += [f"COVERAGE_TYPE={coverage_opt}"]
        py_command += [f"SIM={sim_opt}"]
        py_command += [f"CONF_PARAMS='{conf_params}'"]
        py_command += [
            "make clean all",
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
