# Verification

The verification directory contains [pyuvm](https://github.com/pyuvm/pyuvm) tests, which rely on [cocotb](https://github.com/cocotb/cocotb) library.

## Setup

In order to run the tests, create a python virtual environment. Verilator is used as a backend simulator and must be present in the system.

### Clone repository

Remember to set the `RV_ROOT` environment variable, which is required to generate VeeR-EL2 Core configuration files.

    git clone --recurse-submodules git@github.com:chipsalliance/Cores-VeeR-EL2.git
    cd Cores-Veer-EL2
    export RV_ROOT=$(pwd)

### Prepare python virtual environment

    cd $RV_ROOT/verification
    python -m venv venv
    source venv/bin/activate
    pip install -r requirements.txt

### Install Verilator

Installation instructions are available in the Verilator's User Guide:

    https://veripool.org/guide/latest/install.html

## Tests

Each PyUVM test can be either run from a pytest wrapper or directly from a Makefile. The wrapper is placed to provide easier CI integration, HTML reports and Markdown summaries in job descriptions on GitHub. The Makefile execution may be more convenient during debugging.

### Example: `test_pyuvm`

In `test_pyuvm` directory, a `Makefile` and a wrapper `test_pyuvm.py` are placed.

    ./verification/
    └── test_pyuvm
        ├── Makefile
        ├── test_pyuvm.py ⟵ pytest wrapper
        └── test_irq
           └── test_irq.py ⟵ PyUVM test

The pytest wrapper can be executed with a command:

    python -m pytest -sv test_pyuvm.py

If you need to run the test directly from the `Makefile`, please look for the decorator in the pytest wrapper to find valid `UVM_TEST` names:

    @pytest.mark.parametrize("UVM_TEST", ["test_irq.test_irq"])

The test can also be run directly from the Makefile:

    UVM_TEST=test_irq.test_irq make all

Note that HTML report can be produced with flag `--html=index.html` and a markdown report with `--md=test.md`

## CI

PyUVM tests are run in CI with the following workflow:

    .github/workflows/test-verification.yml
