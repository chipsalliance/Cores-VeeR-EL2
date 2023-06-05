# Verification

The verification directory contains [cocotb](https://github.com/cocotb/cocotb) tests and [pyuvm](https://github.com/pyuvm/pyuvm) tests

## Setup

In order to run the tests, one must clone the repository, create a python virtual environment and patch cocotb's verilator support file. Verilator is used as a backend simulator and must be present in the system.

### Clone repository

Remember to set the `RV_ROOT` environment variable, which is required to generate a VeeR-EL2 Core configuration files.

    git clone git@github.com:chipsalliance/Cores-VeeR-EL2.git
    cd Cores-Veer-EL2
    export RV_ROOT=$(pwd)

### Prepare python virtual environment

    cd $RV_ROOT/verification
    python -m venv venv
    source venv/bin/activate
    pip install -r requirements.txt

### Patch cocotb

Due to issues with Verilator's `--timing` options, the `cocotb/share/lib/verilator.cpp` must be patched. The `--timing` option is only required if the HDL code contains timing structures.

TODO: update link to upstream when patch is merged

    cd $RV_ROOT/third_party
    git clone https://github.com/antmicro/cocotb
    git checkout mczyz/verilator-patch-timing
    pip install -e $RV_ROOT/third_party/cocotb

### Install Verilator

Verification tests were run with Verilator-5.0.10. Installation instruction is avaialable in the Verilator's User Guide:

    https://veripool.org/guide/latest/install.html

## Tests

All tests are wrapped in a pytest, which can be executed with:

    python -m pytest -sv <test_name>

If you want to generate html reports, it is recommended to use:

    python -m pytest -v <test_name> --html=index.html

If you want to generate a mardkown report, it is recommended to use:

    python -m pytest -v <test_name> --md=test.md

### PyUVM

The PyUVM test uses Makefile located in the verification directory:

    cd $RV_ROOT/verification
    UVM_TEST=<valid_test_name> make all

Also available targets are:

    make clean
    make verilator-pyuvm

Run all tests:

    python -m pytest -sv test.py

