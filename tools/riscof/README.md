# RISCOF for VeeR-EL2 Core

This folder stores configuration files and plugins needed for running [RISCOF](https://riscof.readthedocs.io/en/stable/) tests for VeeR-EL2 Core.

RISCOF is an official RISC-V core testing framework. Testing is done by executing predefined test programs on the simulated core (RTL simulation) and using an Instruction Set Simulator (ISS) followed comparing memory signatures. A memory signature is a memory region defined by a particular test program which content is compared.

## Install prerequisities

1. Verilator

Installation instructions are available in the [Verilator's User Guide](https://veripool.org/guide/latest/install.html). Make sure that the verilator executable is available (eg. by setting `PATH`).

2. Spike (Instruction Set Simulator)

Follow the instruction from the [documentation](https://github.com/riscv-software-src/riscv-isa-sim#build-steps). After installation make sure that the spike binary is visible in the current path.

3. RISC-V toolchain

Download and install RISC-V GCC toolchain capable for targeting RV32IMC architecture. Depending on your system this may be done either via the system package manager or manually by downloading binaries / building them.

## Setup

1. Clone VeeR-EL2 Core repository with submodules and set `RV_ROOT` to the repository path:

```
git clone --recurse-submodules git@github.com:chipsalliance/Cores-VeeR-EL2.git
cd Cores-Veer-EL2
export RV_ROOT=$(pwd)
```

2. Build verilated model of VeeR-EL2 Core

```
${RV_ROOT}/configs/veer.config
make -f ${RV_ROOT}/tools/Makefile verilator-build
```

3. Install RISCOF (in a Python virtual environment)

```
python3 -m venv env
source env/bin/activate
pip install git+https://github.com/riscv/riscof
```

4. Clone RISCOF official tests

The RISCOF framework uses manually developed official test programs. These need to be installed:

```
mkdir work
cd work
riscof --verbose info arch-test --clone
```

There are tests that include RISC-V `Zicsr` extension which cannot be disabled. Since VeeR-EL2 Core does not support this extension they need to be removed manually. This is a temporary workaround:
```
rm -rf riscv-arch-test/riscv-test-suite/rv32i_m/privilege/
```

5. Configure RISCOF

Copy RISCOF configuration from VeeR-EL2 Core repository to the working directory and build the test list:
```
cp ${RV_ROOT}/tools/riscof/config.ini ./
cp -r ${RV_ROOT}/tools/riscof/spike ./
cp -r ${RV_ROOT}/tools/riscof/veer ./
riscof testlist --config=config.ini --suite=riscv-arch-test/riscv-test-suite/ --env=riscv-arch-test/riscv-test-suite/env
```

## Running the tests

To run the tests issue the following command. Once the tests finish a HTML report will be generated
```
riscof run --no-browser --config=config.ini --suite=riscv-arch-test/riscv-test-suite/ --env=riscv-arch-test/riscv-test-suite/env
```

## CI

RISCOF tests are run in CI. See `.github/workflows/test-riscof.yml` for GitHub actions workflow description.
