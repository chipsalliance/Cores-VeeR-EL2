# RISCV-DV for VeeR-EL2 Core

This folder contains utilities necessary for running [RISCV-DV](https://htmlpreview.github.io/?https://github.com/google/riscv-dv/blob/master/docs/build/singlehtml/index.html#) tests with VeeR-EL2 Core as well as the master Makefile which facilitates the process.

RISCV-DV is a framework for testing RISC-V cores by generating random instructions, executing them in a reference ISS (instruction set simulator) as well as on the tested core (RTL simulation) and comparing execution trace logs. The trace logs contain executed instructions and core state changes (register writes) after each one which allows to precisely track the core behavior.

## Setup

1. Clone VeeR-EL2 Core repository with submodules and set `RV_ROOT` to the repository path:

```
git clone --recurse-submodules git@github.com:chipsalliance/Cores-VeeR-EL2.git
cd Cores-Veer-EL2
export RV_ROOT=$(pwd)
```

2. Setup the RISCV-DV framework

The framework should be already cloned in `Cores-Veer-EL2/third_party/riscv-dv`. Install its dependencies, best using a Python virtual environment:

```
python3 -m venv env
source env/bin/activate
pip install -r ${RV_ROOT}/third_party/riscv-dv/requirements.txt
```

3. Setup Verilator

Installation instructions are available in the [Verilator's User Guide](https://veripool.org/guide/latest/install.html). Make sure that the verilator executable is available (eg. by setting `PATH`).

4. Setup instruction set simulator (ISS)

RISCV-DV tests require a reference RISC-V program executor in a form of instruction set simulator. The RISCV-DV flow for VeeR-EL2 Core supports three of them:

   - Spike
  
     Follow the instruction from the [documentation](https://github.com/riscv-software-src/riscv-isa-sim#build-steps). After installation make sure that the spike binary is visible in the current path.
  
   - VeeR ISS (previously known as "whisper")
  
     VeeR ISS (previously known as "whisper") is a simulator designed specifically for VeeR. To build and install VeeR ISS follow the instructions in its [documentation](https://github.com/chipsalliance/VeeR-ISS#compiling-whisper).
  
   - Renode
  
     [Renode](www.renode.io) is a full-fledged embedded system simulator developed at Antmicro. Its capabilities go beyond simulating a RISC-V core. In configuration for RISCV-DV only basic features are used just to be able to produce execution trace log.
  
     Renode can be downloaded as a pre-built binary. Download the latest "linux-portable" release from https://github.com/renode/renode/releases and unpack it. For example:
     ```
     wget https://github.com/renode/renode/releases/download/v1.13.3/renode-1.13.3.linux-portable.tar.gz
     tar -zxf renode-1.13.3.linux-portable.tar.gz
     export PATH=${PATH}:`realpath renode_1.13.3_portable`
     ```

5. Setup RISC-V toolchain

Download and install RISC-V GCC toolchain capable for targeting RV32IMC architecture. Depending on your system this may be done either via the system package manager or manually by downloading binaries / building them.

Export environmental variables required by RISCV-DV:
```
export RISCV_TOOLCHAIN=<riscv_gcc_install_path>
export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-gcc"
export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-objcopy"
export RISCV_NM="$RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-nm"
```

## Running tests

To run the tests using the default setup do the following:
```
cd ${RV_ROOT}/tools/riscv-dv
make run
```

Test execution environment is configurable by setting environment variables, which can be done either in the `Makefile` or in the CLI command,e.g;
```
RISCV_DV_ISS=whisper` make all
```

Full list of supported options is presented in the table below:

|     Variable      |         Default value         |           Allowed values          | Description                                               |
| :---------------: | :----------------------------:| :-------------------------------: | :-------------------------------------------------------: |
| `RISCV_DV_ISS`    | `spike`                       | `spike`, `whisper`, `renode`      | Controls which ISS is used as the reference.              |
| `RISCV_DV_TEST`   | `riscv_arithmetic_basic_test` |                                   | Test name. The complete list of tests can be found in [RISCV-DV documentation](https://github.com/chipsalliance/riscv-dv/tree/master/pygen/pygen_src) |
| `RISCV_DV_ITER`   | 1                             | >= 1                              | Test iteration count, default 1.                          |
| `RISCV_DV_BATCH`  | 1                             | >= 1                              | Test batch count, default 1.                              |
| `RISCV_DV_SEED`   | 999                           |                                   | Random generator seed for RISCV-DV instruction randomizer.|
| `COVERAGE`        |                               | `branch`, `toggle`, `functional`  | Enables coverage data collection in Verilator. More information about coverage in Verilator can be found in its [documentation](https://veripool.org/guide/latest/simulating.html#coverage-analysis). |

## CI

RISCV-DV tests are run in GitHub actions CI. The workflow responsible for them can be found at `.github/workflows/test-riscv-dv.yml`
