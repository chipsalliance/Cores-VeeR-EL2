# Block Level Verification

This directory contains block-level verification environments for VeeR-EL2 using [pyuvm](https://github.com/pyuvm/pyuvm) and [cocotb](https://github.com/cocotb/cocotb).

## Setup

The setup is similar to the top-level verification. Verilator (default) or VCS are supported as backend simulators.

### Environment Variables

Ensure `RV_ROOT` is set to the root of the VeeR-EL2 repository:

```bash
export RV_ROOT=/path/to/Cores-VeeR-EL2
```

### Python Environment Setup

You can use either a virtual environment (venv) or Conda to manage Python dependencies.

#### Using `venv`

Create and activate a python virtual environment, then install the dependencies:

```bash
cd $RV_ROOT/verification/block
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

#### Using `Conda`

```bash
conda create -n veer-el2-block python=3.12
conda activate veer-el2-block
pip install -r requirements.txt
```

## Running Tests

Block level verification supports running tests using either `nox` (for automation/multiple blocks) or `make` directly in the block directory (for debugging).

### Running with Nox

`nox` is used to run tests for different blocks with various configurations (e.g., coverage).

To run all tests:

```bash
nox
```

To run tests for a specific block (e.g., `dccm`):

```bash
nox -s dccm_verify
```

To run a specific test case within a block, you can use the `-k` option of `nox` (which uses `pytest` parametrization under the hood):

```bash
nox -s pic_verify -k test_reset
```

### Running with Makefile directly

For debugging, it might be more convenient to run the tests directly from the block's directory using `make`.

1. Navigate to the block directory:
   ```bash
   cd $RV_ROOT/verification/block/dccm
   ```
2. Run `make` specifying the `MODULE` (the python test file name without `.py`):
   ```bash
   MODULE=test_readwrite make
   ```

You can also specify coverage:
```bash
COVERAGE_TYPE=all MODULE=test_readwrite make
```

Available `COVERAGE_TYPE` values are: `all`, `branch`, `toggle`, `functional`.

### Using Alternative Simulators

By default, Verilator is used. You can run tests using Synopsys VCS by setting the `SIM` variable when running `make` directly:

```bash
cd $RV_ROOT/verification/block/dccm
MODULE=test_readwrite SIM=vcs make
```

## Simulation Logs

### When running with Nox
Nox redirects the simulation output to log files to keep the console clean:
*   **Default Log Path**: `verification/block/<block_name>/<test_name>.log` (e.g., `verification/block/dccm/test_readwrite.log`)
*   **With Coverage Enabled**: The log file is renamed to include the coverage type: `verification/block/<block_name>/<test_name>_<coverage_type>.log` (e.g., `verification/block/dccm/test_readwrite_all.log`)

### When running with Makefile directly
The simulation log is printed **directly to your terminal screen** (stdout/stderr). A summary of the test results is also saved in `verification/block/<block_name>/results.xml`.

## Hardware Configuration

Block-level verification automatically generates a default hardware configuration (snapshot) using `veer.config` before running the simulation. This configuration is generated in `verification/block/snapshots/default`.

You can customize this configuration by passing extra options to `veer.config` via the `EXTRA_VEER_CONFIG` variable:

```bash
cd $RV_ROOT/verification/block/dccm
EXTRA_VEER_CONFIG="-set=dccm_size=32" MODULE=test_readwrite make
```

## Directory Structure

*   `common/`: provides shared, reusable Python verification utilities and components that can be imported across all block-level testbenches.
*   Block subdirectories (e.g., `dccm`, `dec`, `exu_alu`): Each subdirectory represents a block under test. They typically contain:
    *   `Makefile`: The block-specific Makefile.
    *   `testbench.py`: The PyUVM testbench environment (drivers, monitors, scoreboards).
    *   `test_*.py`: The test cases.
    *   `config.vlt`: Verilator configuration file (if needed).

