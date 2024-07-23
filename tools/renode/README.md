# VeeR EL2 Support in Renode

This directory contains files required for running VeeR user mode tests in [Renode](https://renode.io/).

## Building tests

The [build-all-tests.sh](build-all-tests.sh) is provided to simplify the process of building all supported tests.
Refer to the main [README](../../README.md) for information about dependencies required for building RISC-V test binaries.

## Running tests in Renode

[veer.robot](veer.robot) contains definitions of tests that will be executed in Renode.
Please refer to [Testing with Renode](https://renode.readthedocs.io/en/latest/introduction/testing.html) documentation chapter for a general
overview of testing software using Renode.

### Using the provided scripts

The simplest way of running test on Linux is to use the provided [run-tests.sh](run-tests.sh) script.
Internally it uses [renode-run](https://github.com/antmicro/renode-run) to obtain a Renode executable and install required dependencies
and start the [veer.robot](veer.robot) test file

### Running tests manually

1. Download a nightly release of Renode from [builds.renode.io](https://builds.renode.io/) for your operating system
   and make sure that Renode is in your system's `PATH`. Full installation instructions are available in
   Renode's [README](https://github.com/renode/renode/blob/master/README.md#installation)
1. Install additional python dependencies required for testing with Renode using `pip`
   ```shell
   pip install -r <renode executable directory>/tests/requirements.txt
   ```
1. For your shell run (assuming that Renode is in your system's `PATH`):
   ```shell
   renode-test veer.robot
   ```

## Directory structure

* [veer.resc](veer.resc) - Renode script defining the simulation environment
* [veer.repl](veer.repl) - Renode platform description used in user mode tests
* [veer.robot](veer.robot) - [Robot Framework](https://robotframework.org/) test file, listing all test cases to be run in Renode
* [build-all-tests.sh](build-all-tests.sh) - Shell script used for building test binaries
* [run-tests.sh](run-tests.sh) - Shell script used to simplify executing user mode tests.
