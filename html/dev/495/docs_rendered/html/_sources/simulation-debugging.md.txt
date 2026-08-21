# Interactive Debugging in Simulation

It is possible to perform a debugging session through a virtual JTAG interface with the VeeR EL2 Core running in simulation.
This allows the user to exercise JTAG usage scenarios using actual debugging tools instead of unit tests written for JTAG logic.
The feature was added to the VeeR EL2 Core with [Pull Request #211](https://github.com/chipsalliance/Cores-VeeR-EL2/pull/211).

The principle of operation is a JTAG probe RTL model which communicates with the host via DPI.
This is illustrated in {numref}`fig-openocd-jtag`:

:::{figure-md} fig-openocd-jtag
![](img/openocd-jtag.png)

OpenOCD JTAG
:::

Currently the probe model implements the `remote_bitbang` protocol of [OpenOCD](https://openocd.org/), allowing the tool to interact with simulation.
The protocol operates over a TCP/IP connection or a UNIX socket.
An appropriate server and protocol decoder runs on the host machine and communicates with the simulation via DPI to set/read JTAG signal states.
The entire flow is transparent to the debugging tools and to the user.

The probe model has been integrated into the testbench.
It is active every time the testbench is run; there is no need for any additional action.
To run a testbench, execute, for example:

```bash
make -C run -f ${RV_ROOT}/tools/Makefile verilator-build program.hex TEST=infinite_loop \
    CONF_PARAMS="-set openocd_test"
```

The `RV_ROOT` variable in the snippet above is the path to the root of the Cores-VeeR-EL2 repository.

To keep the simulation running continuously, the `infinite_loop` test program has been added.
The program consists of two nested loops running continuously.

Then, to connect to a running simulation via OpenOCD, you can use the configs available in the `testbench/openocd_scripts` directory:

```bash
cd testbench/openocd_scripts
openocd -d2 -f verilator-rst.cfg jtag_cg.tcl
```

`jtag_cg.ctl` is an OpenOCD script that performs JTAG access tests.
These include core register access and memory access.
The configuration is passed by `verilator-rst.cfg`.
It includes `sim-jtagdpi.cfg` and `veer-el2-rst.cfg`.
`sim-jtagdpi.cfg` contains a JTAG adapter configuration.
`veer-el2-rst.cfg` configures the target for OpenOCD.
The test involves the CPU core held permanently in reset.
Moreover, a [customized version of OpenOCD](https://github.com/antmicro/openocd/tree/riscv-nohalt) had to be used, as the stock version performs target CPU examination by default which is not possible when in reset.

### Automation

In the `.github/scripts` directory of the [VeeR](https://github.com/chipsalliance/Cores-VeeR-EL2) repository, you can find a helper `openocd_test.sh` script that is responsible for launching simulation, executing an OpenOCD script as a test and terminating it.
The script is used in CI.

The script assumes that both the verilated simulation and the CPU program binary are already built.
You can find a usage example in the GitHub Action workflow definition: `.github/workflows/test-openocd.yml`.
