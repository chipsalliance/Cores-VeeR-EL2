# Running Tock OS

This chapter describes the steps necessary to build a [Tock OS](https://github.com/tock/tock) application for the VeeR EL2 core, along with instructions for running it in simulation using [Verilator](https://github.com/verilator/verilator).

## Prerequisites

Install build dependencies:

```
apt install curl make build-essential gcc-riscv64-unknown-elf wget unzip python3-pip
```

To compile Tock, you need a Rust toolchain installer called `rustup`:

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

For detailed information on installing Tock OS, refer to the project's [documentation](https://book.tockos.org/).

## Fetching sources

```
git clone https://github.com/tock/tock.git
cd tock
```

## Running simulation in Verilator

In order to compile Tock OS and start simulation, run:

```
make -C boards/veer_el2_sim sim
```

The expected output is:

```
VerilatorTB: Start of sim
mem_signature_begin = 00000000
mem_signature_end   = 00000000
mem_mailbox         = D0580000
VeeR EL2 initialisation complete.
Entering main loop.
```

## Running simulation in Verilator with applications

### Building Tock

In order to compile Tock, run:

```
make -C boards/veer_el2_sim
```

### Building an application

```
git clone https://github.com/tock/libtock-c.git
make -C libtock-c/examples/c_hello -j$(nproc)
```

### Providing a verilog file for simulation

The testbench for Verilator requires a single file with a program (`program.hex`), so it's necessary to combine the kernel and applications into a single binary first.

You can use Tockloader to create a binary file representing flash with the kernel, and then install the application:

```
tockloader flash --board veer_el2_sim --flash-file ./veer_el2_sim.bin --address 0x20000000 ./target/riscv32imc-unknown-none-elf/release/veer_el2_sim.bin
tockloader install --board veer_el2_sim --arch rv32imc --flash-file ./veer_el2_sim.bin libtock-c/examples/c_hello/build/c_hello.tab
riscv64-unknown-elf-objcopy --change-addresses 0x20000000 -I binary -O verilog veer_el2_sim.bin program.hex
```

Now `program.hex` is ready for use in simulation.

### Starting simulation in Verilator

Clone the Cores-VeeR-EL2 repository:

```
git clone https://github.com/chipsalliance/Cores-VeeR-EL2.git
cd Cores-VeeR-EL2
git switch --detach da1042557
```

Increase the maximum number of cycles in simulation:

```
sed -i 's/parameter MAX_CYCLES = 2_000_000;/parameter MAX_CYCLES = 10_000_000;/g' testbench/tb_top.sv
```

You can build a testbench using these commands:

```
export RV_ROOT=$(pwd)
make -C tools CONF_PARAMS='-set build-axi4 -set user_mode=1 -set reset_vec=0x20000000' verilator-build
```

Make sure the program you want to run is placed in the current working directory and named `program.hex`:

```
cp ../program.hex .
```

In order to start the simulation, run:

```
./tools/obj_dir/Vtb_top
```

The output should look like this:

```
VerilatorTB: Start of sim

mem_signature_begin = 00000000
mem_signature_end   = 00000000
mem_mailbox         = D0580000
VeeR EL2 initialisation complete.
Entering main loop.
Hello World!
```

The execution trace will be located in `exec.log`.
