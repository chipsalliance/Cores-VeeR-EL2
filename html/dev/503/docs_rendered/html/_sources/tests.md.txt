# Compliance Test Suite Failures

## *I-MISALIGN_LDST-01*

* **Test Location**: [https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32i/src/I-MISALIGN_LDST-01.S](https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32i/src/I-MISALIGN_LDST-01.S)
* **Reason for Failure**:
  * The VeeR EL2 core supports unaligned accesses to memory addresses which are not marked as having side effects (i.e., to idempotent memory).
    Load and store accesses to non-idempotent memory addresses take misalignment exceptions.
  * Note that this is a known issue with the test suite ([https://github.com/riscv/riscv-compliance/issues/22](https://github.com/riscv/riscv-compliance/issues/22)) and is expected to eventually be fixed.
* **Workaround**:
  * Configure the address range used by this test to "non-idempotent" in the `mrac` register.

## *I-MISALIGN_JMP-01*

* **Test location**: [https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32i/src/I-MISALIGN_JMP-01.S](https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32i/src/I-MISALIGN_JMP-01.S)
* **Reason for Failure**:
  * The VeeR EL2 core supports the standard "C" 16-bit compressed instruction extension.
    Compressed instruction execution cannot be turned off.
    Therefore, branch and jump instructions to 16-bit aligned memory addresses do not trigger misalignment exceptions.
  * Note that this is a known issue with the test suite ([https://github.com/riscv/riscv-compliance/issues/16](https://github.com/riscv/riscv-compliance/issues/16)) and is expected to eventually be fixed.
* **Workaround**:
  * None.

## *I-FENCE.I-01 and fence_i*

* **Test location**:
  * [https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32Zifencei/src/I-FENCE.I-01.S](https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32Zifencei/src/I-FENCE.I-01.S) and
  * [https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32ui/src/fence_i.S](https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32ui/src/fence_i.S)
* **Reason for Failure**:
  * The VeeR EL2 core implements separate instruction and data buses to the system interconnect (i.e., Harvard architecture).
    The latencies to memory through the system interconnect may be different for the two interfaces and the order is therefore not guaranteed.
* **Workaround**:
  * Configuring the address range used by this test to "non-idempotent" in the `mrac` register forces the core to wait for a write response before fetching the updated line.
    Alternatively, the system interconnect could provide ordering guarantees between requests sent to the instruction fetch and load/store bus interfaces (e.g., matching latencies through the interconnect).

## *Breakpoint*

* **Test Location**:
  * [https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32mi/src/breakpoint.S](https://github.com/riscv/riscv-compliance/blob/master/riscv-test-suite/rv32mi/src/breakpoint.S)
* **Reason for Failure**:
  * The VeeR EL2 core disables breakpoints when the *mie* bit in the standard `mstatus` register is cleared.
  * Note that this behavior is compliant with the RISC-V External Debug Support specification, Version 0.13.2. See Section 5.1, 'Native M-Mode Triggers' in [[3]](intro.md#ref-3) for more details.
* **Workaround**:
  * None.
