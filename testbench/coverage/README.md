# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages and 0-delay mode.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) along with dynamic cycle latency measurement tracking logic.
- **`el2_veer_lockstep_cov_bind.sv`**: Testbench binding module (`el2_veer_lockstep_delay_cov_bind`) that binds `el2_veer_lockstep_delay_cov_if` (new delay/latency coverage under VCS and Verilator) to `el2_veer_lockstep`, plus a Verilator stub for `el2_veer_lockstep_cov_if` so `verification/block/dcls/` files compile cleanly under Verilator.

## Coverage Architecture

### 1. `lockstep_delay_cp`
Monitors all supported values of parameter `pt.LOCKSTEP_DELAY`:
- `delay_0`: `LOCKSTEP_DELAY == 0` (Combinatorial bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops).
- `delay_1`: `LOCKSTEP_DELAY == 1`
- `delay_2`: `LOCKSTEP_DELAY == 2`
- `delay_3`: `LOCKSTEP_DELAY == 3`
- `delay_4`: `LOCKSTEP_DELAY == 4`

### 2. `delay_mismatch_detection_latency_cp`
Measures the clock cycle latency from the cycle of fault injection / divergence onset to the cycle where `corruption_detected_o` asserts `El2MuBiTrue`:
- `delay_0`: Latency must be 0 to 1 cycle (`latency_0`, `latency_1`).
- `delay_N` ($N \in \{1, 2, 3, 4\}$): Latency must match the configured pipeline delay stage (`latency_N`).

### 3. `corruption_detected_cp`
Tracks `corruption_detected_o` assertion to `El2MuBiTrue`.

### 4. Cross Coverage
- `lockstep_delay_x_corruption`: Crosses `lockstep_delay_cp` with `corruption_detected_cp` to guarantee divergence is caught across every supported delay configuration stage.
- `lockstep_delay_x_latency`: Crosses `lockstep_delay_cp` with `delay_mismatch_detection_latency_cp` to verify that detection latency strictly adheres to the pipeline delay stage.

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`) provide stimulus that exercises these coverpoints across delay configurations.
