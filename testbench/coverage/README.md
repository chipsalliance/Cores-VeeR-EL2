# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages and 0-delay mode.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) along with fault trigger path classification logic.
- **`el2_veer_lockstep_fcov_bind.sv`**: Testbench binding module (`el2_veer_lockstep_fcov_bind`) that binds `el2_veer_lockstep_delay_cov_if` (dual-mode delay and error path coverage under VCS and Verilator) to `el2_veer_lockstep`.

## Coverage Architecture

### 1. `lockstep_delay_cp`
Monitors all supported values of parameter `pt.LOCKSTEP_DELAY` when `corruption_detected_o` asserts `El2MuBiTrue`:
- `delay_0`: `LOCKSTEP_DELAY == 0` (Combinational bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops).
- `delay_1`: `LOCKSTEP_DELAY == 1`
- `delay_2`: `LOCKSTEP_DELAY == 2`
- `delay_3`: `LOCKSTEP_DELAY == 3`
- `delay_4`: `LOCKSTEP_DELAY == 4`

### 2. `error_path_cp`
Classifies the active fault trigger path when `corruption_detected_o` asserts `El2MuBiTrue`:
- `ctrl_fault`: Control-port error injection (`lockstep_err_injection_en_i`) or invalid multi-bit control encoding (`ctrl_fault_inject`).
- `datapath_fault`: Core output or register-file comparator divergence (`datapath_divergence`).

### 3. Cross Coverage
- `lockstep_delay_x_error_path`: Crosses `lockstep_delay_cp` with `error_path_cp` to verify that both control-port faults and core datapath/regfile divergences are detected across every supported pipeline delay stage (`0..4`).

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`) provide stimulus that exercises these coverpoints across delay configurations.
