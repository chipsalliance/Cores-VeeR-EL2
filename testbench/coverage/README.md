# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages, 0-delay mode, and core debug mode suppression and transitions.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) along with combinational fault-to-detection latency tracking logic.
- **`el2_veer_lockstep_debug_mode_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_debug_mode_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) for core debug mode entry/exit transitions and DCLS corruption reporting suppression during debug mode.
- **`el2_veer_lockstep_fcov_bind.sv`**: Testbench binding module (`el2_veer_lockstep_fcov_bind`) that binds `el2_veer_lockstep_delay_cov_if` and `el2_veer_lockstep_debug_mode_cov_if` to `el2_veer_lockstep`.

## Coverage Architecture

### Task 1: DCLS Delay Configuration and 0-Delay Mode Coverage (`el2_veer_lockstep_delay_cov`)

#### 1. `lockstep_delay_cp`
Monitors all supported values of parameter `pt.LOCKSTEP_DELAY`:
- `delay_0`: `LOCKSTEP_DELAY == 0` (Combinatorial bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops).
- `delay_1`: `LOCKSTEP_DELAY == 1`
- `delay_2`: `LOCKSTEP_DELAY == 2`
- `delay_3`: `LOCKSTEP_DELAY == 3`
- `delay_4`: `LOCKSTEP_DELAY == 4`

#### 2. `delay_mismatch_detection_latency_cp`
Measures the clock cycle latency from the cycle of fault injection / divergence onset to the cycle where `corruption_detected_o` asserts `El2MuBiTrue`:
- `delay_0`: Latency must be 0 to 1 cycle (`latency_0`, `latency_1`).
- `delay_N` ($N \in \{1, 2, 3, 4\}$): Latency must match the configured pipeline delay stage (`latency_N`).

#### 3. `corruption_detected_cp`
Tracks `corruption_detected_o` assertion to `El2MuBiTrue`.

#### 4. Cross Coverage
- `lockstep_delay_x_corruption`: Crosses `lockstep_delay_cp` with `corruption_detected_cp` to guarantee divergence is caught across every supported delay configuration stage.
- `lockstep_delay_x_latency`: Crosses `lockstep_delay_cp` with `delay_mismatch_detection_latency_cp` to verify that detection latency strictly adheres to the pipeline delay stage.

### Task 2: DCLS Core Debug Mode Suppression and Transition Coverage (`el2_veer_lockstep_debug_mode_cov`)

#### 1. `core_debug_state_cp`
Monitors the core debug and DCLS debug suppression state (`dec_tlu_debug_mode` / `dbg_detected`):
- `normal_run`: `dec_tlu_debug_mode == 0` (normal execution without debug suppression).
- `debug_halt`: `dec_tlu_debug_mode == 1` (debug halt / latched DCLS debug suppression active).

#### 2. `debug_transition_cp`
Tracks transitions on `dec_tlu_debug_mode` (`o_debug_mode_status`):
- `enter_debug`: Transition bin `0 => 1` upon entering debug halt mode.
- `exit_debug`: Transition bin `1 => 0` upon resuming from debug halt mode.

#### 3. `debug_suppression_behavior_cp`
Verifies DCLS error reporting suppression during debug mode and active reporting in normal run mode:
- `debug_active_error_suppressed`: When debug mode is active and a core divergence or error injection is present, `corruption_detected_o` remains `El2MuBiFalse`.
- `run_active_error_reported`: When in normal run mode and a core divergence or error injection is present, `corruption_detected_o` asserts `El2MuBiTrue`.

#### 4. Cross Coverage
- `debug_state_x_corruption`: Crosses `core_debug_state_cp` with `outputs_corrupted_cp` and `corruption_detected_cp` to verify DCLS disable during debug mode and active detection during normal execution.

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_debug`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`) provide stimulus that exercises these coverpoints across delay configurations and debug mode transitions.
