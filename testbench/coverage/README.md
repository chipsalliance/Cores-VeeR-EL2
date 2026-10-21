# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages, 0-delay mode, core debug mode suppression and transitions, Multi-Bit Integrity (MUBI) encoding and fail-secure tamper coverage, Memory Address XOR Infection coverage, and Register File Read Port Comparison coverage.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) along with combinational fault-to-detection latency tracking logic.
- **`el2_veer_lockstep_debug_mode_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_debug_mode_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) for core debug mode entry/exit transitions and DCLS corruption reporting suppression during debug mode.
- **`el2_veer_lockstep_mubi_sweep_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_mubi_sweep_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) for MUBI width configurations, control signal encoding validation, and fail-secure tamper protection.
- **`el2_veer_lockstep_address_xor_infection_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_address_xor_infection_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) for ICCM, DCCM, and ICache address-XOR infection and DCLS-domain `iccm_rd_data` divergence detection.
- **`el2_veer_lockstep_regfile_read_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_regfile_read_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) for register file read port comparison modes, `rd0`/`rd1` read data divergence, architectural register divergence, and instruction type cross coverage.
- **`el2_veer_lockstep_fcov_bind.sv`**: Testbench binding module (`el2_veer_lockstep_fcov_bind`) that binds `el2_veer_lockstep_delay_cov_if`, `el2_veer_lockstep_debug_mode_cov_if`, `el2_veer_lockstep_mubi_sweep_cov_if`, `el2_veer_lockstep_address_xor_infection_cov_if`, and `el2_veer_lockstep_regfile_read_cov_if` to `el2_veer_lockstep`.

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

### Task 3: Multi-Bit Integrity (MUBI) Comprehensive Encoding and Fail-Secure Coverage (`el2_veer_lockstep_mubi_sweep_cov`)

#### 1. `mubi_width_config_cp`
Monitors all supported MUBI width configurations (`pt.MUBI_WIDTH` / `El2MuBiWidth`):
- `width_2`, `width_4`, `width_8`, `width_16`, `width_32`: Configured 2-bit, 4-bit, 8-bit, 16-bit, and 32-bit MUBI widths.

#### 2. `mubi_error_injection_control_cp`
Tracks valid and corrupted bit patterns on `lockstep_err_injection_en_i`:
- `inj_true`: Value equals `El2MuBiTrue` (injection active).
- `inj_false`: Value equals `El2MuBiFalse` (injection inactive).
- `inj_invalid_hd1_true`, `inj_invalid_hd1_false`, `inj_invalid_all_zeros`, `inj_invalid_all_ones`: Corrupted bit patterns (Hamming distance 1 from True, Hamming distance 1 from False, all-zeros, all-ones).

#### 3. `mubi_disable_detection_control_cp`
Tracks valid and corrupted bit patterns on `disable_corruption_detection_i`:
- `disable_true`: Value equals `El2MuBiTrue` (monitoring disabled, errors suppressed).
- `disable_false`: Value equals `El2MuBiFalse` (normal monitoring enabled).
- `disable_invalid_hd1_true`, `disable_invalid_hd1_false`, `disable_invalid_all_zeros`, `disable_invalid_all_ones`: Corrupted bit patterns (Hamming distance 1 from True, Hamming distance 1 from False, all-zeros, all-ones).

#### 4. `fail_secure_tamper_cp`
Verifies fail-secure tamper protection:
- `corrupted_disable_with_fault`: When `disable_corruption_detection_i` has an invalid pattern and a fault is injected, `corruption_detected_o` asserts `El2MuBiTrue`.

#### 5. Cross Coverage
- `disable_ctrl_x_corruption`: Crosses `mubi_disable_detection_control_cp` [True, False, Invalid] with `outputs_corrupted` [0, 1] and `corruption_detected_o` [True, False].

### Task 4: Memory Address XOR Infection Coverage (`el2_veer_address_xor_infection_cov`)

#### 1. `iccm_xor_infection_cp`
Monitors ICCM address-XOR infection and DCLS subordinate core ICCM divergence:
- `iccm_xor_active`: `ICCM_ADDR_XOR == 1` and address bit inversion / XOR infection fault triggered.
- `iccm_mismatch_detected`: Subordinate core ICCM address or datapath divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 2. `dccm_xor_infection_cp`
Monitors DCCM address-XOR infection and DCLS subordinate core DCCM divergence:
- `dccm_xor_active`: `DCCM_ADDR_XOR == 1` and address bit inversion / XOR infection fault triggered during load or store.
- `dccm_mismatch_detected`: Subordinate core DCCM address or datapath divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 3. `icache_xor_infection_cp`
Monitors ICache address-XOR infection and DCLS subordinate core ICache divergence:
- `icache_xor_active`: `ICACHE_ADDR_XOR == 1` active during instruction fetch / cache access.
- `icache_mismatch_detected`: Subordinate core ICache address or datapath divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 4. `iccm_rd_data_divergence_cp`
Verifies DCLS-domain `iccm_rd_data` divergence detection (commit `0b61bfd`):
- `iccm_rd_data_divergence_caught`: Monitors `delayed_main_iccm_rd_data ^ shadow_iccm_rd_data` (along with ICCM read/write/address divergence in the DCLS domain) to ensure read data divergence is caught when `corruption_detected_o == El2MuBiTrue`.

### Task 5: Register File Read Port Comparison Coverage (`el2_veer_lockstep_regfile_read_cov`)

#### 1. `regfile_read_enable_config_cp`
Monitors the register file DCLS comparison configuration (`RV_LOCKSTEP_REGFILE_READ_ENABLE`):
- `full_regfile_mode`: `RV_LOCKSTEP_REGFILE_READ_ENABLE == 0` (flop subset comparison of `ra`, `sp`, `s0/fp`, and `a0`–`a7`).
- `read_port_mode`: `RV_LOCKSTEP_REGFILE_READ_ENABLE == 1` (read port `rd0`/`rd1` comparison across all 31 GPRs).

#### 2. `regfile_read_port_diff_cp`
Tracks divergence on the register file read ports between the delayed main core and subordinate shadow core:
- `rd0_divergence`: Main core `rd0` data differs from shadow core `rd0` data (`raddr0 != 0`).
- `rd1_divergence`: Main core `rd1` data differs from shadow core `rd1` data (`raddr1 != 0`).

#### 3. `target_register_divergence_cp`
Tracks which architectural register differed when read:
- `zero_x0`: Zero register `x0` (`illegal_bins`, as `x0` is hardwired to zero and must never diverge).
- `ra`: Return address `x1`.
- `sp`: Stack pointer `x2`.
- `s0_fp`, `s1`: Saved registers `x8` and `x9`.
- `a0`–`a7`: Argument registers `x10` through `x17`.
- `t0`–`t6`: Temporary registers `x5` through `x7` and `x28` through `x31`.

#### 4. Cross Coverage
- `target_register_x_instr_type`: Crosses `target_register_divergence_cp` with `instr_type_cp` (`alu`, `branch`, `store`, `load_addr`) executing when the register divergence occurred.

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_debug`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`, `dcls_regfile_read`, `iccm_addr_xor`, `dccm_addr_xor`, `icache_infection`) provide stimulus that exercises these coverpoints across delay configurations, debug mode transitions, MUBI widths, memory address-XOR infection modes, and register file read comparison modes.
