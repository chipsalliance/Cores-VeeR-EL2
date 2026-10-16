# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages and 0-delay mode.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup (VCS) and SVA `cover property` assertions (Verilator) along with combinational fault-to-detection latency tracking logic.
- **`el2_ifu_icache_ecc_recovery_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_ifu_icache_ecc_recovery_cov` and `el2_ifu_icache_core_check_cov` covergroups (VCS) and SVA `cover property` assertions (Verilator) for ICache core-side ECC/parity fault recovery and bank check alignment.
- **`el2_veer_lockstep_fcov_bind.sv`**: Unified testbench functional coverage binding module (`el2_veer_lockstep_fcov_bind`) that binds the coverage interfaces (`el2_veer_lockstep_delay_cov_if`, `el2_ifu_icache_ecc_recovery_cov_if`) into their target RTL modules under VCS and Verilator.

## Coverage Architecture

### Task 1: DCLS Delay Configuration & 0-Delay Mode (`el2_veer_lockstep_delay_cov`)

1. **`lockstep_delay_cp`**:
   Monitors all supported values of parameter `pt.LOCKSTEP_DELAY` (`delay_0` through `delay_4`).
2. **`delay_mismatch_detection_latency_cp`**:
   Measures the clock cycle latency from the cycle of fault injection / divergence onset to the cycle where `corruption_detected_o` asserts `El2MuBiTrue`.
3. **`corruption_detected_cp`**:
   Tracks `corruption_detected_o` assertion to `El2MuBiTrue`.
4. **Cross Coverage**:
   - `lockstep_delay_x_corruption`: Crosses `lockstep_delay_cp` with `corruption_detected_cp`.
   - `lockstep_delay_x_latency`: Crosses `lockstep_delay_cp` with `delay_mismatch_detection_latency_cp`.

### Task 9: ICache Core-Side ECC and Parity Fault Recovery (`el2_ifu_icache_ecc_recovery_cov` & `el2_ifu_icache_core_check_cov`)

1. **`icache_protection_mode_cp`**:
   - `parity_mode` (`pt.ICACHE_ECC == 0`) vs. `secded_mode` (`pt.ICACHE_ECC == 1`).
2. **`icache_fault_type_cp`**:
   - Covers `single_bit_data_error`, `single_bit_tag_error`, and `double_bit_uncorrectable_error`.
3. **`icache_recovery_action_cp`**:
   - Covers `pipeline_squash_and_flush`, `micect_counter_increment`, and `refetch_success`.
4. **`icache_waypack_cp` & `icache_num_ways_cp`**:
   - Covers `waypack_0` vs. `waypack_1`, and `num_ways_2` vs. `num_ways_4`.
5. **Recovery Cross Coverage**:
   - `icache_protection_x_fault_x_waypack_x_ways`: Crosses `icache_protection_mode_cp`, `icache_fault_type_cp`, `icache_waypack_cp`, and `icache_num_ways_cp`.
   - `icache_fault_x_recovery_action`: Crosses `icache_fault_type_cp` with `icache_recovery_action_cp`.
6. **Issue `#569` Core-Side Bank Check & Byte Rotator Alignment (`el2_ifu_icache_core_check_cov`)**:
   - `icache_bank_check_en_cp`: Covers `primary_bank_only` (`2'b01`), `both_banks_checked` (`2'b11`), and `check_disabled_or_masked` (`2'b00`, `2'b10`).
   - `icache_rotator_offset_cp`: Covers `rot_offset_00`, `rot_offset_01`, `rot_offset_10`, and `rot_offset_11_straddle`.
   - `icache_straddle_bank_check_cp`: Covers `bank0_to_bank1_straddle` and `bank1_to_bank0_straddle` on cross-bank straddling fetches (`addr[2:1] == 2'b11`).
   - `icache_rotator_addr_consistency_cp`: Covers `addr_lo_matched` vs. `addr_lo_mismatched` (`ic_rd_addr_lo` vs. `ifu_fetch_addr_int_f[2:1]`).
   - `icache_rotator_x_bank_check_en`: Crosses `icache_rotator_offset_cp` with `icache_bank_check_en_cp` (excluding non-straddle offsets with `both_banks_checked`).

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`) provide stimulus that exercises these coverpoints across delay configurations.
