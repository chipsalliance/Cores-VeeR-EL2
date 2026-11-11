# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages and 0-delay mode.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` covergroup along with fault trigger path classification logic.
- **`el2_ifu_icache_ecc_recovery_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_ifu_icache_ecc_recovery_cov` and `el2_ifu_icache_core_check_cov` covergroups for ICache core-side ECC/parity fault recovery and bank check alignment.
- **`el2_lsu_dccm_wr_readback_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_lsu_dccm_wr_readback_cov` covergroup for DCCM write-readback protection.
- **`el2_core_ecc_threshold_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_core_ecc_threshold_cov` covergroup for Multi-Memory Core RAS ECC Threshold Alerts (`MDCCMECT`, `MICCMECT`, `MICECT`).
- **`el2_veer_lockstep_asymmetric_fault_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_asymmetric_fault_cov` covergroup for DCLS Asymmetric Shadow Core Fault Divergence.
- **`el2_veer_lockstep_internal_state_tamper_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_internal_state_tamper_cov` covergroup for DCLS Internal Core Architectural State Tamper (`a5`/`x15` GPR, `q0pcff` PC, and `mtvec_ff` CSR across lockstep delays `0..4` and warm-reset recovery).
- **`el2_veer_lockstep_fcov_bind.sv`**: Unified testbench functional coverage binding module (`el2_veer_lockstep_fcov_bind`) that binds all coverage interfaces (`el2_veer_lockstep_delay_cov_if`, `el2_ifu_icache_ecc_recovery_cov_if`, `el2_lsu_dccm_wr_readback_cov_if`, `el2_core_ecc_threshold_cov_if`, `el2_veer_lockstep_asymmetric_fault_cov_if`, `el2_veer_lockstep_internal_state_tamper_cov_if`) into their target RTL modules under VCS and Verilator.

## Coverage Architecture

### Task 1: DCLS Delay Configuration & 0-Delay Mode (`el2_veer_lockstep_delay_cov`)

1. **`lockstep_delay_cp`**:
   Monitors all supported values of parameter `pt.LOCKSTEP_DELAY` (`delay_0` through `delay_4`) when `corruption_detected_o` asserts `El2MuBiTrue`.
2. **`error_path_cp`**:
   Classifies the active fault trigger path when `corruption_detected_o` asserts `El2MuBiTrue` (`ctrl_fault` vs. `datapath_fault`).
3. **Cross Coverage**:
   - `lockstep_delay_x_error_path`: Crosses `lockstep_delay_cp` with `error_path_cp` to verify that both control-port faults and core datapath/regfile divergences are detected across every supported pipeline delay stage (`0..4`).

### Task 6: DCCM Write Readback Protection (`el2_lsu_dccm_wr_readback_cov`)

1. **`dccm_wr_readback_enabled_cp`**:
   - `feature_enabled` (`RdbkHwEnabled` & `!dec_tlu_dccm_wr_readback_disable`) vs. `feature_disabled` (`!RdbkHwEnabled` | `dec_tlu_dccm_wr_readback_disable`).
2. **`readback_steal_vs_snoop_cp`**:
   - `steal_cycle` (idle cycle steal) vs. `snoop_cycle` (active load snoop).
3. **`write_readback_error_pin_cp`**:
   - `no_error` vs. `error_asserted` (`dccm_wr_readback_error`).
4. **`dmi_first_fault_wins_registers_cp` (`#561`)**:
   - Covers `fault_valid_set`, `fault_addr_captured`, `fault_data_captured`, `fault_ecc_captured`, `fault_clear_w1c`, and `subsequent_fault_ignored`.
5. **Bug Regression & Cross Coverpoints (`#566`, `#572`)**:
   - `readback_mismatch_hamming_weight_cp`: Covers `no_bit_mismatch`, `single_bit_mismatch_sbe`, and `multi_bit_mismatch_dbe` (`#566`).
   - `snoop_bank_select_cp`: Covers `snoop_lo_bank` and `snoop_hi_bank` (`#572`).
   - `pending_readback_deferral_cp`: Covers `stbuf_drain_deferred`, `dma_write_deferred`, and `readback_deferred_by_ecc_scrub` (`#566`, `#572`).
   - `readback_mode_x_error_pin`: Crosses `readback_steal_vs_snoop_cp` with `write_readback_error_pin_cp`.
   - `readback_mode_x_mismatch_weight`: Crosses `readback_steal_vs_snoop_cp` with `readback_mismatch_hamming_weight_cp`.

### Task 7: Multi-Memory Core RAS ECC Threshold Alerts (`el2_core_ecc_threshold_cov`)

1. **`MDCCMECT` (`0x7F2` - DCCM)**:
   - `dccm_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `dccm_sbe_incr` is active.
   - `dccm_counter_increment_cp`: Single-bit ECC error counter increment (`sbe_incr`).
   - `dccm_thresh_x_sbe_incr`: Crosses `dccm_threshold_values_cp` with `dccm_counter_increment_cp`.
   - `dccm_counter_comparison_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.
2. **`MICCMECT` (`0x7F1` - ICCM)**:
   - `iccm_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `iccm_sbe_incr` is active.
   - `iccm_counter_increment_cp`: Instruction fetch SBE (`fetch_sbe_incr`) and DMA read SBE (`dma_sbe_incr`) counter increments.
   - `iccm_thresh_x_sbe_incr`: Crosses `iccm_threshold_values_cp` with `iccm_counter_increment_cp`.
   - `iccm_threshold_trigger_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.
3. **`MICECT` (`0x7F0` - ICache)**:
   - `icache_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `icache_sbe_incr` is active.
   - `icache_counter_increment_cp`: Cache fetch parity/ECC error counter increment (`sbe_incr`).
   - `icache_thresh_x_sbe_incr`: Crosses `icache_threshold_values_cp` with `icache_counter_increment_cp`.
   - `icache_threshold_trigger_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.
4. **`core_ecc_interrupt_generation_cp`**:
   - `interrupt_masked`: `ce_int` asserted while `mie[30] == 0` or `mstatus.MIE == 0`.
   - `interrupt_taken`: Core takes Machine Correctable Error Interrupt trap (`take_ce_int`, `mcause == 0x8000001e`).

### Task 8: DCLS Asymmetric Shadow Core Fault Divergence (`el2_veer_lockstep_asymmetric_fault_cov`)

1. **`asymmetric_fault_source_cp`**:
   - `dccm_asymmetric`: Asymmetric DCCM threshold alert active (`mdccmect` mismatch, Case 203).
   - `iccm_asymmetric`: Asymmetric ICCM threshold alert active (`miccmect` mismatch, Case 204).
   - `icache_asymmetric`: Asymmetric ICache threshold alert active (`micect` mismatch, Case 205).
2. **`asymmetric_lockstep_response_cp`**:
   - `comparator_mismatch`: Subordinate alert causes execution/regfile divergence (`corruption_detected_o == El2MuBiTrue`).
   - `external_interrupt_fired`: Lockstep mismatch interrupt signals to PIC (`extintsrc_req[2]`).
3. **`lockstep_delay_cp`**:
   - Configured lockstep pipeline delay (`delay_0` through `delay_4`) during asymmetric fault detection.
4. **`asymmetric_source_x_delay_cross`**:
   - Crosses `asymmetric_fault_source_cp` with `lockstep_delay_cp` (`delay_0` through `delay_4`).

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
   - `icache_fault_x_recovery_action`: Crosses `icache_fault_type_cp` with `icache_recovery_action_cp`.
   - `icache_protection_x_fault_x_waypack_x_ways`: Crosses `icache_protection_mode_cp`, `icache_fault_type_cp`, `icache_waypack_cp`, and `icache_num_ways_cp`.
6. **Issue `#569` / PR `#571` Core-Side Bank Check, Bank Select & Byte Rotator Alignment (`el2_ifu_icache_core_check_cov`)**:
   - `icache_bank_check_en_cp`: Covers `primary_bank_only` (`2'b01`), `both_banks_checked` (`2'b11`), and `check_disabled_or_masked` (`2'b00`, `2'b10`) on `ic_bank_check_en`.
   - `icache_rotator_offset_cp`: Covers `rot_offset_00`, `rot_offset_01`, `rot_offset_10`, and `rot_offset_11_straddle` on `ic_rd_rot_sel`.
   - `icache_straddle_bank_check_cp`: Covers `bank0_to_bank1_straddle` and `bank1_to_bank0_straddle` on cross-bank straddling fetches (`addr[2:1] == 2'b11`).
   - `icache_bank_sel_cp`: Covers `lower_chunk_in_bank0` (`1'b0`) vs. `lower_chunk_in_bank1` (`1'b1`) on `ic_rd_bank_sel`.
   - `icache_rotator_x_bank_sel`: Crosses `icache_rotator_offset_cp` with `icache_bank_sel_cp`.

### Task 10: DCLS Internal Core Architectural State Tamper (`el2_veer_lockstep_internal_state_tamper_cov`)

1. **`internal_tamper_target_cp`**:
   - `gpr_tamper`: Bit-flip in general purpose register (`a5` / `x15`, Case 200).
   - `pc_tamper`: Bit-flip in fetch queue program counter flop (`q0pcff`, Case 201).
   - `csr_tamper`: Bit-flip in trap vector base CSR flop (`mtvec_ff`, Case 202).
2. **`internal_tamper_detection_cp`**:
   - `trapped_and_recovered`: Divergence detected (`corruption_detected_o == El2MuBiTrue`), external interrupt trap taken (`extintsrc_req[2]`), hardware forces released (`0x95`), and warm-reset resynchronization (`0x96`) succeeds.
3. **`lockstep_delay_cp`**:
   - Configured lockstep pipeline delay (`delay_0` through `delay_4`) during internal state tamper detection.
4. **`internal_tamper_x_delay_cross`**:
   - Crosses `internal_tamper_target_cp` with `lockstep_delay_cp` (`delay_0` through `delay_4`).

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv`.
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`) provide stimulus that exercises these coverpoints across delay configurations.
