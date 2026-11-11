# VeeR EL2 Testbench Coverage Subsystem

This directory contains testbench-level functional coverage interfaces and binding modules for the VeeR EL2 Dual-Core Lockstep (DCLS) subsystem, addressing the verification requirements and gap analysis for configurable pipeline delay stages, 0-delay mode, core debug mode suppression and transitions, Multi-Bit Integrity (MUBI) encoding and fail-secure tamper coverage, Memory Address XOR Infection coverage, and Register File Read Port Comparison coverage.

## Files

- **`el2_veer_lockstep_delay_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_delay_cov` IEEE 1800 covergroup along with fault trigger path classification logic.
- **`el2_veer_lockstep_debug_mode_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_debug_mode_cov` IEEE 1800 covergroup for core debug mode entry/exit transitions and DCLS corruption reporting suppression during debug mode.
- **`el2_veer_lockstep_mubi_sweep_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_mubi_sweep_cov` IEEE 1800 covergroup for MUBI width configurations, control signal encoding validation, and fail-secure tamper protection.
- **`el2_veer_lockstep_address_xor_infection_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_address_xor_infection_cov` IEEE 1800 covergroup for ICCM, DCCM, and ICache address-XOR infection, DCLS-domain `iccm_rd_data` divergence detection, ICCM DMA read word-enable masking (Issue #550), ICCM redundant row lane selection and CAM re-reads (Issue #562), and DCLS-internal ICache bank select and cacheline-wrap straddle check masking (Issue #569).
- **`el2_veer_lockstep_regfile_read_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_regfile_read_cov` IEEE 1800 covergroup for register file read port comparison modes, `rd0`/`rd1` read data divergence, architectural register divergence, and D-stage instruction type coverage.
- **`el2_lsu_dccm_wr_readback_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_lsu_dccm_wr_readback_cov` IEEE 1800 covergroup for DCCM write-readback protection.
- **`el2_core_ecc_threshold_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_core_ecc_threshold_cov` IEEE 1800 covergroup for Multi-Memory Core RAS ECC Threshold Alerts (`MDCCMECT`, `MICCMECT`, `MICECT`).
- **`el2_veer_lockstep_asymmetric_fault_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_asymmetric_fault_cov` IEEE 1800 covergroup for DCLS Asymmetric Shadow Core Fault Divergence.
- **`el2_ifu_icache_ecc_recovery_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_ifu_icache_ecc_recovery_cov` and `el2_ifu_icache_core_check_cov` IEEE 1800 covergroups for ICache core-side ECC/parity fault recovery and bank check alignment.
- **`el2_veer_lockstep_internal_state_tamper_cov_if.sv`**: Dedicated SystemVerilog coverage interface encapsulating the `el2_veer_lockstep_internal_state_tamper_cov` IEEE 1800 covergroup for DCLS Internal Core Architectural State Tamper (`a5`/`x15` GPR, `q0pcff` PC, and `mtvec_ff` CSR across lockstep delays `0..4` and warm-reset recovery).
- **`el2_veer_lockstep_fcov_bind.sv`**: Testbench binding module (`el2_veer_lockstep_fcov_bind`) that binds `el2_veer_lockstep_delay_cov_if`, `el2_veer_lockstep_debug_mode_cov_if`, `el2_veer_lockstep_mubi_sweep_cov_if`, and `el2_veer_lockstep_regfile_read_cov_if` to `el2_veer_lockstep`, and binds `el2_veer_lockstep_address_xor_infection_cov_if` to `el2_veer_wrapper`, along with `el2_lsu_dccm_wr_readback_cov_if` to `el2_lsu_dccm_ctl`, `el2_core_ecc_threshold_cov_if` to `el2_dec_tlu_ctl`, `el2_veer_lockstep_asymmetric_fault_cov_if` to `el2_veer_wrapper`, `el2_ifu_icache_ecc_recovery_cov_if` to `el2_ifu_mem_ctl`, `el2_veer_lockstep_internal_state_tamper_cov_if` to `el2_veer_wrapper`.

## Coverage Architecture

### Task 1: DCLS Delay Configuration and 0-Delay Mode Coverage (`el2_veer_lockstep_delay_cov`)

#### 1. `lockstep_delay_cp`
Monitors all supported values of parameter `pt.LOCKSTEP_DELAY` when `corruption_detected_o` asserts `El2MuBiTrue`:
- `delay_0`: `LOCKSTEP_DELAY == 0` (Combinational bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops).
- `delay_1`: `LOCKSTEP_DELAY == 1`
- `delay_2`: `LOCKSTEP_DELAY == 2`
- `delay_3`: `LOCKSTEP_DELAY == 3`
- `delay_4`: `LOCKSTEP_DELAY == 4`

#### 2. `error_path_cp`
Classifies the active fault trigger path when `corruption_detected_o` asserts `El2MuBiTrue`:
- `ctrl_fault`: Control-port error injection (`lockstep_err_injection_en_i`) or invalid multi-bit control encoding (`ctrl_fault_inject`).
- `datapath_fault`: Core output or register-file comparator divergence (`datapath_divergence`).

#### 3. Cross Coverage
- `lockstep_delay_x_error_path`: Crosses `lockstep_delay_cp` with `error_path_cp` to verify that both control-port faults and core datapath/regfile divergences are detected across every supported pipeline delay stage (`0..4`).

### Task 2: DCLS Core Debug Mode Suppression and Transition Coverage (`el2_veer_lockstep_debug_mode_cov`)

#### 1. `core_debug_state_cp`
Monitors the registered DCLS debug suppression state (`dbg_detected`):
- `normal_run`: `dbg_detected == El2MuBiFalse` (normal execution without debug suppression).
- `debug_halt`: `dbg_detected == El2MuBiTrue` (latched DCLS debug suppression active).

#### 2. `debug_transition_cp`
Tracks transitions on `dec_tlu_debug_mode` (`o_debug_mode_status`):
- `enter_debug`: Transition bin `0 => 1` upon entering debug halt mode.
- `exit_debug`: Transition bin `1 => 0` upon resuming from debug halt mode.

#### 3. `debug_suppression_behavior_cp`
Verifies DCLS error reporting suppression during debug mode and active reporting in normal run mode when `disable_corruption_detection_i == El2MuBiFalse`:
- `debug_active_error_suppressed`: When debug suppression (`dbg_detected`) is active and a core divergence or error injection is present, `corruption_detected_o` remains `El2MuBiFalse`.
- `run_active_error_reported`: When in normal run mode (`dbg_detected == El2MuBiFalse`) and a core divergence or error injection is present, `corruption_detected_o` asserts `El2MuBiTrue`.

#### 4. Cross Coverage
- `debug_state_x_corruption`: Crosses `debug_state_qual_cp` with `outputs_corrupted_cp` (qualified by `disable_corruption_detection_i == El2MuBiFalse` and expected `corruption_detected_o` response) to verify DCLS disable during debug mode and active detection during normal execution.

### Task 3: Multi-Bit Integrity (MUBI) Comprehensive Encoding and Fail-Secure Coverage (`el2_veer_lockstep_mubi_sweep_cov`)

#### 1. `mubi_width_config_cp`
Monitors all supported MUBI width configurations (`pt.MUBI_WIDTH` / `El2MuBiWidth`) when `corruption_detected_o` asserts `El2MuBiTrue`:
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
- `corrupted_disable_with_fault`: When `disable_corruption_detection_i` has an invalid pattern and an active fault or datapath/regfile divergence is present, `corruption_detected_o` asserts `El2MuBiTrue`.

#### 5. Cross Coverage
- `disable_ctrl_x_corruption`: Crosses `disable_mode_resp_cp` (`disable_true`, `disable_false`, `disable_invalid` qualified by expected `corruption_detected_o` response) with `fault_present_cp` (`no_fault`, `fault_active`), confirming that invalid `disable_corruption_detection_i` encodings fail secure both with and without an active fault.
- `valid_disable_x_fault_source`: Crosses `valid_disable_resp_cp` (`disable_true`, `disable_false`) with `fault_source_cp` (`no_fault`, `ctrl_fault`, `datapath_mismatch` covering `outputs_corrupted || regfile_corrupted`) to confirm both fault paths are suppressed when disabled and reported when enabled.

### Task 4: Memory Address XOR Infection Coverage (`el2_veer_lockstep_address_xor_infection_cov`)

#### 1. `iccm_xor_infection_cp`
Monitors ICCM address-XOR infection faults and DCLS subordinate core ICCM divergence:
- `iccm_xor_active`: `RV_ICCM_ADDR_XOR == 1` with an active ICCM ECC error or address/data divergence.
- `iccm_mismatch_detected`: Subordinate core ICCM address or datapath divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 2. `dccm_xor_infection_cp`
Monitors DCCM address-XOR infection faults and DCLS subordinate core DCCM divergence:
- `dccm_xor_active`: `RV_DCCM_ADDR_XOR == 1` with an active DCCM ECC/readback error or address/data divergence.
- `dccm_mismatch_detected`: Subordinate core DCCM address or datapath divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 3. `icache_xor_infection_cp`
Monitors ICache address-XOR infection faults and DCLS subordinate core ICache divergence:
- `icache_xor_active`: `RV_ICACHE_ADDR_XOR == 1` with an active ICache parity/ECC error (`ic_perr_r` / `ic_tag_perr`) or address/data divergence.
- `icache_mismatch_detected`: Subordinate core ICache address, datapath, or control divergence triggers DCLS mismatch (`corruption_detected_o == El2MuBiTrue`).

#### 4. `iccm_rd_data_divergence_cp`
Verifies DCLS-domain F-stage `iccm_rd_data` divergence detection (commit `0b61bfd`):
- `iccm_rd_data_divergence_caught`: Directly compares the `LockstepDelay`-aligned main-core and shadow-core F-stage `iccm_rd_data` signals inside `el2_ifu_mem_ctl` during ICCM reads and confirms DCLS reports `corruption_detected_o == El2MuBiTrue`.

#### 5. `iccm_dma_rd_xor_cp` (Issue #550 / PR #552)
Verifies ICCM DMA read word-enable masking under `RV_ICCM_ADDR_XOR == 1`:
- `dma_rd_word_even_no_false_err`, `dma_rd_word_odd_no_false_err`: 32-bit even and odd word DMA reads complete without spurious double-bit ECC errors on the unrequested lane.
- `dma_rd_dword_both_en`: 64-bit doubleword DMA read enables ECC checking across both 32-bit lanes.

#### 6. `iccm_redundant_row_xor_corr_cp` and `iccm_redundant_row_xor_reread_cp` (Issue #562 / PR #565)
Verifies ICCM 2-entry redundant row single-bit ECC correction and re-fetch under `RV_ICCM_ADDR_XOR == 1`:
- `corr_even_word_lane0`, `corr_odd_word_lane1`: Single-bit ECC correction writebacks (`iccm_buf_correct_ecc`) on even (`iccm_rw_addr[2] == 0`) and odd (`iccm_rw_addr[2] == 1`) words.
- `reread_even_redundant_clean`, `reread_odd_redundant_clean`: Clean re-fetches hitting a valid even or odd entry in `el2_ifu_iccm_mem` (`sel_red0` / `sel_red1` and `redundant_address`) without double-bit ECC errors.

#### 7. `icache_dcls_bank_sel_xor_cp`, `icache_dcls_cl_wrap_straddle_cp`, and `icache_dcls_ctrl_divergence_cp` (Issue #569 / PR #571)
Verifies DCLS-internal ICache bank selection, cacheline-wrap upper-bank check suppression, and main-vs-shadow control divergence:
- `lower_chunk_in_bank0`, `lower_chunk_in_bank1`: F2-stage `ic_rd_bank_sel` exercising both unswapped and swapped physical bank orderings under `RV_ICACHE_ADDR_XOR == 1`.
- `straddle_intra_line_both_checked`, `straddle_cl_wrap_upper_dropped`: Halfword-straddling fetches (`ic_rd_rot_sel == 2'b11`) checking both banks within a cacheline versus suppressing the upper-bank check on a 64B cacheline wrap.
- `dcls_icache_ctrl_mismatch_caught`: Main-vs-shadow divergence on DCLS-internal ICache read controls caught with `corruption_detected_o == El2MuBiTrue`.

### Task 5: Register File Read Port Comparison Coverage (`el2_veer_lockstep_regfile_read_cov`)

#### 1. `regfile_read_enable_config_cp`
Monitors the register file DCLS comparison configuration (`RV_LOCKSTEP_REGFILE_READ_ENABLE`) when an active register divergence is present:
- `full_regfile_mode`: `RV_LOCKSTEP_REGFILE_READ_ENABLE == 0` (flop subset comparison of `ra`, `sp`, `s0/fp`, and `a0`–`a7`).
- `read_port_mode`: `RV_LOCKSTEP_REGFILE_READ_ENABLE == 1` (read port `rd0`/`rd1` comparison across all 31 GPRs).

#### 2. `regfile_read_port_diff_cp`
Tracks divergence on the register file read ports between the `rst_l`-aligned delayed main core and subordinate shadow core:
- `rd0_divergence`: Main core `rd0` data differs from shadow core `rd0` data (`raddr0 != 0`).
- `rd1_divergence`: Main core `rd1` data differs from shadow core `rd1` data (`raddr1 != 0`).

#### 3. `target_register_divergence_cp`
Tracks which architectural register differed on the active divergence cycle:
- `zero_x0`: Zero register `x0` (`ignore_bins` in coverage, while non-coverage-gated SVA assertions in `testbench/veer_wrapper.sv` verify `x0` read ports always return zero).
- `ra`: Return address `x1`.
- `sp`: Stack pointer `x2`.
- `s0_fp`, `s1`: Saved registers `x8` and `x9`.
- `a0`–`a7`: Argument registers `x10` through `x17`.
- `t0`–`t6`: Temporary registers `x5` through `x7` and `x28` through `x31`.

#### 4. `instr_type_cp` and Cross Coverage
- `instr_type_cp`: Tracks D-stage instruction classification (`alu`, `branch`, `store`, `load_addr`) executing while a register divergence is active.
- `target_register_x_instr_type`: Crosses `target_register_divergence_cp` with `alu_instr_cp` (`alu` qualified by active register divergence) across all 19 monitored architectural registers.

### Task 6: DCCM Write Readback Protection (`el2_lsu_dccm_wr_readback_cov`)

#### 1. `dccm_wr_readback_enabled_cp`
- `feature_enabled` (`RdbkHwEnabled` & `!dec_tlu_dccm_wr_readback_disable`) vs. `feature_disabled` (`!RdbkHwEnabled` | `dec_tlu_dccm_wr_readback_disable`).

#### 2. `readback_steal_vs_snoop_cp`
- `steal_cycle` (idle cycle steal) vs. `snoop_cycle` (active load snoop).

#### 3. `write_readback_error_pin_cp`
- `no_error` vs. `error_asserted` (`dccm_wr_readback_error`).

#### 4. `dmi_first_fault_wins_registers_cp` (Issue #561)
- Covers `fault_valid_set`, `fault_addr_captured`, `fault_data_captured`, `fault_ecc_captured`, `fault_clear_w1c`, and `subsequent_fault_ignored`.

#### 5. Bug Regression & Cross Coverpoints (Issues #566 & #572)
- `readback_mismatch_hamming_weight_cp`: Covers `no_bit_mismatch`, `single_bit_mismatch_sbe`, and `multi_bit_mismatch_dbe` (Issue #566).
- `snoop_bank_select_cp`: Covers `snoop_lo_bank` and `snoop_hi_bank` (Issue #572).
- `pending_readback_deferral_cp`: Covers `stbuf_drain_deferred`, `dma_write_deferred`, and `readback_deferred_by_ecc_scrub` (Issues #566 & #572).
- `readback_mode_x_error_pin`: Crosses `readback_steal_vs_snoop_cp` with `write_readback_error_pin_cp`.
- `readback_mode_x_mismatch_weight`: Crosses `readback_steal_vs_snoop_cp` with `readback_mismatch_hamming_weight_cp`.

### Task 7: Multi-Memory Core RAS ECC Threshold Alerts (`el2_core_ecc_threshold_cov`)

#### 1. `MDCCMECT` (`0x7F2` - DCCM)
- `dccm_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `dccm_sbe_incr` is active.
- `dccm_counter_increment_cp`: Single-bit ECC error counter increment (`sbe_incr`).
- `dccm_thresh_x_sbe_incr`: Crosses `dccm_threshold_values_cp` with `dccm_counter_increment_cp`.
- `dccm_counter_comparison_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.

#### 2. `MICCMECT` (`0x7F1` - ICCM)
- `iccm_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `iccm_sbe_incr` is active.
- `iccm_counter_increment_cp`: Instruction fetch SBE (`fetch_sbe_incr`) and DMA read SBE (`dma_sbe_incr`) counter increments.
- `iccm_thresh_x_sbe_incr`: Crosses `iccm_threshold_values_cp` with `iccm_counter_increment_cp`.
- `iccm_threshold_trigger_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.

#### 3. `MICECT` (`0x7F0` - ICache)
- `icache_threshold_values_cp`: Threshold exponent bins (`0, 1, 2, 4, 8, 16, 26`), sampled when `icache_sbe_incr` is active.
- `icache_counter_increment_cp`: Cache fetch parity/ECC error counter increment (`sbe_incr`).
- `icache_thresh_x_sbe_incr`: Crosses `icache_threshold_values_cp` with `icache_counter_increment_cp`.
- `icache_threshold_trigger_cp`: `count_below_thresh`, `count_at_thresh`, and `count_above_thresh`.

#### 4. `core_ecc_interrupt_generation_cp`
- `interrupt_masked`: `ce_int` asserted while `mie[30] == 0` or `mstatus.MIE == 0`.
- `interrupt_taken`: Core takes Machine Correctable Error Interrupt trap (`take_ce_int`, `mcause == 0x8000001e`).

### Task 8: DCLS Asymmetric Shadow Core Fault Divergence (`el2_veer_lockstep_asymmetric_fault_cov`)

#### 1. `asymmetric_fault_source_cp`
- `dccm_asymmetric`: Asymmetric DCCM threshold alert active (`mdccmect` mismatch, Case 203).
- `iccm_asymmetric`: Asymmetric ICCM threshold alert active (`miccmect` mismatch, Case 204).
- `icache_asymmetric`: Asymmetric ICache threshold alert active (`micect` mismatch, Case 205).

#### 2. `asymmetric_lockstep_response_cp`
- `comparator_mismatch`: Subordinate alert causes execution/regfile divergence (`corruption_detected_o == El2MuBiTrue`).
- `external_interrupt_fired`: Lockstep mismatch interrupt signals to PIC (`extintsrc_req[2]`).

#### 3. `lockstep_delay_cp` and Cross Coverage
- `lockstep_delay_cp`: Configured lockstep pipeline delay (`delay_0` through `delay_4`) during asymmetric fault detection.
- `asymmetric_source_x_delay_cross`: Crosses `asymmetric_fault_source_cp` with `lockstep_delay_cp` (`delay_0` through `delay_4`).

### Task 9: ICache Core-Side ECC and Parity Fault Recovery (`el2_ifu_icache_ecc_recovery_cov` & `el2_ifu_icache_core_check_cov`)

#### 1. `icache_protection_mode_cp`, `icache_waypack_cp`, and `icache_num_ways_cp`
- `icache_protection_mode_cp`: `parity_mode` (`pt.ICACHE_ECC == 0`) vs. `secded_mode` (`pt.ICACHE_ECC == 1`).
- `icache_waypack_cp`: `waypack_0` vs. `waypack_1`.
- `icache_num_ways_cp`: `num_ways_2` vs. `num_ways_4`.

#### 2. `icache_fault_type_cp` and `icache_recovery_action_cp`
- `icache_fault_type_cp`: Covers `single_bit_data_error`, `single_bit_tag_error`, and `double_bit_uncorrectable_error`.
- `icache_recovery_action_cp`: Covers `pipeline_squash_and_flush`, `micect_counter_increment`, and `refetch_success`.

#### 3. Recovery Cross Coverage
- `icache_fault_x_recovery_action`: Crosses `icache_fault_type_cp` with `icache_recovery_action_cp`.
- `icache_protection_x_fault_x_waypack_x_ways`: Crosses `icache_protection_mode_cp`, `icache_fault_type_cp`, `icache_waypack_cp`, and `icache_num_ways_cp`.

#### 4. Core-Side Bank Check, Bank Select & Byte Rotator Alignment (`el2_ifu_icache_core_check_cov`, Issue #569 / PR #571)
- `icache_bank_check_en_cp`: Covers `primary_bank_only` (`2'b01`), `both_banks_checked` (`2'b11`), and `check_disabled_or_masked` (`2'b00`, `2'b10`) on `ic_bank_check_en`.
- `icache_rotator_offset_cp`: Covers `rot_offset_00`, `rot_offset_01`, `rot_offset_10`, and `rot_offset_11_straddle` on `ic_rd_rot_sel`.
- `icache_straddle_bank_check_cp`: Covers `bank0_to_bank1_straddle` and `bank1_to_bank0_straddle` on cross-bank straddling fetches (`addr[2:1] == 2'b11`).
- `icache_bank_sel_cp`: Covers `lower_chunk_in_bank0` (`1'b0`) vs. `lower_chunk_in_bank1` (`1'b1`) on `ic_rd_bank_sel`.
- `icache_rotator_x_bank_sel`: Crosses `icache_rotator_offset_cp` with `icache_bank_sel_cp`.

### Task 10: DCLS Internal Core Architectural State Tamper (`el2_veer_lockstep_internal_state_tamper_cov`)

#### 1. `internal_tamper_target_cp`
- `gpr_tamper`: Bit-flip in general purpose register (`a5` / `x15`, Case 200).
- `pc_tamper`: Bit-flip in fetch queue program counter flop (`q0pcff`, Case 201).
- `csr_tamper`: Bit-flip in trap vector base CSR flop (`mtvec_ff`, Case 202).

#### 2. `internal_tamper_detection_cp`
- `trapped_and_recovered`: Divergence detected (`corruption_detected_o == El2MuBiTrue`), external interrupt trap taken (`extintsrc_req[2]`), hardware forces released (`0x95`), and warm-reset resynchronization (`0x96`) succeeds.

#### 3. `lockstep_delay_cp` and Cross Coverage
- `lockstep_delay_cp`: Configured lockstep pipeline delay (`delay_0` through `delay_4`) during internal state tamper detection.
- `internal_tamper_x_delay_cross`: Crosses `internal_tamper_target_cp` with `lockstep_delay_cp` (`delay_0` through `delay_4`).

## Testbench & CI Integration

The coverage files are compiled via `testbench/flist` and automatically instantiated when building with `+define+FCOV` via `testbench/veer_wrapper.sv` (`dcls_fcov`).
The tests in `testbench/tests/` (e.g., `dcls`, `dcls_debug`, `dcls_error_ctrl`, `dcls_mubi_sweep`, `dcls_ecc_asymmetric`, `dcls_internal_state`, `dcls_regfile_read`, `ecc`, `iccm_addr_xor`, `dccm_addr_xor`, `icache_infection`) provide stimulus that exercises these coverpoints across delay configurations, debug mode transitions, MUBI widths, memory address-XOR infection modes, and register file read comparison modes.
