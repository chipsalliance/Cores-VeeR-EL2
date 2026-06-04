// Copyright 2024 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0
`ifndef VERILATOR

`ifdef FCOV
`ifdef RV_LOCKSTEP_ENABLE
bind el2_veer_lockstep dcls_fcov dcls_fcov_bind (
    .clk(clk),
    .rst_l(rst_l),
    .dbg_rst_l(dbg_rst_l),
    .core_rst_l(core_rst_l),
    .lockstep_err_injection_en_i(lockstep_err_injection_en_i),
    .disable_corruption_detection_i(disable_corruption_detection_i),
    .corruption_detected_o(corruption_detected_o),
    .rst_shadow(rst_shadow),
    .rst_dbg_shadow(rst_dbg_shadow),
    .rst_n(rst_n),
    .outputs_corrupted(outputs_corrupted),
    .corruption_detected(corruption_detected),
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    .regfile_corrupted(regfile_corrupted)
`endif //ifdef RV_LOCKSTEP_REGFILE_ENABLE
);
`endif //ifdef FCOV
`endif //ifdef FCOV
`endif //ifndef VERILATOR 
