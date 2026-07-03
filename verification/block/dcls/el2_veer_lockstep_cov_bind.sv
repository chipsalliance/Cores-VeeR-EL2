module el2_veer_lockstep_cov_bind
#(
`ifdef FCOV
    `include "el2_param.vh"
`endif
) ();
`ifdef FCOV
    if (pt.LOCKSTEP_DELAY > 0) begin
        bind el2_veer_lockstep el2_veer_lockstep_cov_if el2_veer_lockstep_cov(
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
            .delayed_main_core_regfile(delayed_regfile.delayed_main_core_regfile[pt.LOCKSTEP_DELAY-1].veer_rf_sink),
            .shadow_core_regfile(shadow_core_regfile.veer_rf_sink),
`endif
             .*
        );
    end else begin
        bind el2_veer_lockstep el2_veer_lockstep_cov_if el2_veer_lockstep_cov(
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
            .delayed_main_core_regfile(main_core_regfile.veer_rf_sink),
            .shadow_core_regfile(shadow_core_regfile.veer_rf_sink),
`endif
             .*
        );
    end
`endif

endmodule
