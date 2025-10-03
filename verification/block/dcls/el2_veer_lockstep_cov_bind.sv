module el2_veer_lockstep_cov_bind
#(
    `include "el2_param.vh"
) ();
`ifdef FCOV
    bind el2_veer_lockstep el2_veer_lockstep_cov_if el2_veer_lockstep_cov(
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
        .delayed_main_core_regfile(delayed_main_core_regfile[pt.LOCKSTEP_DELAY].veer_rf_sink),
        .shadow_core_regfile(shadow_core_regfile.veer_rf_sink),
`endif
         .*
    );
`endif

endmodule
