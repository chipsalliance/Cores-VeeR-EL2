module el2_veer_lockstep_cov_bind ();
     `ifdef FCOV
     bind el2_veer_lockstep el2_veer_lockstep_cov_if el2_veer_lockstep_cov(.*);
     `endif
endmodule
