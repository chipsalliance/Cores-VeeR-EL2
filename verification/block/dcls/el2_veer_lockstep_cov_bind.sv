module el2_veer_lockstep_cov_bind ();
     `ifdef FCOV
     bind el2_veer_lockstep_cov_if(.*);
     `endif
endmodule