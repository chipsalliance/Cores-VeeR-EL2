# Post-simulation power analysis for the mapped synthesis netlist.
# Required environment: LIBERTY, TECH_LEF, CELL_LEF, NETLIST, SAIF, CLK_PERIOD_NS.

read_lef $::env(TECH_LEF)
read_lef $::env(CELL_LEF)
read_liberty $::env(LIBERTY)
read_verilog $::env(NETLIST)
link_design el2_veer_wrapper

# The clock period must match the simulation that generated the SAIF.
create_clock -name core_clock -period $::env(CLK_PERIOD_NS) [get_ports clk]

# trace2power's SAIF is rooted at rvtop_synth_wrapper, with the synthesized
# design instance nested below it as rvtop_synth.
read_saif -scope rvtop_synth_wrapper/rvtop_synth $::env(SAIF)

if {[info exists ::env(POWER_REPORT)]} {
    report_power > $::env(POWER_REPORT)
} else {
    report_power
}
