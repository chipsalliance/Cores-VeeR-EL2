set sdc_version 2.0

current_design swerv_wrapper

set clk_name core_clock
set clk_port_name clk
set clk_period 1300

# Match the old set_input/output_delay = 0.2 * clk_period budget, as
# optimization targets only (no set_input/output_delay — see rationale below)
set in2reg_max [expr { $clk_period * 0.6 }]
set reg2out_max [expr { $clk_period * 0.8 }]
set in2out_max [expr { $clk_period * 0.8 }]

set clk_port [get_ports $clk_port_name]
create_clock -period $clk_period -waveform [list 0 [expr $clk_period / 2]] -name $clk_name $clk_port

set non_clk_inputs [all_inputs -no_clocks]

# Optimization targets: overconstrain by default and
# leave refinements to a more design specific constraints.sdc file.
#
# Minimum time, excluding clock latency, for io-io, io-reg, reg-io
# paths in macro is on the order of 80ps for a small macro on ASAP7.
set_max_delay -ignore_clock_latency \
  [expr { [info exists in2reg_max] ? $in2reg_max : 80 }] -from $non_clk_inputs \
  -to [all_registers]
set_max_delay -ignore_clock_latency \
  [expr { [info exists reg2out_max] ? $reg2out_max : 80 }] -from [all_registers] \
  -to [all_outputs]
set_max_delay [expr { [info exists in2out_max] ? $in2out_max : 80 }] -from $non_clk_inputs \
  -to [all_outputs]

# This allows us to view the different groups
# in the histogram in the GUI and also includes these
# groups in the report
group_path -name in2reg -from $non_clk_inputs -to [all_registers]
group_path -name reg2out -from [all_registers] -to [all_outputs]
group_path -name reg2reg -from [all_registers] -to [all_registers]
group_path -name in2out -from $non_clk_inputs -to [all_outputs]
