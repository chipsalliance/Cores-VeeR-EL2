# Global variables, user configurable
set clk_frequency_mhz 1000
set jtag_frequency_mhz 50
set io_delay_reg_percent 0.6
set io_delay_comb_percent 0.3
set io_delay_clken_percent 0.5
# Set to 1 for AXI interfaces, 0 for AHB interfaces
set axi_core_if 1

# Clock definition
set clk_period_ps [expr 1000000/${clk_frequency_mhz}]
set clk_name clk
set clk_port_name clk
create_clock -name $clk_name -period $clk_period_ps -waveform [list 0 [expr $clk_period_ps/2]] [get_ports $clk_port_name]
create_clock -name v_$clk_name -period $clk_period_ps -waveform [list 0 [expr $clk_period_ps/2]]
set jtag_period_ns [expr 1000/${jtag_frequency_mhz}]
set jtag_clk_name jtag_clk
set jtag_clk_port_name jtag_tck
create_clock -name $jtag_clk_name -period $jtag_period_ns -waveform [list 0 [expr $jtag_period_ns/2]] [get_ports $jtag_clk_port_name]
create_clock -name v_$jtag_clk_name -period $jtag_period_ns -waveform [list 0 [expr $jtag_period_ns/2]]

set_clock_groups -async \
-group [list $clk_name v_$clk_name] \
-group [list $jtag_clk_name v_$jtag_clk_name]

# IO delay
set io_min_delay_ns [expr 0.01*$clk_period_ps]

# Main bus interfaces
if { $axi_core_if == 1} {
    puts "CORE has AXI interfaces"
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} lsu_axi_*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} lsu_axi_*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} lsu_axi_*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} lsu_axi_*]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} ifu_axi_*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} ifu_axi_*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} ifu_axi_*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} ifu_axi_*]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} sb_axi_*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} sb_axi_*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} sb_axi_*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} sb_axi_*]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} dma_axi_*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} dma_axi_*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} dma_axi_*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} dma_axi_*]

} else {
    puts "CORE has AHB interfaces"
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hrdata]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hrdata]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hready]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hready]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hresp]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hresp]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports haddr]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports haddr]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hburst]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hburst]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hmastlock]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hmastlock]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hprot]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hprot]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hsize]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hsize]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports htrans]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports htrans]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports hwrite]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports hwrite]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} lsu_h*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} lsu_h*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} lsu_h*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} lsu_h*]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} sb_h*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} sb_h*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} sb_h*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} sb_h*]
    set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} dma_h*]
    set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} dma_h*]
    set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} dma_h*]
    set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} dma_h*]
}
# Clock gate enable signals
set_input_delay -clock v_$clk_name -max [expr $io_delay_clken_percent*$clk_period_ps] [get_ports -filter {direction==input} *_bus_clk_en]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} *_bus_clk_en]
# ECC error signals
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} *ccm*_error]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} *ccm*_error]
# Interrupts
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports nmi_int]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports nmi_int]
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports timer_int]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports timer_int]
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports soft_int]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports soft_int]
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports extintsrc_req]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports extintsrc_req]
# Performance counters
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} dec_tlu_perfcnt*]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} dec_tlu_perfcnt*]
# JTAG interface
set_input_delay -clock v_$jtag_clk_name -max [expr $io_delay_reg_percent*$jtag_period_ns] [get_ports jtag_tms]
set_input_delay -clock v_$jtag_clk_name -min $io_min_delay_ns [get_ports jtag_tms]
set_input_delay -clock v_$jtag_clk_name -max [expr $io_delay_reg_percent*$jtag_period_ns] [get_ports jtag_tdi]
set_input_delay -clock v_$jtag_clk_name -min $io_min_delay_ns [get_ports jtag_tdi]
set_output_delay -clock v_$jtag_clk_name -max [expr $io_delay_reg_percent*$jtag_period_ns] [get_ports jtag_tdo]
set_output_delay -clock v_$jtag_clk_name -min $io_min_delay_ns [get_ports jtag_tdo]
set_output_delay -clock v_$jtag_clk_name -max [expr $io_delay_reg_percent*$jtag_period_ns] [get_ports jtag_tdoEn]
set_output_delay -clock v_$jtag_clk_name -min $io_min_delay_ns [get_ports jtag_tdoEn]
# MPC interface
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} mpc_*]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} mpc_*]
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} mpc_*]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} mpc_*]
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports debug_brkpt_status]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} debug_brkpt_status]
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} i_cpu_*]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} i_cpu_*]
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} i_cpu_*]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} i_cpu_*]
# DMI interface
set_input_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==input} dmi_*]
set_input_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==input} dmi_*]
set_output_delay -clock v_$clk_name -max [expr $io_delay_reg_percent*$clk_period_ps] [get_ports -filter {direction==output} dmi_*]
set_output_delay -clock v_$clk_name -min $io_min_delay_ns [get_ports -filter {direction==output} dmi_*]

# TODO: EL2 icache_export?
# TODO el2_mem_export

# Timing exceptions
## Tied signals
set_case_analysis 0 scan_mode
set_case_analysis 0 mbist_mode

## Ports that should be tied to constant, relax timing so they are not completely ignored
set_multicycle_path -setup 2 -from [get_ports rst_vec]
set_multicycle_path -hold 1 -from [get_ports rst_vec]
set_multicycle_path -setup 2 -from [get_ports nmi_vec]
set_multicycle_path -hold 1 -from [get_ports nmi_vec]
set_multicycle_path -setup 2 -from [get_ports jtag_id]
set_multicycle_path -hold 1 -from [get_ports jtag_id]
set_multicycle_path -setup 2 -from [get_ports core_id]
set_multicycle_path -hold 1 -from [get_ports core_id]

