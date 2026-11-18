proc die_shot {write_path} {
    gui::show {
        gui::set_display_controls * visible false
        gui::set_display_controls Layers/* visible true
        gui::set_display_controls Nets/* visible true
        gui::set_display_controls "Shape Types/*" visible true
        gui::set_display_controls Instances/* visible true
        select -type Inst -highlight 0 -filter "Description=Sequential cell"
        select -type Inst -highlight 0 -filter "Description=Multi-Input combinational cell"
        select -type Inst -highlight 0 -filter "Description=Timing Repair Buffer"
        select -type Inst -highlight 0 -filter "Description=Inverter"
        select -type Inst -highlight 0 -filter "Description=Clock buffer"
        select -type Inst -highlight 0 -filter "Description=Clock inverter"
        gui::fit
        save_image -width 7200 $write_path
    } false
}
