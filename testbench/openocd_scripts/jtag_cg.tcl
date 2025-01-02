# SPDX-License-Identifier: Apache-2.0
# Copyright 2024 Antmicro <www.antmicro.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

proc dmi_dump {} {
    # Dumps all DMI registers defined by the spec

    # DMI regs per "RISC-V External Debug Support Version 0.13.2"
    set dmi_regs {
        {0x04 "data0"}
        {0x0f "data1"}
        {0x10 "dmcontrol"}
        {0x11 "dmstatus"}
        {0x12 "hartinfo"}
        {0x13 "haltsum1"}
        {0x14 "hawindowsel"}
        {0x15 "hawindow"}
        {0x16 "abstractcs"}
        {0x17 "command"}
        {0x18 "abstractauto"}
        {0x19 "configstrptr0"}
        {0x1a "configstrptr1"}
        {0x1b "configstrptr2"}
        {0x1c "configstrptr3"}
        {0x1d "nextdm"}
        {0x20 "progbuf0"}
        {0x2f "progbuf15"}
        {0x30 "authdata"}
        {0x34 "haltsum2"}
        {0x35 "haltsum3"}
        {0x37 "sbaddress3"}
        {0x38 "sbcs"}
        {0x39 "sbaddress0"}
        {0x3a "sbaddress1"}
        {0x3b "sbaddress2"}
        {0x3c "sbdata0"}
        {0x3d "sbdata1"}
        {0x3e "sbdata2"}
        {0x3f "sbdata3"}
        {0x40 "haltsum"}
    }

    puts "Dumping DMI registers"
    foreach it $dmi_regs {
        set addr [lindex $it 0]
        set name [lindex $it 1]
        set val [riscv dmi_read $addr]

        puts " $addr $name $val"
    }
}

proc test_single_access { addr size data1 data2 } {
    # Tests memory access to a single address. Writes data1, then overwrites
    # it with data2, performs readback and compares the read value.

    set astr [format %08X $addr]
    puts "  $size-bit access to 0x$astr"

    # Write 1
    if {[catch { write_memory $addr $size $data1 phys }]} {
        return -1
    }
    # Write 2
    if {[catch { write_memory $addr $size $data2 phys }]} {
        return -1
    }

    # Read
    if {[catch { set readback [read_memory $addr $size 1 phys] }]} {
        return -1
    }
    # Compare
    if {[compare $readback $data2] != 0} {
        return -1
    }

    return 0
}

proc test_memory_access { access_mode base_address widths uwidths } {
    # Test various types of memory access to the given address
    # "widths" is a list of aligned access sizes to execute and "uwidths"
    # is a list of unaligned accesses to perform.

    puts "Testing memory access at $base_address using $access_mode mode"
    riscv set_mem_access $access_mode

    set addr0 $base_address
    set addr1 [ expr {$base_address + 1} ]
    set addr2 [ expr {$base_address + 2} ]
    set addr3 [ expr {$base_address + 3} ]

    set data32_1 0xCAFEBACA
    set data32_2 0xDEADBEEF

    set data16_1 0xFACE
    set data16_2 0x5A5A

    set data8_1  0x55
    set data8_2  0xAA

    # Aligned accesses
    puts " testing aligned access"

    if {[lsearch -exact $widths 32] >= 0} {
        test_single_access $addr0 32 $data32_1 $data32_2
    }

    if {[lsearch -exact $widths 16] >= 0} {
        test_single_access $addr0 16 $data16_1 $data16_2
        test_single_access $addr2 16 $data16_2 $data16_1
    }

    if {[lsearch -exact $widths 8] >= 0} {
        test_single_access $addr0 8  $data8_1 $data8_2
        test_single_access $addr1 8  $data8_2 $data8_1
        test_single_access $addr2 8  $data8_1 $data8_2
        test_single_access $addr3 8  $data8_2 $data8_1
    }

    # Unaligned accesses
    puts " testing unaligned access"

    if {[lsearch -exact $uwidths 32] >= 0} {
        test_single_access $addr1 32 $data32_2 $data32_1
        test_single_access $addr2 32 $data32_1 $data32_2
        test_single_access $addr3 32 $data32_2 $data32_1
    }

    if {[lsearch -exact $uwidths 16] >= 0} {
        test_single_access $addr1 16 $data16_2 $data16_1
        test_single_access $addr3 16 $data16_2 $data16_1
    }
}

# Memory region base addesses for "default" VeeR configuration
set ram_begin  0x00000000
set dccm_begin 0xF0040000
set iccm_begin 0xEE000000
set pic_begin  0xF00C0000

init

set script_dir [file dirname [info script]]
source [file join $script_dir common.tcl]

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts " dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

# Dump all DMI registers
dmi_dump

# Access abstractauto (0x18) DMI register
puts "Exercising abstractauto (0x18) DMI register"
for {set i 0} {$i < 10} {incr i} {
    riscv dmi_write 0x18 [expr {int(rand()*0xFFFFFFFF)}]
    riscv dmi_read  0x18
    riscv dmi_write 0x18 0
}

# Access sbdata1 (0x3D)
for {set i 0} {$i < 10} {incr i} {
    riscv dmi_write 0x3D [expr {int(rand()*0xFFFFFFFF)}]
    riscv dmi_read  0x3D
    riscv dmi_write 0x3D 0
}

# Test access in sysbus mode
for {set i 0} {$i < 5} {incr i} {
    test_memory_access "sysbus" $dccm_begin {32 16 8} {32 16}
    test_memory_access "sysbus" $ram_begin  {32 16 8} {32 16}
    test_memory_access "sysbus" $iccm_begin {32} {32 16}
    test_memory_access "sysbus" $pic_begin  {32 16 8} {32 16}
}

# Halt the core
puts "Halting the core"
halt
set val [riscv dmi_read $dmstatus_addr]
puts " dmstatus: $val"

# Manually attempt 64-bit sysbus transaction to trigger internal illegal size
# error in the debug core
puts "Attempting 64-bit memory access in abstract mode"
for {set i 0} {$i < 5} {incr i} {
    riscv dmi_write 0x38 0x000E0000
    riscv dmi_write 0x39 $ram_begin
    riscv dmi_write 0x3C [expr {int(rand()*0xFFFFFFFF)}]
    # Clear errors
    riscv dmi_write 0x38 0x00407000
}

puts "Testing automatic bus read (sbreadonaddr=1)"
for {set i 0} {$i < 5} {incr i} {
    riscv dmi_write 0x38 0x00140000
    for {set j 0} {$j < 5} {incr j} {
        riscv dmi_write 0x39 [expr {$ram_begin + 4 * $j}]
        set val [riscv dmi_read 0x3C]
        puts " sbdata0: $val"
    }
}

puts "Testing automatic bus read and address increment (sbreadondata=1, sbautoincrement=1)"
for {set i 0} {$i < 5} {incr i} {
    riscv dmi_write 0x38 0x00058000
    riscv dmi_write 0x39 $ram_begin
    for {set j 0} {$j < 5} {incr j} {
        set val [riscv dmi_read 0x3C]
        puts " sbdata0: $val"
    }
}

# Test access in abstract mode
for {set i 0} {$i < 5} {incr i} {
    test_memory_access "abstract" $dccm_begin {32 16 8} {32 16}
    test_memory_access "abstract" $ram_begin  {32 16 8} {32 16}
    test_memory_access "abstract" $iccm_begin {32} {32 16}
    # No abstract access to PIC
    #test_memory_access "abstract" $pic_begin  {32} {}
}

# Send signal to call $finish
riscv set_mem_access sysbus
write_memory 0xd0580000 8 0xFF phys

shutdown
