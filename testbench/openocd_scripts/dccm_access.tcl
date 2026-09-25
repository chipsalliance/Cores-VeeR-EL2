# SPDX-License-Identifier: Apache-2.0
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
# DCCM write + read-back using abstract memory access.
#
# Abstract memory accesses reach DCCM through the DMA with the size requested by
# the debugger. DMA writes to DCCM must be word-sized, so each word below is
# written with a 32-bit access and read back with 32-, 16- and 8-bit accesses.
# The test fails if an access errors or the read data differs.

# DCCM base address for "default" VeeR configuration
set dccm_begin 0xF0040000

init

set script_dir [file dirname [info script]]
source [file join $script_dir common.tcl]

proc finish { code } {
    # Send signal to call $finish, then exit with the test result
    riscv set_mem_access sysbus
    write_memory 0xd0580000 8 $code phys
    if {$code != 0xFF} {
        shutdown error
    }
    shutdown
}

proc check_read { addr size expected } {
    puts [format "%d-bit read of 0x%08X" $size $addr]
    if {[catch { set readback [read_memory $addr $size 1 phys] }]} {
        puts "read failed!"
        finish 0x01
    }
    if {[compare $readback $expected] != 0} {
        finish 0x01
    }
}

# Abstract memory access requires the core to be halted
puts "Halting the core"
halt

riscv set_mem_access abstract

# One word per DCCM bank
set words {
    {0x0 0xCAFEBACA}
    {0x4 0xDEADBEEF}
    {0x8 0x12345678}
    {0xC 0xA5A5A5A5}
}

foreach word $words {
    set addr [expr {$dccm_begin + [lindex $word 0]}]
    set data [lindex $word 1]
    puts [format "32-bit write of 0x%08X" $addr]

    if {[catch { write_memory $addr 32 $data phys }]} {
        puts "write failed!"
        finish 0x01
    }

    check_read $addr 32 $data
    for {set i 0} {$i < 4} {incr i 2} {
        check_read [expr {$addr + $i}] 16 [expr {($data >> (8 * $i)) & 0xFFFF}]
    }
    for {set i 0} {$i < 4} {incr i} {
        check_read [expr {$addr + $i}] 8 [expr {($data >> (8 * $i)) & 0xFF}]
    }
}

finish 0xFF
