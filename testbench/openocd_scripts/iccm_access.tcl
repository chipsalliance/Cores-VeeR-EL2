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
# 32-bit ICCM write + read-back using abstract memory access.
#
# Abstract memory accesses reach ICCM through the DMA with the size requested by
# the debugger, so each word below is written and read back with a 32-bit DMA
# access. The test fails if an access errors or the read data differs.

# ICCM base address for "default" VeeR configuration
set iccm_begin 0xEE000000

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

# Abstract memory access requires the core to be halted
puts "Halting the core"
halt

riscv set_mem_access abstract

# Even and odd words are held in different ICCM banks
set words {
    {0x0 0xCAFEBACA}
    {0x4 0xDEADBEEF}
    {0x8 0x12345678}
    {0xC 0xA5A5A5A5}
}

foreach word $words {
    set addr [expr {$iccm_begin + [lindex $word 0]}]
    set data [lindex $word 1]
    puts [format "32-bit access to 0x%08X" $addr]

    if {[catch { write_memory $addr 32 $data phys }]} {
        puts "write failed!"
        finish 0x01
    }
    if {[catch { set readback [read_memory $addr 32 1 phys] }]} {
        puts "read failed!"
        finish 0x01
    }
    if {[compare $readback $data] != 0} {
        finish 0x01
    }
}

finish 0xFF
