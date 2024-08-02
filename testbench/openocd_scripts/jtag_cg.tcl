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
init

set script_dir [file dirname [info script]]
source [file join $script_dir common.tcl]

puts "Read Debug Module Status Register..."
set val [riscv dmi_read $dmstatus_addr]
puts "dmstatus: $val"
if {($val & 0x00000c00) == 0} {
    echo "The hart is halted!"
    shutdown error
}
puts ""

riscv set_mem_access sysbus

set addr1 0xFFFF0000
set addr2 0x0000FFF0
set addr3 0x0000FFFF
set data1 0x05050505
set data2 0xFAFAFAFA
set data3 0xAB

puts "Write few bytes"
write_memory $addr1 32 $data1 phys

puts "Write few different bytes at the same address"
write_memory $addr1 32 $data2 phys

puts "Read few bytes"
set actual [read_memory $addr1 32 1 phys]
if {[compare $actual $data2] != 0} {
    shutdown error
}

puts "Read few bytes one more time"
set actual [read_memory $addr1 32 1 phys]
if {[compare $actual $data2] != 0} {
    shutdown error
}

puts "Write few bytes to different address"
write_memory $addr2 32 $data1 phys

puts "Read few bytes from that address"
set actual [read_memory $addr2 32 1 phys]
if {[compare $actual $data1] != 0} {
    shutdown error
}

puts "Write 1 byte"
write_memory $addr3 8 $data3 phys

puts "Read 1 byte"
set actual [read_memory $addr3 8 1 phys]
if {[compare $actual $data3] != 0} {
    shutdown error
}

# Send signal to call $finish
write_memory 0xd0580000 8 0xFF phys

shutdown
