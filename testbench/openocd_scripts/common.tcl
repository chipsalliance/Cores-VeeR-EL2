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
proc compare {x y} {
    puts "'$x' vs. '$y'"

    if {[llength $y] != [llength $y]} {
        puts "length mismatch!"
        return -1
    }

    for {set i 0} {$i < [llength $x]} {incr i} {
        if {[lindex $x $i] != [lindex $y $i]} {
            puts "item $i mismatch!"
            return -1
        }
    }

    return 0
}

set STDOUT 0x300300cc
set dmstatus_addr 0x11

