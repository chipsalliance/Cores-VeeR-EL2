#!/bin/bash
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
set -ex

# Invoke GDB and dump core registers
${GCC_PREFIX}-gdb -n --batch -x dump_registers.gdb >gdb.log
# Parse the log, extract register values. Skip those which change as the
# program executes since we don't know at which point we tap in.
cat gdb.log | grep -E '^ra |^sp |^gp |^tp |^t[01256] |^s[0-9]+ |^a[0-9]+ |^\$[0-9]+' >regdump.txt

# Compare the dumps
diff -E -y regdump_golden.txt regdump.txt

