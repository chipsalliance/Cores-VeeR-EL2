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

# Invoke GDB
${GCC_PREFIX}-gdb -n --batch -x peripheral_access.gdb >gdb.log
# Parse the log
cat gdb.log | grep -E '^\$[0-9]+' >peripheral_access.txt

# Compare the dumps
diff -E -y peripheral_access_golden.txt peripheral_access.txt || true

