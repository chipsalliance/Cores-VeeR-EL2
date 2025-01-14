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
echo Connecting to OpenOCD...\n
set architecture riscv:rv32
set remotetimeout 360
target extended-remote :3333

echo Dumping registers...\n
info registers

echo Accessing region at 0x20000000...\n
set *(0x20000000) = 0x01234567
set *(0x20000004) = 0x89ABCDEF
set *(0x20000008) = 0x55555555
set *(0x2000000C) = 0xAAAAAAAA
set *(0x25555550) = 0x55555555
set *(0x2aaaaaa0) = 0xAAAAAAAA
print/x *0x20000000@4
print/x *0x25555550
print/x *0x2aaaaaa0

echo Accessing region at 0x30000000...\n
set *(0x30000000) = 0x01234567
set *(0x30000004) = 0x89ABCDEF
set *(0x30000008) = 0x55555555
set *(0x3000000C) = 0xAAAAAAAA
set *(0x35555550) = 0x55555555
set *(0x3aaaaaa0) = 0xAAAAAAAA
print/x *0x30000000@4
print/x *0x35555550
print/x *0x3aaaaaa0

echo Accessing region at 0x40000000...\n
set *(0x40000000) = 0x01234567
set *(0x40000004) = 0x89ABCDEF
set *(0x40000008) = 0x55555555
set *(0x4000000C) = 0xAAAAAAAA
set *(0x45555550) = 0x55555555
set *(0x4aaaaaa0) = 0xAAAAAAAA
print/x *0x40000000@4
print/x *0x45555550
print/x *0x4aaaaaa0

echo Accessing region at 0x50000000...\n
set *(0x50000000) = 0x01234567
set *(0x50000004) = 0x89ABCDEF
set *(0x50000008) = 0x55555555
set *(0x5000000C) = 0xAAAAAAAA
set *(0x55555550) = 0x55555555
set *(0x5aaaaaa0) = 0xAAAAAAAA
print/x *0x50000000@4
print/x *0x55555550
print/x *0x5aaaaaa0

echo Accessing region at 0x60000000...\n
set *(0x60000000) = 0x01234567
set *(0x60000004) = 0x89ABCDEF
set *(0x60000008) = 0x55555555
set *(0x6000000C) = 0xAAAAAAAA
set *(0x65555550) = 0x55555555
set *(0x6aaaaaa0) = 0xAAAAAAAA
print/x *0x60000000@4
print/x *0x65555550
print/x *0x6aaaaaa0

echo Accessing region at 0x70000000...\n
set *(0x70000000) = 0x01234567
set *(0x70000004) = 0x89ABCDEF
set *(0x70000008) = 0x55555555
set *(0x7000000C) = 0xAAAAAAAA
set *(0x75555550) = 0x55555555
set *(0x7aaaaaa0) = 0xAAAAAAAA
print/x *0x70000000@4
print/x *0x75555550
print/x *0x7aaaaaa0

echo Accessing region at 0x80000000...\n
set *(0x80000000) = 0x01234567
set *(0x80000004) = 0x89ABCDEF
set *(0x80000008) = 0x55555555
set *(0x8000000C) = 0xAAAAAAAA
set *(0x85555550) = 0x55555555
set *(0x8aaaaaa0) = 0xAAAAAAAA
print/x *0x80000000@4
print/x *0x85555550
print/x *0x8aaaaaa0

echo Accessing region at 0x90000000...\n
set *(0x90000000) = 0x01234567
set *(0x90000004) = 0x89ABCDEF
set *(0x90000008) = 0x55555555
set *(0x9000000C) = 0xAAAAAAAA
set *(0x95555550) = 0x55555555
set *(0x9aaaaaa0) = 0xAAAAAAAA
print/x *0x90000000@4
print/x *0x95555550
print/x *0x9aaaaaa0

echo Accessing region at 0xa0000000...\n
set *(0xa0000000) = 0x01234567
set *(0xa0000004) = 0x89ABCDEF
set *(0xa0000008) = 0x55555555
set *(0xa000000C) = 0xAAAAAAAA
set *(0xa5555550) = 0x55555555
set *(0xaaaaaaa0) = 0xAAAAAAAA
print/x *0xa0000000@4
print/x *0xa5555550
print/x *0xaaaaaaa0

echo Accessing region at 0xb0000000...\n
set *(0xb0000000) = 0x01234567
set *(0xb0000004) = 0x89ABCDEF
set *(0xb0000008) = 0x55555555
set *(0xb000000C) = 0xAAAAAAAA
set *(0xb5555550) = 0x55555555
set *(0xbaaaaaa0) = 0xAAAAAAAA
print/x *0xb0000000@4
print/x *0xb5555550
print/x *0xbaaaaaa0

echo Accessing region at 0xc0000000...\n
set *(0xc0000000) = 0x01234567
set *(0xc0000004) = 0x89ABCDEF
set *(0xc0000008) = 0x55555555
set *(0xc000000C) = 0xAAAAAAAA
set *(0xc5555550) = 0x55555555
set *(0xcaaaaaa0) = 0xAAAAAAAA
print/x *0xc0000000@4
print/x *0xc5555550
print/x *0xcaaaaaa0

echo Accessing region at 0xd0000000...\n
set *(0xd0000000) = 0x01234567
set *(0xd0000004) = 0x89ABCDEF
set *(0xd0000008) = 0x55555555
set *(0xd000000C) = 0xAAAAAAAA
set *(0xd5555550) = 0x55555555
set *(0xdaaaaaa0) = 0xAAAAAAAA
print/x *0xd0000000@4
print/x *0xd5555550
print/x *0xdaaaaaa0

echo Setting Breakpoint 1...\n
hbreak *0x1c

echo Continuing...\n
continue

delete

# end the simulation gracefully
set *(volatile unsigned char*)0xd0580000 = 0xff
