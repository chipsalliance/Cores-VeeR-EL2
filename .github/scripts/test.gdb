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
echo Accessing DCCM...\n
set *(0x00080000) = 0x01234567
set *(0x00080004) = 0x89ABCDEF
set *(0x00080008) = 0x55555555
set *(0x0008000C) = 0xAAAAAAAA
print/x *0x00080000@4

# TODO why does the default configuration for iccm (0xe000000) differ from the documentation (0x40000)?
echo Accessing ICCM...\n
set *(0x0e000000) = 0x01234567
set *(0x0e000004) = 0x89ABCDEF
set *(0x0e000008) = 0x55555555
set *(0x0e00000C) = 0xAAAAAAAA
print/x *0x00e00000@4

echo Accessing region at 0x20000000...\n
set *(0x20000000) = 0x01234567
set *(0x20000004) = 0x89ABCDEF
set *(0x20000008) = 0x55555555
set *(0x2000000C) = 0xAAAAAAAA
print/x *0x20000000@4

echo Accessing region at 0x30000000...\n
set *(0x30000000) = 0x01234567
set *(0x30000004) = 0x89ABCDEF
set *(0x30000008) = 0x55555555
set *(0x3000000C) = 0xAAAAAAAA
print/x *0x30000000@4

echo Accessing region at 0x40000000...\n
set *(0x40000000) = 0x01234567
set *(0x40000004) = 0x89ABCDEF
set *(0x40000008) = 0x55555555
set *(0x4000000C) = 0xAAAAAAAA
print/x *0x40000000@4

echo Accessing region at 0x50000000...\n
set *(0x50000000) = 0x01234567
set *(0x50000004) = 0x89ABCDEF
set *(0x50000008) = 0x55555555
set *(0x5000000C) = 0xAAAAAAAA
print/x *0x50000000@4

echo Accessing region at 0x60000000...\n
set *(0x60000000) = 0x01234567
set *(0x60000004) = 0x89ABCDEF
set *(0x60000008) = 0x55555555
set *(0x6000000C) = 0xAAAAAAAA
print/x *0x60000000@4

echo Accessing region at 0x70000000...\n
set *(0x70000000) = 0x01234567
set *(0x70000004) = 0x89ABCDEF
set *(0x70000008) = 0x55555555
set *(0x7000000C) = 0xAAAAAAAA
print/x *0x70000000@4

echo Accessing region at 0x80000000...\n
set *(0x80000000) = 0x01234567
set *(0x80000004) = 0x89ABCDEF
set *(0x80000008) = 0x55555555
set *(0x8000000C) = 0xAAAAAAAA
print/x *0x80000000@4

echo Accessing region at 0x90000000...\n
set *(0x90000000) = 0x01234567
set *(0x90000004) = 0x89ABCDEF
set *(0x90000008) = 0x55555555
set *(0x9000000C) = 0xAAAAAAAA
print/x *0x90000000@4

echo Accessing region at 0xa0000000...\n
set *(0xa0000000) = 0x01234567
set *(0xa0000004) = 0x89ABCDEF
set *(0xa0000008) = 0x55555555
set *(0xa000000C) = 0xAAAAAAAA
print/x *0xa0000000@4

echo Accessing region at 0xb0000000...\n
set *(0xb0000000) = 0x01234567
set *(0xb0000004) = 0x89ABCDEF
set *(0xb0000008) = 0x55555555
set *(0xb000000C) = 0xAAAAAAAA
print/x *0xb0000000@4

echo Accessing region at 0xc0000000...\n
set *(0xc0000000) = 0x01234567
set *(0xc0000004) = 0x89ABCDEF
set *(0xc0000008) = 0x55555555
set *(0xc000000C) = 0xAAAAAAAA
print/x *0xc0000000@4

echo Accessing region at 0xd0000000...\n
set *(0xd0000000) = 0x01234567
set *(0xd0000004) = 0x89ABCDEF
set *(0xd0000008) = 0x55555555
set *(0xd000000C) = 0xAAAAAAAA
print/x *0xd0000000@4

echo Setting Breakpoint 1...\n
hbreak *0x1c

echo Continuing...\n
continue

delete

# end the simulation gracefully
set *(volatile unsigned char*)0xd0580000 = 0xff
