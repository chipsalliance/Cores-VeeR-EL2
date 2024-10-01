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
set remotetimeout 30
target extended-remote :3333

echo Connected, waiting...\n
shell sleep 5s

echo Accessing ECC...\n
print/x *0x10008000@2
print/x *0x10008008@2

echo Accessing HMAC...\n
print/x *0x10010000@2
print/x *0x10010008@2

echo Accessing SHA512...\n
print/x *0x10020000@2
print/x *0x10020008@2

echo Accessing SHA256...\n
print/x *0x10028000@2
print/x *0x10028008@2

echo Writing and reading DOE IV...\n
set *(0x10000000) = 0xCAFEBABA
set *(0x10000004) = 0xDEADBEEF
set *(0x10000008) = 0xD0ED0E00
print/x *0x10000000@3

