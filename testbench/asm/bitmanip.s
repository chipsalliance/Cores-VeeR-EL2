// SPDX-License-Identifier: Apache-2.0
// Copyright 2024 Antmicro <www.antmicro.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#define STDOUT 0xd0580000
#define RESULT_SUCCESS 0xff
#define RESULT_FAILURE 0x1

// 5-bit encodings of registers
#define reg_map(x) reg_map__##x
#define reg_map__t0 5
#define reg_map__t1 6
#define reg_map__t2 7

// Implement instructions not implemented in the toolchain (Bitmanip Extenstion 0.94-draft, Jan 20, 2021)
#define bcompress(rd, rs1, rs2) .word (0b0000100 << 25| (reg_map(rs2)) << 20 | (reg_map(rs1)) << 15 | 0b110 << 12 | (reg_map(rd)) << 7 | 0b0110011)
#define bdecompress(rd, rs1, rs2) .word (0b0100100 << 25| (reg_map(rs2)) << 20 | (reg_map(rs1)) << 15 | 0b110 << 12 | (reg_map(rd)) << 7 | 0b0110011)
#define grev(rd, rs1, rs2) .word (0b0110100 << 25| (reg_map(rs2)) << 20 | (reg_map(rs1)) << 15 | 0b101 << 12 | (reg_map(rd)) << 7 | 0b0110011)
#define gorc(rd, rs1, rs2) .word (0b0010100 << 25| (reg_map(rs2)) << 20 | (reg_map(rs1)) << 15 | 0b101 << 12 | (reg_map(rd)) << 7 | 0b0110011)

#define EQUAL_OR_FAIL(reg, value) \
    li t3, value; \
    bne reg, t3, test_failed

.global _start
_start:
    li t0, 0xc0de    // arg1
    li t1, 0xdec0de  // arg2
    li t2, 0         // result

test_bcompress:
    bcompress(t2, t0, t1)
    EQUAL_OR_FAIL(t2, 0xff)

test_bdcompress:
    bdecompress(t2, t0, t1)
    EQUAL_OR_FAIL(t2, 0xc05c)

test_grev:
    grev(t2, t0, t1)
    EQUAL_OR_FAIL(t2, 0xb7030000)

test_gorc:
    gorc(t2, t0, t1)
    EQUAL_OR_FAIL(t2, 0xffffffff)

success:
    li a0, STDOUT
    li a1, RESULT_SUCCESS
    sw a1, 0(a0)

do_nothing:
    nop
    j do_nothing

test_failed:
    li a0, STDOUT
    li a1, RESULT_FAILURE
    sw a1, 0(a0)
.long   0
