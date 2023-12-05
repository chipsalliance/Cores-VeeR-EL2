.include "user_define.h"
.globl _start
.section .text
_start:           
                  .include "user_init.s"
                  csrr x5, 0xf14
                  li x6, 0
                  beq x5, x6, 0f

0: la x31, h0_start
jalr x0, x31, 0
h0_start:
                  li x6, 0x40001104
                  csrw 0x301, x6
kernel_sp:        
                  la x30, kernel_stack_end

trap_vec_init:    
                  la x6, mtvec_handler
                  ori x6, x6, 1
                  csrw 0x305, x6 # MTVEC

mepc_setup:       
                  la x6, init
                  csrw 0x341, x6

init_machine_mode:
                  li x6, 0x1800
                  csrw 0x300, x6 # MSTATUS
                  li x6, 0x0
                  csrw 0x304, x6 # MIE
                  mret
init:             
                  li x0, 0x80000000
                  li x1, 0xfb436cd9
                  li x2, 0xf73e2014
                  li x3, 0xfa05c495
                  li x4, 0x80000000
                  li x5, 0x80000000
                  li x6, 0xf7a95956
                  li x7, 0x0
                  li x8, 0x3
                  li x9, 0x9
                  li x11, 0xe
                  li x12, 0x0
                  li x13, 0x80000000
                  li x14, 0x9a8c3e6d
                  li x15, 0xf
                  li x16, 0x0
                  li x17, 0x0
                  li x18, 0xd
                  li x19, 0x6f633778
                  li x20, 0xf43b952c
                  li x21, 0x9e7198bf
                  li x22, 0x2
                  li x23, 0x0
                  li x24, 0xa
                  li x25, 0x0
                  li x26, 0x2
                  li x27, 0x0
                  li x28, 0x0
                  li x29, 0x80000000
                  li x31, 0xa
                  la x10, user_stack_end
main:             li         t0, 0x52d893a0 #start riscv_int_numeric_corner_stream_5
                  li         t3, 0x83c22e1
                  li         s6, 0x1
                  li         s11, 0x20f26623
                  li         s10, 0x0
                  li         t4, 0x0
                  li         s8, 0x0
                  li         s3, 0x1
                  li         s2, 0x56dfb7da
                  li         t1, 0x1
                  addi        s7, a2, -140
                  add         t3, s9, s7
                  add         a6, ra, s1
                  sub         t1, sp, a3
                  add         zero, a4, s11
                  sub         sp, t0, t1
                  c.mv        s3, t6
                  c.nop
                  c.addi16sp  sp, -16
                  nop
                  c.lui       s0, 5
                  c.addi      a2, 9
                  mul         s4, s2, a3
                  add         s6, tp, sp
                  c.addi4spn  a2, sp, 128
                  c.addi4spn  a1, sp, 192
                  rem         a5, s1, t0
                  c.addi      s4, -1
                  mul         sp, a0, ra
                  add         sp, sp, s3 #end riscv_int_numeric_corner_stream_5
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_6
                  li         t3, 0x54fd690d
                  li         t1, 0x1
                  li         s11, 0x0
                  li         a3, 0x63471a69
                  li         s10, 0x1cd36d3d
                  li         a1, 0x0
                  li         s9, 0x1c0a687
                  li         s8, 0x0
                  li         gp, 0x1
                  sub         a3, t0, s9
                  c.addi16sp  sp, 432
                  c.addi      sp, 2
                  rem         zero, s10, a3
                  rem         tp, a3, s5
                  c.addi      s3, 24
                  mulh        a4, t6, sp
                  mulh        s6, s7, sp
                  mulh        t1, s1, gp
                  c.addi      a5, -1
                  c.addi4spn  s1, sp, 896
                  mulh        s5, t6, t3
                  c.sub       a2, s1
                  auipc       s11, 817633
                  auipc       a4, 661274
                  add         a2, sp, tp
                  c.nop
                  c.lui       t0, 19
                  addi        s6, a1, 1708
                  divu        sp, a6, ra
                  c.sub       a2, a3
                  add         s3, s11, s1
                  lui         a6, 987739
                  c.addi      ra, -1
                  mulhsu      s8, s4, s8
                  c.sub       a3, s1
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_3
                  li         t3, 0x0
                  li         s11, 0x1
                  li         s9, 0x1
                  li         s7, 0x1
                  li         s2, 0x0
                  li         a1, 0x0
                  li         s3, 0x71e722ba
                  li         s10, 0x1
                  li         a7, 0x0
                  add         a2, s2, zero
                  c.add       a5, s8
                  sub         s10, t1, s0
                  nop
                  mulh        a6, s5, a1
                  auipc       a2, 404318
                  c.addi16sp  sp, -16
                  auipc       zero, 866547
                  c.nop
                  divu        tp, t5, a7
                  c.sub       a3, s0
                  divu        a2, t4, t2
                  c.sub       a3, s1
                  divu        a4, t0, a5
                  mulhu       s0, a2, zero
                  rem         s4, s10, s8
                  mulh        a7, zero, a7
                  div         s3, t3, t6
                  c.li        s1, -1
                  c.addi16sp  sp, -16
                  c.li        t2, 4
                  mulhsu      a7, s5, s8
                  mul         t2, a1, s7
                  addi        s10, a1, 307
                  lui         t2, 344368
                  lui         t2, 153214
                  mulhu       gp, s7, s1 #end riscv_int_numeric_corner_stream_3
                  li         s8, 0x0 #start riscv_int_numeric_corner_stream_4
                  li         a6, 0x0
                  li         s10, 0x761ffaf8
                  li         t4, 0x0
                  li         t3, 0x0
                  li         s11, 0x0
                  li         a2, 0x1bea1a9a
                  li         a3, 0x0
                  li         s6, 0x0
                  li         s9, 0x7af24240
                  div         t3, t2, s4
                  nop
                  div         s3, zero, s6
                  mulh        gp, s11, a4
                  rem         a6, s3, s7
                  c.li        ra, -1
                  c.li        s8, -1
                  c.lui       s1, 12
                  divu        s3, t6, s11
                  c.mv        t0, t1
                  add         s1, t2, s7
                  c.mv        s7, t6
                  mulhsu      s3, sp, a3
                  addi        a5, s8, -918
                  c.sub       a2, s1
                  rem         zero, tp, a0
                  rem         a2, s4, gp
                  lui         s5, 391654
                  lui         s11, 692644
                  auipc       s3, 632424
                  mul         zero, sp, s7
                  c.addi4spn  a2, sp, 16
                  c.addi      s8, -1
                  c.mv        ra, a4
                  mul         a7, tp, a6
                  mul         t3, zero, s0
                  c.li        a7, -1
                  c.sub       a3, a2
                  c.xor       a3, a1
                  mulh        zero, t2, t4
                  auipc       t1, 171993
                  divu        s11, t5, s4
                  c.addi4spn  s0, sp, 576
                  sra         s2, s4, t0
                  sll         a3, s9, s11
                  andi        t3, zero, -1982
                  sub         s4, a1, s10
                  slti        tp, s1, -35
                  sll         s9, ra, s0
                  divu        zero, s9, a3
                  add         s2, a7, a4
                  c.sub       a1, a5
                  sll         zero, s10, s11
                  c.srli      a3, 14
                  sltiu       a7, zero, -334
                  srl         a7, a2, s8
                  srli        s10, gp, 24
                  slli        a7, s0, 29
                  sltu        s10, t5, s11
                  sub         zero, t5, s4
                  mul         a5, s10, s0
                  ori         s9, a0, 1906
                  mulh        tp, s9, s2
                  c.mv        ra, t6
                  c.srli      s0, 12
                  div         a5, t6, s11
                  srai        gp, sp, 7
                  slli        t4, a2, 0
                  c.xor       a1, a3
                  c.srai      a3, 1
                  rem         t0, s9, tp
                  c.srli      a2, 14
                  sra         s2, s3, a4
                  srl         sp, zero, s2
                  c.lui       s7, 3
                  div         s11, s8, gp
                  c.addi      t2, -1
                  sll         zero, a1, t2
                  c.mv        tp, s0
                  sll         sp, s3, s4
                  c.sub       s1, a0
                  c.mv        ra, gp
                  c.sub       a3, a4
                  xori        sp, s2, 1943
                  sra         a4, tp, a0
                  slti        a4, s1, -1454
                  add         t0, t6, t0
                  mulh        t1, a4, a2
                  or          s1, s7, s5
                  add         gp, t4, ra
                  andi        zero, s1, -1614
                  mulh        zero, a0, a0
                  c.and       a2, a0
                  c.mv        tp, a4
                  sll         s9, a0, a7
                  c.nop
                  c.lui       ra, 20
                  c.sub       s1, s1
                  sltiu       t2, a2, 1914
                  rem         a7, a2, s10
                  c.and       s0, a5
                  c.or        a4, a5
                  slli        zero, s3, 28
                  slt         s3, s3, gp
                  lui         s6, 515011
                  srai        sp, s9, 6
                  c.andi      s0, 18
                  c.and       a2, a3
                  andi        zero, t2, 1146
                  or          s1, t0, t6
                  ori         t1, a7, 129
                  slli        a7, t4, 0
                  sub         a2, a1, a5
                  addi        s7, s2, 257
                  xori        t0, sp, -1926
                  add         s4, s1, s5
                  c.or        a2, a1
                  c.addi16sp  sp, -16
                  c.srai      a3, 4
                  c.xor       a3, s0
                  c.add       a1, a3
                  or          s10, s11, tp
                  sltu        zero, a0, ra
                  divu        s2, gp, a0
                  c.add       t4, s4
                  c.sub       a3, a3
                  sub         s7, t3, t3
                  slti        s0, t4, -1397
                  c.mv        s11, s5
                  mulhu       tp, a2, s5
                  xori        s6, gp, -433
                  srli        s5, s9, 17
                  divu        a1, t5, a5
                  c.addi      t2, 26
                  c.li        s5, -1
                  sra         a7, sp, s9
                  mulh        a3, s5, t3
                  xor         s7, a4, s9
                  c.addi      s3, -1
                  sll         t3, s5, t3
                  c.andi      a3, -1
                  or          t2, gp, ra
                  add         s1, s6, t0
                  c.sub       a3, a0
                  c.addi16sp  sp, -16
                  and         zero, s7, t1
                  srl         s5, ra, tp
                  c.addi16sp  sp, -16
                  nop
                  xor         sp, a5, a3
                  or          sp, t3, a1
                  slt         s1, a4, s10
                  add         a5, t6, a2
                  c.xor       s1, a2
                  mul         t2, tp, t0
                  mulh        zero, s1, a1
                  srli        s7, s8, 15
                  ori         a1, t3, 1038
                  mul         a3, t3, s7
                  c.add       ra, a1
                  c.li        s10, 6
                  c.addi4spn  a1, sp, 240
                  srl         zero, a0, s8
                  xori        s6, a0, 61
                  c.srai      s0, 10
                  sltiu       s9, a1, -1200
                  lui         t3, 795062
                  xori        s10, s11, 691
                  srl         s10, s11, a7
                  auipc       zero, 181892
                  auipc       a5, 854375
                  addi        zero, s4, 655
                  sra         t1, t1, t0
                  mulhu       sp, s3, a6
                  c.sub       a2, a0
                  sltu        a6, a0, a1
                  and         t1, s9, s4
                  c.add       ra, t4
                  c.srai      a3, 24
                  xori        s9, s8, 557
                  add         s11, ra, t3
                  slt         s9, s8, s11
                  andi        a1, s7, 1328
                  mul         a1, t5, s3
                  c.addi16sp  sp, 400
                  c.andi      a2, -1
                  c.srli      a1, 11
                  slti        s1, a3, -1463
                  c.mv        t2, s10
                  srli        tp, s6, 11
                  slli        t2, t1, 17
                  c.addi      gp, 29
                  c.srli      a2, 22
                  c.srai      a3, 21
                  c.mv        s4, a0
                  or          t1, a2, s0
                  sltiu       t3, t5, -1727
                  c.nop
                  c.addi4spn  a3, sp, 128
                  divu        ra, s1, s7
                  c.addi4spn  a2, sp, 352
                  slti        zero, tp, 1897
                  mulh        s0, s0, s7
                  andi        zero, a3, 1355
                  c.andi      a3, 6
                  srai        t4, s9, 19
                  slli        a2, a0, 20
                  andi        a7, t2, 648
                  lui         s10, 969172
                  c.and       s1, a0
                  xori        a1, a5, -250
                  srli        ra, a7, 3
                  c.add       a4, s0
                  ori         zero, s7, 859
                  addi        zero, sp, 1814
                  c.srai      a2, 9
                  sltiu       s8, s11, -472
                  xori        s2, s10, -404
                  nop
                  srai        s11, a0, 17
                  c.nop
                  mul         a7, a1, a2
                  c.andi      a3, 4
                  c.srli      a4, 19
                  mul         t0, a3, t0
                  c.mv        ra, s8
                  c.and       a3, a3
                  sltiu       zero, a4, 646
                  sll         a6, a6, s6
                  c.addi16sp  sp, 64
                  c.addi      s2, 21
                  c.add       a5, s5
                  mulhu       s0, a2, s4
                  c.sub       a1, s0
                  and         a3, a2, s3
                  c.mv        a3, s6
                  lui         s1, 519385
                  c.sub       a2, a0
                  srai        a7, s8, 12
                  c.slli      ra, 28
                  andi        a1, s9, -2025
                  c.xor       a3, a2
                  c.srli      s0, 24
                  c.nop
                  c.and       s1, s0
                  lui         t1, 775137
                  slli        s6, t4, 31
                  mulh        t3, t1, t1
                  lui         s5, 40155
                  addi        t0, t6, -1102
                  mulhu       zero, a2, s2
                  c.addi      s1, -1
                  or          a2, t0, s3
                  xor         a5, s1, s9
                  sltiu       s4, sp, -1227
                  auipc       t1, 255354
                  c.sub       a3, a2
                  c.or        a2, a2
                  nop
                  slti        a7, s7, 273
                  c.xor       s1, a1
                  srli        t3, a6, 9
                  c.andi      a3, -1
                  c.srai      a2, 20
                  slt         zero, t0, s3
                  add         zero, t3, t6
                  c.addi16sp  sp, -16
                  sltiu       s4, gp, 1685
                  mulhu       s7, a3, a0
                  c.srli      a3, 7
                  add         tp, a0, a3
                  and         s9, s6, sp
                  c.addi      s4, 18
                  c.addi16sp  sp, 448
                  rem         sp, s9, t0
                  slti        tp, s7, 1520
                  mulhu       s10, tp, s8
                  c.sub       s0, a4
                  xor         s11, a2, a0
                  rem         t1, t2, t6
                  sltiu       zero, s6, 39
                  c.add       a2, ra
                  c.addi16sp  sp, 32
                  c.addi      s6, 11
                  div         t3, t5, t5
                  auipc       t1, 129460
                  mul         s6, s4, sp
                  xori        a5, a6, -53
                  div         s0, a1, s3
                  sltu        t0, a0, s4
                  c.srli      a3, 19
                  slt         t4, zero, s3
                  srl         s11, t5, t0
                  c.xor       a2, s0
                  addi        s6, s0, 829
                  sub         s5, t5, t5
                  c.lui       s3, 5
                  c.xor       a3, s0
                  srli        s10, t3, 18
                  sltiu       s8, a2, -199
                  xori        sp, s10, -1776
                  divu        zero, s0, s1
                  c.srai      s1, 22
                  and         t2, a2, zero
                  srli        s10, a5, 16
                  andi        t4, s3, -1552
                  c.nop
                  xori        ra, ra, -1022
                  mulh        t1, s9, s7
                  c.mv        t2, a7
                  srl         a4, s7, s5
                  and         zero, a0, s0
                  slli        a4, a1, 2
                  c.add       a2, a0
                  sra         sp, s1, t3
                  c.slli      sp, 11
                  srli        a4, s6, 24
                  mul         t1, a3, a0
                  c.lui       s11, 2
                  srli        ra, s9, 3
                  c.add       s10, s4
                  c.xor       a2, s0
                  c.addi4spn  s0, sp, 288
                  c.srai      a3, 1
                  c.sub       a2, a1
                  c.add       s2, ra
                  rem         s10, s7, a1
                  mulhu       tp, sp, a2
                  lui         a4, 863299
                  c.and       s1, a2
                  c.srli      a3, 12
                  c.andi      a3, -1
                  sra         zero, s9, s10
                  sltu        t1, t4, t6
                  c.xor       a3, a1
                  srai        s1, t0, 20
                  rem         s10, zero, a7
                  andi        t2, s7, -1686
                  mul         t0, s2, s10
                  add         zero, s11, a5
                  c.slli      s7, 16
                  mulhu       a3, a7, gp
                  c.andi      a3, -1
                  mulh        a2, s2, s11
                  and         ra, t6, a7
                  xor         s7, s4, s5
                  c.addi4spn  a2, sp, 608
                  slli        s11, s9, 3
                  mul         t0, s8, tp
                  c.mv        ra, tp
                  slli        a7, t4, 10
                  c.and       a2, a0
                  mul         s2, s1, s3
                  slt         zero, sp, ra
                  addi        s10, s10, -1680
                  c.or        a3, a3
                  sra         ra, s1, sp
                  c.addi16sp  sp, 112
                  add         a4, sp, gp
                  auipc       t0, 224279
                  c.srli      a3, 31
                  slli        s10, a5, 27
                  xor         zero, a4, t2
                  sltiu       zero, s9, -1058
                  andi        s4, s2, 1522
                  srli        t4, s3, 30
                  c.addi16sp  sp, 352
                  srl         s5, a2, s3
                  c.lui       a1, 12
                  sub         a7, s4, a3
                  divu        a1, s4, s9
                  srli        s7, t1, 1
                  div         a4, s9, a1
                  c.srai      a2, 26
                  c.xor       a2, a1
                  c.srai      a3, 25
                  and         s5, s6, ra
                  sltiu       t1, t1, 865
                  c.srli      a3, 29
                  rem         t1, a2, t4
                  lui         t3, 43407
                  c.lui       a7, 27
                  c.addi16sp  sp, 208
                  c.and       s0, a1
                  srai        a4, s3, 10
                  c.andi      a3, 2
                  sub         s1, s10, s3
                  srl         s2, s7, a2
                  c.xor       a3, a3
                  c.add       s6, s8
                  c.addi4spn  s1, sp, 656
                  nop
                  xori        a1, a4, -461
                  sll         s4, a1, t3
                  and         s4, a4, t5
                  slt         a1, a4, s8
                  and         s2, a0, t2
                  ori         a2, zero, -787
                  sltu        s6, ra, s4
                  c.addi      a5, 27
                  srl         zero, s10, a6
                  mulhsu      t1, t1, s9
                  andi        s5, s2, 595
                  ori         gp, ra, -241
                  c.slli      a7, 2
                  c.li        s7, 29
                  li         t2, 0x69748ddd #start riscv_int_numeric_corner_stream_8
                  li         a5, 0x0
                  li         t4, 0x0
                  li         s6, 0x0
                  li         t3, 0x1
                  li         s11, 0x1
                  li         s4, 0x0
                  li         s8, 0x0
                  li         a2, 0x6b51bc1a
                  li         tp, 0x0
                  c.mv        s3, t5
                  add         zero, a4, a1
                  add         t0, t0, s5
                  c.addi      a7, -1
                  div         s0, s5, s6
                  mul         a1, tp, tp
                  mulh        ra, a3, t4
                  c.addi      s3, -1
                  addi        s10, s7, 1719
                  c.mv        t0, ra
                  mulh        s2, a3, a5
                  lui         t3, 617425
                  auipc       s5, 429976
                  c.addi      ra, 7
                  c.li        ra, -1
                  divu        a7, s3, s2
                  mulh        t0, t6, a5 #end riscv_int_numeric_corner_stream_8
                  c.sub       s1, a0
                  mulhu       a7, a2, t1
                  c.srli      s0, 27
                  sub         a1, s2, s7
                  divu        a3, a4, sp
                  divu        s3, a6, t5
                  mulhu       s3, s11, s11
                  and         s6, s0, s2
                  c.add       s0, a2
                  xori        t3, ra, 191
                  mulh        tp, a3, s1
                  sra         sp, t6, s3
                  sll         a2, s1, s10
                  rem         s0, zero, a5
                  c.nop
                  c.addi4spn  s0, sp, 416
                  c.addi      t1, -1
                  slli        s8, s2, 18
                  slti        t1, a0, 1897
                  mul         a2, s7, s6
                  slti        a1, t4, 1289
                  c.mv        ra, s2
                  sll         s6, a3, t0
                  divu        zero, a4, sp
                  srai        zero, s11, 2
                  xor         t1, s6, t0
                  mulhsu      zero, ra, t2
                  add         s9, a1, s1
                  c.addi16sp  sp, -16
                  add         s10, a5, a5
                  sub         s2, s0, s8
                  div         zero, a6, a0
                  c.addi16sp  sp, 176
                  c.or        s0, s1
                  sub         a1, a1, a0
                  c.lui       t3, 1
                  slt         s4, s3, a4
                  rem         zero, t1, tp
                  xor         s9, s0, t4
                  mulhsu      s2, t1, s5
                  srli        a7, s11, 25
                  sub         s10, s6, s5
                  c.xor       a3, s0
                  c.srai      a3, 11
                  c.xor       a2, a5
                  c.slli      t4, 28
                  mulhu       s6, s5, s5
                  add         s11, s5, s3
                  c.add       t4, a6
                  div         zero, s10, s9
                  srl         t1, s9, a7
                  xori        s10, t5, -1412
                  srai        t1, s11, 23
                  lui         zero, 255578
                  slli        zero, t3, 11
                  c.slli      ra, 2
                  lui         zero, 760915
                  div         a5, s7, t6
                  c.li        a5, -1
                  c.and       a1, a3
                  mulhu       s6, s6, a1
                  xor         s1, s9, a2
                  xor         zero, s3, s11
                  c.and       s0, a1
                  or          a3, a1, t4
                  sltu        a6, s10, a4
                  rem         tp, s4, t4
                  mulh        ra, t1, s3
                  div         a7, s0, s10
                  nop
                  sltiu       s11, s3, -1716
                  sltiu       s9, a7, 1459
                  ori         s6, s4, 2006
                  srli        a7, a2, 25
                  c.mv        s8, s6
                  divu        s4, a7, a0
                  c.li        gp, -1
                  xor         s2, s9, a5
                  auipc       s1, 223043
                  c.srli      a3, 13
                  c.li        tp, -1
                  c.or        s1, a3
                  xori        a4, t0, 1520
                  c.add       ra, a4
                  c.slli      s3, 21
                  c.slli      ra, 31
                  srli        t0, a6, 5
                  c.or        a1, a3
                  c.slli      s4, 6
                  c.slli      a2, 30
                  c.andi      a2, -1
                  c.addi4spn  a3, sp, 192
                  slti        ra, s8, 680
                  slt         t2, t4, a1
                  xor         s10, s9, s0
                  div         s9, a1, a3
                  c.xor       a3, s1
                  andi        ra, ra, -1406
                  addi        s2, t6, -802
                  slli        t3, s7, 19
                  xor         a5, s6, sp
                  c.mv        s3, s2
                  c.mv        a4, a6
                  sra         s4, s7, a1
                  srai        s7, t5, 9
                  sub         zero, s11, a6
                  or          tp, t5, s7
                  c.sub       a2, a2
                  sltu        s6, a4, sp
                  lui         a5, 934403
                  slli        zero, a0, 16
                  c.srli      a3, 4
                  srli        s5, t4, 11
                  c.addi4spn  s0, sp, 784
                  ori         a5, a3, -156
                  c.nop
                  or          t2, tp, a7
                  c.andi      a1, -1
                  sltu        s1, s3, a5
                  mulhu       s1, t5, a4
                  c.or        a2, a3
                  xori        s0, s6, -1268
                  c.mv        a6, tp
                  c.and       a5, a2
                  divu        zero, zero, s11
                  c.nop
                  slti        zero, s6, -1049
                  add         s11, s11, a5
                  addi        a6, s4, 111
                  srl         s3, s9, s9
                  mul         ra, a7, t2
                  add         a4, s7, s9
                  srai        t0, t4, 1
                  c.or        a1, a3
                  sra         a6, a3, s7
                  c.sub       a3, a0
                  c.andi      a2, 29
                  srli        s0, s4, 10
                  c.xor       a2, a0
                  srl         a6, t2, a1
                  sll         s11, t6, t3
                  c.lui       s4, 1
                  c.or        s1, a0
                  auipc       s0, 598678
                  c.and       s0, a3
                  rem         gp, a5, a7
                  c.add       ra, a0
                  c.mv        s0, s10
                  sll         t1, t3, s8
                  divu        s9, a1, s0
                  slli        t4, a2, 18
                  sub         a7, t3, zero
                  and         sp, tp, tp
                  mulhsu      s11, s11, t0
                  slti        t2, a5, -867
                  c.addi16sp  sp, 128
                  c.lui       s6, 19
                  c.addi      s7, -1
                  srl         a3, s6, gp
                  c.mv        sp, s6
                  mul         s11, t3, ra
                  srl         s5, a7, s8
                  mulhsu      a1, tp, t6
                  c.xor       s1, a3
                  c.lui       ra, 3
                  c.addi16sp  sp, 160
                  c.slli      a3, 27
                  c.sub       a3, a3
                  c.xor       a3, s1
                  slt         s1, s5, a3
                  c.or        a1, s1
                  srai        s6, s9, 28
                  c.li        a4, -1
                  add         t4, a7, a5
                  c.li        s6, -1
                  c.addi4spn  a3, sp, 496
                  slli        s1, sp, 13
                  add         s0, a6, gp
                  xor         s4, a1, s1
                  c.addi4spn  a3, sp, 544
                  xor         s4, s4, s1
                  sltiu       s7, a3, -1854
                  c.li        ra, 20
                  c.nop
                  xor         s6, tp, a1
                  or          s7, a7, sp
                  c.slli      a3, 1
                  c.add       ra, s5
                  nop
                  mul         s8, gp, a3
                  xori        s1, s7, 1112
                  andi        zero, t5, -530
                  c.addi      s8, 26
                  sltu        a1, s10, s3
                  c.srli      a3, 13
                  c.li        s5, 9
                  slti        zero, t1, -359
                  and         s9, a6, s3
                  or          s5, t5, t2
                  and         sp, s5, s10
                  div         zero, s0, zero
                  c.addi4spn  a1, sp, 608
                  c.and       a2, a0
                  divu        zero, s0, ra
                  nop
                  ori         s4, s10, 586
                  c.and       a3, a0
                  and         zero, t4, a1
                  mul         s3, zero, s0
                  sltiu       t2, s3, -289
                  srai        zero, a2, 28
                  xor         a6, a1, a6
                  c.sub       a2, a5
                  sll         s6, t6, a0
                  c.srli      s0, 3
                  c.addi      s4, -1
                  auipc       ra, 998931
                  ori         zero, t1, 288
                  c.mv        t3, s1
                  c.or        a3, s1
                  c.and       a2, a1
                  c.li        a2, -1
                  and         s3, s9, a7
                  c.sub       s0, a2
                  mul         a5, s7, s7
                  slli        a5, s10, 27
                  andi        tp, s5, -905
                  lui         s0, 22443
                  xori        ra, s2, -962
                  nop
                  c.or        a1, a0
                  li         a3, 0x51ae7562 #start riscv_int_numeric_corner_stream_1
                  li         t3, 0x55ee2821
                  li         s8, 0x1
                  li         a2, 0x0
                  li         s11, 0x0
                  li         ra, 0x0
                  li         s9, 0x3e5a9e5f
                  li         t0, 0x1
                  li         s10, 0x56373da1
                  li         s2, 0x0
                  div         t2, t6, t5
                  nop
                  c.mv        sp, s8
                  lui         zero, 181784
                  mul         zero, a3, s4
                  lui         zero, 471548
                  c.li        t3, -1
                  c.li        a4, -1
                  rem         t3, t4, s2
                  sub         a1, s8, t6
                  auipc       t4, 138346
                  nop
                  c.mv        t2, s9
                  c.mv        t3, a4
                  mulhsu      sp, s2, a0
                  mul         zero, s11, a4
                  mul         s11, a6, s0 #end riscv_int_numeric_corner_stream_1
                  c.andi      a3, 4
                  c.addi      t4, -1
                  andi        tp, s1, 1776
                  sltiu       s9, s11, -1114
                  div         a6, s1, s2
                  srli        t0, s10, 22
                  and         s10, s5, t1
                  andi        s11, t0, -461
                  srai        s4, a5, 9
                  sltiu       ra, a0, 1577
                  mul         t1, ra, s0
                  sltiu       a6, gp, 1067
                  nop
                  c.addi4spn  a5, sp, 48
                  srai        sp, a7, 17
                  c.andi      a3, 1
                  c.or        a2, s1
                  srli        a3, s5, 11
                  sra         tp, t0, s11
                  ori         tp, ra, -1057
                  c.sub       a1, a0
                  c.li        ra, -1
                  and         ra, s2, s2
                  div         t2, zero, sp
                  c.xor       a2, a4
                  sll         s0, gp, s9
                  slt         s2, t2, t6
                  or          a7, t1, a6
                  srl         a1, s11, s6
                  sltiu       a5, s2, 696
                  c.xor       s0, a3
                  srai        a3, s10, 13
                  addi        a6, a7, 1377
                  div         s10, s0, a6
                  sub         tp, a2, zero
                  sra         s3, gp, t3
                  mulhsu      t4, t0, zero
                  slti        a5, s6, 1888
                  nop
                  slt         s10, tp, t0
                  auipc       t1, 381729
                  slli        a3, t6, 10
                  c.sub       a5, a3
                  mulh        s11, t0, a1
                  srai        zero, s0, 10
                  c.xor       s0, a3
                  addi        a4, s9, -1383
                  or          zero, s11, s5
                  sub         t4, s4, s2
                  slti        zero, t0, 947
                  sra         s5, s2, s3
                  c.or        a1, a2
                  c.addi4spn  s1, sp, 448
                  div         s5, a4, t4
                  c.add       s0, s5
                  srl         sp, s0, gp
                  c.and       s1, a3
                  c.addi4spn  a1, sp, 912
                  c.xor       a4, s1
                  c.srli      a3, 15
                  srli        a6, t5, 5
                  c.lui       s10, 1
                  c.nop
                  or          a3, s11, a4
                  mulhu       t1, a6, a0
                  c.lui       s4, 25
                  slli        s2, t1, 28
                  sltiu       gp, t2, 537
                  mulhsu      s10, s4, a5
                  c.slli      a5, 31
                  xori        a4, t0, -265
                  ori         a2, s6, -1524
                  lui         s5, 898605
                  c.nop
                  c.addi      ra, 30
                  or          a5, sp, s1
                  c.xor       a3, a3
                  srai        zero, a5, 22
                  mul         zero, ra, a5
                  c.andi      s1, 26
                  srai        t1, ra, 25
                  c.addi16sp  sp, -16
                  c.addi4spn  s1, sp, 304
                  c.or        s1, a0
                  c.and       a2, s1
                  nop
                  c.li        ra, 29
                  c.and       a1, a1
                  c.sub       a1, s0
                  c.lui       a5, 22
                  c.lui       s10, 17
                  srli        s8, s6, 21
                  sltiu       s9, s1, -119
                  and         gp, t1, s5
                  c.sub       a2, a3
                  c.srli      a3, 30
                  slti        s2, t3, -390
                  sltiu       t3, ra, 790
                  add         t0, t3, t6
                  slli        zero, s4, 30
                  srai        a3, a2, 11
                  mulhu       t2, s10, s5
                  slli        s8, a1, 1
                  c.lui       a5, 1
                  srli        s6, sp, 16
                  c.and       a1, s0
                  xor         s7, ra, a0
                  auipc       s6, 690791
                  srli        t3, a6, 25
                  auipc       a3, 759678
                  or          ra, s7, s7
                  slt         zero, s0, a6
                  ori         a7, t3, 589
                  add         s6, t2, a5
                  div         s5, t2, s0
                  c.slli      s10, 24
                  mulhu       t1, s8, a6
                  or          ra, a6, gp
                  c.xor       a2, a0
                  srl         t2, t1, s8
                  c.addi4spn  a2, sp, 976
                  slli        t0, s7, 2
                  c.slli      ra, 6
                  c.slli      t0, 27
                  add         s9, t3, a2
                  sll         s9, a5, a4
                  and         s3, a0, t3
                  lui         s11, 597260
                  mulhsu      t0, t2, t1
                  c.addi16sp  sp, 224
                  c.or        a2, s1
                  c.srli      a2, 3
                  c.li        s9, 25
                  c.sub       a2, a2
                  c.addi16sp  sp, -16
                  c.mv        s6, ra
                  c.add       t4, t4
                  mul         s4, t5, s7
                  sltiu       s6, zero, 1885
                  sra         s4, a1, a4
                  c.lui       s3, 21
                  andi        t3, a6, 1175
                  slti        s7, s7, 1810
                  nop
                  srl         s4, t5, t2
                  sub         t0, a4, s0
                  add         t1, t2, t5
                  sltu        ra, s11, tp
                  divu        s4, s6, t2
                  sra         zero, s1, t3
                  xor         s11, s3, a3
                  srli        t3, t6, 20
                  c.or        a2, a2
                  c.lui       gp, 12
                  ori         zero, s3, 22
                  c.srai      s1, 30
                  and         s6, s0, sp
                  sll         s9, t3, a0
                  or          a7, t2, a0
                  xor         t0, gp, s6
                  xori        a3, a2, 1398
                  addi        tp, s1, 1335
                  mulh        a4, gp, a1
                  nop
                  c.add       s8, s4
                  c.nop
                  c.xor       s1, a2
                  srai        s9, zero, 9
                  c.or        a2, a3
                  c.srli      s1, 7
                  c.addi4spn  a2, sp, 592
                  mulh        s5, s5, t2
                  xori        zero, a6, -872
                  or          s2, a0, s0
                  div         t0, a5, t0
                  c.addi4spn  a3, sp, 992
                  mulhsu      s9, t5, s8
                  c.li        s11, 26
                  add         a2, s0, s10
                  nop
                  sub         s10, a0, s3
                  and         s7, a1, t3
                  slti        t4, a5, 31
                  c.addi      t3, 20
                  sltu        t0, t3, s2
                  c.mv        s6, tp
                  lui         gp, 461711
                  addi        tp, s6, 1743
                  c.srli      a1, 15
                  nop
                  mulhsu      s11, a5, s9
                  c.or        a5, a1
                  slti        s7, s2, 1121
                  c.srai      a3, 8
                  sltiu       zero, sp, 1782
                  sub         sp, s4, a3
                  mul         zero, a5, a5
                  srai        t1, t6, 23
                  sltiu       s5, sp, -182
                  mulhu       s9, t6, t2
                  c.srli      a2, 8
                  c.sub       a3, a0
                  c.lui       s0, 23
                  c.and       a3, a2
                  sltu        a5, s7, a6
                  ori         s4, a3, -553
                  c.addi      s10, -1
                  mulh        s11, a7, a2
                  sra         t4, a0, t2
                  c.li        tp, 24
                  sll         t0, a3, a1
                  c.addi16sp  sp, 224
                  andi        ra, a0, -241
                  nop
                  div         tp, a5, a7
                  c.srai      a2, 17
                  slli        zero, ra, 19
                  mulhu       zero, a4, s10
                  c.and       a2, a3
                  c.srli      a2, 27
                  lui         s6, 239350
                  srai        a1, s10, 15
                  c.mv        a6, tp
                  srli        t2, t0, 4
                  c.nop
                  or          s11, a2, ra
                  div         s1, t4, a2
                  c.sub       a1, a3
                  sltiu       s5, t5, 1447
                  xor         a4, ra, a2
                  andi        s7, a4, 682
                  lui         s1, 377474
                  mul         a6, s5, s11
                  sll         zero, s4, a6
                  sltu        t2, a1, s2
                  rem         s6, t5, s8
                  sltu        t3, s6, t1
                  c.add       t4, t3
                  xori        s1, t2, 1670
                  mul         s8, t5, s11
                  c.xor       a3, a1
                  mulh        s7, s5, s6
                  srl         s8, t2, s6
                  c.addi      s8, 14
                  ori         s4, s2, 868
                  c.srai      a5, 1
                  c.or        a3, s1
                  c.sub       s1, a3
                  and         s4, t3, t3
                  c.srli      s0, 18
                  slli        t4, t6, 4
                  sltu        zero, a0, a3
                  and         s6, a2, s5
                  srli        t0, gp, 31
                  rem         zero, zero, a0
                  srl         s3, a0, s8
                  slli        s4, a1, 6
                  or          zero, zero, s6
                  slti        zero, zero, 818
                  xori        s1, gp, -329
                  mulhu       tp, sp, ra
                  lui         s3, 950866
                  and         a5, ra, s1
                  c.addi4spn  a2, sp, 320
                  nop
                  mulhsu      t0, a3, gp
                  addi        zero, t3, 1731
                  c.xor       a2, a2
                  auipc       s4, 989913
                  rem         zero, s11, a6
                  c.sub       a2, a2
                  nop
                  c.xor       a2, a2
                  c.nop
                  c.li        ra, -1
                  mul         a7, t2, s7
                  slli        gp, sp, 12
                  c.and       a3, a4
                  srai        s1, s4, 31
                  ori         zero, zero, 631
                  c.slli      a7, 9
                  srai        a4, t5, 22
                  auipc       a5, 313210
                  add         t0, s6, zero
                  slli        a2, gp, 7
                  div         zero, t0, a0
                  c.mv        a6, s8
                  andi        a1, s0, 348
                  divu        zero, ra, t3
                  c.addi      s1, -1
                  c.add       sp, ra
                  c.andi      a2, -1
                  nop
                  sub         s2, s11, a0
                  slti        tp, s11, 355
                  lui         t2, 595138
                  divu        s10, s10, s5
                  c.sub       a2, a3
                  mulh        s6, t3, s5
                  c.addi16sp  sp, -16
                  add         s8, s1, ra
                  xor         s1, t3, t3
                  slli        zero, t3, 20
                  mulhu       t2, gp, s3
                  c.andi      a3, -1
                  c.srli      a3, 16
                  c.or        a3, a1
                  sltu        a2, a5, s11
                  c.slli      ra, 29
                  srli        a3, a6, 30
                  sltiu       s4, s7, -371
                  lui         t4, 726943
                  c.addi4spn  a3, sp, 640
                  c.andi      s1, 19
                  c.xor       a3, a0
                  auipc       s7, 137782
                  c.addi4spn  a3, sp, 464
                  nop
                  c.and       a1, a1
                  c.sub       s0, a2
                  add         t4, zero, a1
                  nop
                  mul         zero, t3, t4
                  lui         s11, 939519
                  add         s0, a5, a7
                  ori         gp, a3, -766
                  add         s10, a3, s10
                  c.or        a3, a3
                  c.li        a5, 18
                  div         zero, a6, gp
                  srli        a4, s5, 31
                  mulhsu      a6, s5, ra
                  srl         ra, gp, zero
                  or          zero, t1, s0
                  c.srli      a1, 15
                  c.sub       s1, a2
                  ori         t2, s8, -1689
                  slti        s9, s4, 1633
                  lui         zero, 200817
                  c.xor       a3, a1
                  srli        zero, a6, 4
                  sltiu       sp, s7, 64
                  nop
                  sub         s10, s7, s5
                  c.addi4spn  a1, sp, 624
                  c.andi      a3, 5
                  or          s8, a3, s10
                  c.slli      a2, 1
                  c.xor       s1, a2
                  lui         t0, 134223
                  c.li        s11, 29
                  sltiu       zero, s1, 1430
                  sltiu       ra, s9, -246
                  mulhu       s2, s9, s1
                  andi        zero, s2, 939
                  sltiu       s11, s0, -185
                  slt         a5, t3, s3
                  srl         a5, a1, tp
                  c.nop
                  mulh        s5, tp, s1
                  slli        s11, a4, 9
                  ori         s11, a2, -931
                  c.srli      a3, 13
                  xori        zero, s6, 603
                  c.srli      s1, 11
                  c.lui       t1, 4
                  mul         a2, s1, t4
                  srl         s1, s9, a7
                  c.addi16sp  sp, -16
                  div         s8, a2, a1
                  c.and       s0, a3
                  sltu        s9, a6, a5
                  mulhu       s0, t2, a5
                  mulh        ra, s3, s0
                  xori        s10, t2, 1859
                  sub         s8, a7, a5
                  ori         a1, t4, 737
                  or          s8, t5, a3
                  auipc       s4, 767010
                  c.add       a7, t6
                  sll         s9, t1, gp
                  mulhu       zero, zero, a5
                  and         s11, t3, a6
                  c.addi4spn  a3, sp, 784
                  c.xor       s0, a1
                  nop
                  divu        t0, t2, t2
                  c.li        a1, -1
                  c.sub       s0, s1
                  c.slli      s7, 11
                  mulhsu      t0, a6, a6
                  c.andi      a3, 5
                  mulhsu      a7, t1, a5
                  divu        a5, s9, gp
                  mul         t1, s7, tp
                  c.and       a3, a2
                  c.srai      a3, 12
                  div         gp, s9, gp
                  mulh        a2, s1, s0
                  sltiu       t4, zero, -1342
                  ori         s7, s8, -25
                  c.add       s11, t6
                  mulhu       a7, a6, s0
                  srl         s10, t3, a7
                  c.and       s1, a2
                  slt         zero, zero, t2
                  ori         a5, s7, -1857
                  mulh        gp, s1, s2
                  c.mv        t2, s3
                  rem         s8, s7, t5
                  srli        t3, sp, 6
                  auipc       a4, 47219
                  mulhu       s0, s0, s9
                  add         a6, s6, s2
                  c.addi4spn  a2, sp, 272
                  and         t4, s3, t2
                  c.addi16sp  sp, -16
                  and         s6, s6, gp
                  c.or        a1, a4
                  sltu        s5, s6, a1
                  xori        tp, ra, -315
                  sra         a7, a0, a3
                  c.and       a3, a3
                  sll         sp, t3, t1
                  c.or        a2, a2
                  c.or        a3, a1
                  and         a6, s11, a1
                  c.li        t3, -1
                  c.xor       a3, a1
                  slli        sp, s11, 14
                  slti        a1, s7, 1708
                  auipc       t4, 7441
                  rem         a4, t4, t5
                  sltu        t1, t3, s4
                  andi        zero, a6, 1423
                  c.andi      a2, -1
                  srl         a5, s3, tp
                  mulhu       zero, s7, a1
                  andi        gp, a2, 1228
                  c.addi16sp  sp, 256
                  xori        s1, sp, 254
                  slli        a3, t4, 26
                  c.lui       gp, 16
                  div         t1, s11, s6
                  c.sub       a3, a2
                  c.addi      a2, -1
                  srl         a6, a3, a2
                  nop
                  c.srai      s1, 7
                  c.sub       a2, a3
                  nop
                  xori        gp, s10, 1465
                  c.mv        s6, gp
                  rem         t0, s5, a6
                  c.add       ra, s6
                  divu        sp, s0, tp
                  sub         s1, s4, a1
                  xor         s8, s0, a6
                  xori        zero, tp, 55
                  c.sub       s1, s0
                  c.add       ra, s4
                  slti        s3, s8, 1863
                  xori        t1, tp, 1109
                  sub         tp, a4, a5
                  add         a7, s1, a7
                  add         zero, s5, s3
                  xori        t1, s8, 280
                  add         a5, s1, t2
                  c.addi16sp  sp, -16
                  or          t0, s0, zero
                  c.add       s0, s7
                  mulhu       s8, a5, a0
                  c.srai      a3, 25
                  c.addi16sp  sp, 384
                  srl         t2, s1, zero
                  slt         s3, t5, t4
                  sub         t4, s8, t0
                  c.slli      s7, 12
                  sra         s11, t5, a0
                  c.srli      a2, 24
                  c.addi      s7, 25
                  c.srai      a2, 27
                  c.slli      s9, 15
                  add         s11, a3, a5
                  and         a3, t4, t0
                  auipc       zero, 445923
                  and         a3, a5, t3
                  c.srli      a4, 28
                  c.li        a2, 12
                  c.sub       s1, a2
                  mulh        s11, a4, s10
                  c.lui       ra, 8
                  mulh        ra, a7, s1
                  div         s0, s0, s3
                  or          s1, t5, a0
                  c.srli      s0, 4
                  c.srli      a3, 2
                  rem         a4, a2, gp
                  sub         s3, s7, a5
                  rem         a6, s4, s0
                  slti        s8, s10, 1561
                  sra         gp, s0, a5
                  c.addi4spn  a2, sp, 384
                  mul         a2, s9, a4
                  c.li        t0, 9
                  add         t4, a1, s11
                  srai        zero, s5, 10
                  c.addi      t2, -1
                  c.sub       a2, a3
                  sub         t4, a5, s9
                  c.mv        gp, a7
                  mul         t2, s1, zero
                  srl         ra, a5, a2
                  c.nop
                  c.addi16sp  sp, -16
                  lui         s6, 510882
                  divu        s2, t4, s10
                  nop
                  srl         a5, t2, t2
                  c.srai      s1, 20
                  c.nop
                  srli        t4, s1, 30
                  divu        s7, t1, s1
                  c.or        a2, a0
                  add         a6, t3, t3
                  or          s10, s7, t2
                  srli        s0, s2, 15
                  sltu        s11, a5, t4
                  andi        s4, a0, 572
                  mul         zero, ra, t5
                  c.xor       a3, a3
                  c.srai      a3, 29
                  c.addi4spn  s1, sp, 624
                  ori         s3, a5, 1709
                  add         a7, s11, s9
                  slti        a5, s8, 1933
                  c.addi4spn  a1, sp, 160
                  slli        zero, t5, 1
                  c.and       a3, a3
                  c.add       ra, a4
                  auipc       a6, 997676
                  c.andi      a3, -1
                  c.sub       s1, a1
                  andi        t3, a1, -1351
                  srai        ra, t1, 11
                  srli        s2, s6, 19
                  c.li        s8, -1
                  c.nop
                  c.and       a2, a4
                  mulhsu      s0, a7, a0
                  add         a1, a1, gp
                  divu        s5, s7, s5
                  andi        a4, t2, 253
                  slli        s9, s1, 13
                  slli        zero, s1, 16
                  xori        a1, tp, -1271
                  c.li        a4, 15
                  ori         s1, a6, 73
                  c.xor       a3, a2
                  slti        zero, s4, -1935
                  c.lui       a7, 7
                  lui         s0, 125998
                  xor         t1, s5, s2
                  lui         t3, 655294
                  c.addi16sp  sp, 240
                  mul         s6, s4, s1
                  mulhu       a3, tp, a2
                  c.lui       a5, 23
                  or          s8, t4, t2
                  sltiu       zero, s8, -1905
                  mulh        zero, t2, t2
                  c.sub       a1, a3
                  c.addi      ra, 8
                  srl         s2, s8, t2
                  mul         a1, t4, s2
                  andi        s3, t6, -1394
                  rem         zero, t0, t4
                  c.addi4spn  a2, sp, 64
                  c.slli      s9, 25
                  slli        a2, s9, 22
                  auipc       a6, 894926
                  c.addi      s10, -1
                  srai        t3, a0, 1
                  rem         a3, zero, gp
                  srl         sp, s8, s7
                  andi        zero, t2, -124
                  c.add       s6, a4
                  lui         s3, 141982
                  c.lui       s8, 7
                  sra         s9, sp, a1
                  mulhu       a6, s1, a5
                  c.add       t4, s8
                  mulh        s4, s3, tp
                  slli        zero, s9, 13
                  rem         s6, t4, a7
                  srai        zero, a7, 10
                  c.srli      a3, 9
                  sll         t4, tp, tp
                  c.addi16sp  sp, 64
                  rem         a4, a7, a2
                  xor         ra, a1, t3
                  c.or        a3, a0
                  c.li        s8, -1
                  mulh        a4, sp, s7
                  slli        tp, a3, 24
                  andi        gp, a0, 1613
                  sltiu       ra, t3, -1204
                  c.li        a4, -1
                  ori         a7, t1, 164
                  xori        t2, a0, -1908
                  ori         s7, sp, -1672
                  c.slli      s7, 7
                  c.sub       a3, a2
                  c.addi      t3, 9
                  srli        t4, gp, 16
                  c.srli      a2, 7
                  c.or        a3, a1
                  sub         zero, t4, t1
                  c.mv        ra, s8
                  c.andi      a3, -1
                  c.sub       a3, a3
                  sltu        s9, ra, s10
                  c.sub       a2, a5
                  mulhsu      a6, a6, s6
                  xor         t2, s3, ra
                  c.xor       a5, a1
                  or          gp, s6, a6
                  slli        t1, a4, 2
                  slli        t3, s3, 7
                  c.xor       a3, a0
                  sub         t2, zero, sp
                  auipc       t1, 396919
                  lui         zero, 254524
                  c.andi      s0, -1
                  c.slli      s5, 16
                  c.mv        ra, a3
                  add         sp, zero, t4
                  divu        a7, zero, s5
                  c.add       a1, s0
                  srai        a2, a5, 23
                  c.and       a3, a0
                  and         a1, sp, a6
                  slli        zero, s0, 4
                  div         t4, t4, t1
                  c.lui       gp, 17
                  sub         s2, s5, sp
                  sll         t4, s4, t6
                  srai        s6, a4, 1
                  c.sub       a2, a3
                  c.mv        t4, s1
                  and         t3, a7, s11
                  srli        zero, s7, 23
                  c.addi16sp  sp, -16
                  srl         s8, s8, s2
                  mul         t4, s10, s4
                  srl         a7, a3, t0
                  sll         zero, s3, a1
                  sltu        a4, a1, s11
                  divu        zero, s9, gp
                  c.sub       a3, a2
                  srli        a2, a0, 29
                  srl         s2, t4, t0
                  mul         a2, s10, a1
                  c.addi4spn  a1, sp, 992
                  or          a2, s7, a2
                  sra         zero, a3, t2
                  srai        s10, a7, 13
                  auipc       zero, 744419
                  c.li        t1, -1
                  c.srai      a2, 27
                  slli        s9, s0, 4
                  mul         s7, a6, a6
                  c.addi      a7, 24
                  c.add       s11, sp
                  sll         s4, t1, t5
                  c.sub       s1, a2
                  and         a2, ra, s9
                  srli        s6, s8, 14
                  slt         s2, s6, s1
                  mulhu       a4, s3, ra
                  c.srai      s0, 25
                  c.mv        s8, t6
                  add         a7, a5, s4
                  lui         zero, 461264
                  and         s8, s10, a6
                  sltu        a4, a0, s4
                  c.li        t3, 5
                  mul         s4, s10, s9
                  addi        s4, tp, 1837
                  srl         sp, a6, a6
                  srai        a1, s6, 0
                  sra         t3, t2, a6
                  srli        s11, a2, 3
                  srai        t0, a7, 6
                  c.nop
                  add         tp, s8, t1
                  xor         s8, a3, a7
                  mulh        a4, zero, s0
                  c.add       t3, t4
                  c.li        t2, 21
                  srai        t1, s9, 17
                  mulhsu      s11, a7, a5
                  slli        t4, a5, 28
                  div         s8, s10, a3
                  divu        t4, t0, s3
                  add         a7, a7, s3
                  c.addi4spn  a5, sp, 864
                  lui         s0, 291278
                  c.and       s1, a3
                  slt         zero, gp, t5
                  slti        tp, tp, 2018
                  nop
                  c.addi16sp  sp, 96
                  c.and       a3, a2
                  c.or        s1, a3
                  c.addi16sp  sp, -16
                  auipc       a6, 453791
                  c.andi      a2, -1
                  lui         zero, 430210
                  c.and       a3, a0
                  mulh        s5, s2, t6
                  c.andi      a2, -1
                  mulhu       s5, t3, s11
                  c.addi16sp  sp, -16
                  mulhsu      t1, s11, s8
                  c.addi      s6, -1
                  rem         s1, t1, t4
                  c.nop
                  and         t3, ra, s5
                  lui         s0, 233616
                  c.andi      a2, 7
                  c.addi4spn  a3, sp, 816
                  sra         s7, s8, zero
                  lui         s3, 475140
                  nop
                  mulh        gp, s8, t5
                  c.srli      a1, 20
                  sra         ra, zero, ra
                  slti        a5, a3, -1446
                  sub         a7, s9, a5
                  srai        s9, s5, 8
                  divu        s2, t1, a4
                  sub         sp, a2, tp
                  c.srai      a1, 24
                  and         t4, a5, s10
                  c.andi      a3, 25
                  andi        zero, a1, -1444
                  xori        t1, s3, -1489
                  slt         a7, a3, s4
                  c.addi16sp  sp, 64
                  c.sub       s1, a3
                  srai        t3, a3, 23
                  c.xor       a3, a1
                  c.addi16sp  sp, 304
                  c.sub       a3, a2
                  c.li        t0, -1
                  c.xor       a2, a0
                  c.and       a3, a3
                  srai        zero, s8, 3
                  and         a6, t4, s5
                  mul         s7, t4, t2
                  sltu        a4, gp, a3
                  srli        s9, a6, 2
                  auipc       s5, 407351
                  c.or        a3, a0
                  sltiu       s7, t0, 1675
                  nop
                  addi        sp, s0, 546
                  c.lui       s8, 13
                  sll         s9, s5, s1
                  sub         s10, s11, a0
                  andi        s6, s3, 947
                  nop
                  addi        zero, t5, -1387
                  sltiu       s10, t6, 1212
                  mulhsu      a2, a6, a2
                  c.lui       s10, 9
                  c.lui       ra, 15
                  div         a4, t6, s7
                  slti        ra, s9, 1576
                  sub         a5, zero, a5
                  c.nop
                  c.addi4spn  a1, sp, 848
                  sltu        zero, a6, s11
                  slt         tp, s8, t3
                  nop
                  c.lui       ra, 16
                  sltu        s9, s5, s11
                  andi        s0, a0, 290
                  or          sp, a2, t6
                  slli        t3, s11, 21
                  slli        a6, sp, 14
                  andi        s6, a1, 1413
                  xor         ra, sp, a3
                  c.nop
                  xor         a3, t6, a3
                  sll         tp, s4, s3
                  c.srli      s0, 9
                  srai        tp, t0, 4
                  srai        zero, s4, 12
                  sltiu       s10, s10, -794
                  sltiu       a6, s0, 1124
                  mul         s4, gp, ra
                  c.addi      s4, -1
                  rem         zero, t5, s6
                  c.addi      s6, 1
                  c.add       s5, a4
                  sra         s5, s0, a2
                  c.li        t2, -1
                  slti        zero, gp, 1128
                  auipc       s10, 693217
                  ori         tp, s2, 1255
                  srai        t0, s7, 16
                  auipc       a2, 690097
                  mul         a2, t2, a6
                  c.slli      s8, 15
                  sra         s4, s11, s0
                  c.li        a5, -1
                  sll         t3, zero, s11
                  c.nop
                  c.li        s8, 14
                  c.li        s5, 26
                  sltiu       s7, sp, 251
                  addi        a5, s10, -1239
                  sltu        s11, s1, t0
                  slt         a6, t5, a3
                  xor         s4, a1, a7
                  c.andi      a3, 16
                  c.or        a3, a0
                  mul         t4, s9, a6
                  div         a6, s8, a7
                  auipc       t1, 875868
                  c.xor       s0, a2
                  c.srli      s1, 27
                  mulhu       s5, s9, a2
                  mul         sp, s5, sp
                  slli        s3, s9, 29
                  div         t1, s11, a1
                  ori         a7, s10, -1161
                  c.lui       s7, 22
                  divu        s3, s9, s7
                  c.li        t3, 0
                  and         s7, t2, s2
                  sll         a5, ra, a2
                  mul         s5, a2, t6
                  sltiu       a7, sp, 1275
                  c.nop
                  c.addi      s5, 23
                  mulh        tp, t6, ra
                  c.nop
                  add         a4, t6, s9
                  c.or        a3, a1
                  slt         t0, t5, t4
                  div         s4, zero, a5
                  addi        s9, s9, 436
                  c.sub       a3, a1
                  addi        s8, a5, 201
                  c.addi      ra, 30
                  slli        a7, a6, 2
                  ori         a5, s1, -1604
                  c.xor       s0, s1
                  mulhsu      zero, zero, t5
                  c.and       a3, a1
                  xori        t0, s6, -866
                  nop
                  andi        t3, t4, -1821
                  ori         s10, s11, 621
                  c.slli      s10, 14
                  or          s10, a3, s0
                  auipc       t1, 389593
                  c.li        s10, 28
                  lui         a6, 887124
                  mulhu       zero, s9, ra
                  addi        a3, t3, 250
                  c.addi16sp  sp, 384
                  and         s3, s6, t6
                  xori        s3, a4, 983
                  c.li        s6, -1
                  c.add       a3, a7
                  c.li        s8, 21
                  lui         s6, 49891
                  c.mv        s10, s9
                  c.or        a1, a0
                  sll         zero, s1, s1
                  c.srli      a1, 6
                  srl         a2, t2, gp
                  addi        ra, a4, -1770
                  c.and       s0, a0
                  c.addi4spn  s1, sp, 304
                  slt         gp, s9, ra
                  lui         zero, 602021
                  mulhu       zero, sp, a6
                  c.and       s1, s0
                  c.or        a3, a3
                  sll         a6, a5, a5
                  srli        s6, ra, 0
                  srl         a3, s0, ra
                  slt         a1, t0, tp
                  c.or        a3, a0
                  c.lui       tp, 31
                  addi        tp, t1, -387
                  slt         zero, s9, s5
                  c.addi4spn  a1, sp, 640
                  sltu        zero, a0, zero
                  c.mv        a3, s3
                  sll         t2, s1, a3
                  nop
                  c.nop
                  srli        s11, s3, 12
                  c.lui       s10, 5
                  and         t4, t6, sp
                  lui         s10, 224587
                  auipc       gp, 274124
                  div         t1, tp, a2
                  c.addi4spn  a2, sp, 720
                  divu        s7, a4, a5
                  c.nop
                  c.slli      s9, 10
                  c.srai      a1, 6
                  xor         t3, a2, t1
                  c.mv        s6, ra
                  ori         tp, a3, -1520
                  c.srai      s0, 3
                  sll         zero, a6, s7
                  and         gp, s5, s8
                  c.slli      s5, 22
                  sltiu       s0, a5, -1496
                  lui         s2, 536441
                  c.nop
                  lui         zero, 78110
                  srai        s4, a7, 18
                  c.xor       a3, a3
                  and         zero, s1, a7
                  slli        t4, s0, 11
                  auipc       a6, 237436
                  sltiu       tp, a2, -145
                  c.andi      a1, -1
                  srl         zero, s8, s2
                  andi        s1, a6, -1894
                  add         a2, ra, t0
                  xor         ra, t3, t0
                  lui         s4, 796464
                  sll         t2, t5, t2
                  c.sub       a1, a4
                  slt         a7, zero, s10
                  c.add       t0, tp
                  mulhu       sp, t1, s10
                  slli        zero, t2, 0
                  or          s5, t6, s1
                  sll         a4, tp, a5
                  c.nop
                  c.slli      a7, 1
                  addi        a5, a6, -509
                  divu        zero, a1, zero
                  srai        t1, a1, 24
                  sltiu       s4, zero, -42
                  sub         ra, s9, s7
                  c.nop
                  and         gp, s0, s6
                  xori        zero, s9, 945
                  mulh        t0, s9, tp
                  lui         s2, 752532
                  c.sub       a3, s1
                  rem         ra, t4, s1
                  slti        s11, gp, 1813
                  xori        zero, tp, -1221
                  mulh        t4, t0, s11
                  sra         tp, gp, t3
                  nop
                  c.mv        a1, s5
                  c.or        a3, a2
                  sub         s7, a0, gp
                  c.nop
                  or          a5, t2, s11
                  div         zero, s6, t0
                  c.addi      a5, 25
                  div         a1, a3, s11
                  c.add       a2, sp
                  c.addi      ra, 31
                  add         s3, s10, a7
                  xor         t2, s9, s0
                  sltiu       s0, s10, -2018
                  slt         t3, s5, zero
                  c.add       sp, ra
                  c.srai      a3, 5
                  c.add       tp, a1
                  lui         s0, 128772
                  c.mv        ra, ra
                  xor         s3, a4, s9
                  xor         a4, s9, s6
                  sltu        s4, s9, s6
                  xor         zero, t6, t1
                  slti        s5, s0, 1938
                  xori        gp, zero, 1019
                  mulhsu      s7, t1, a2
                  sltu        a2, a2, tp
                  mulh        zero, sp, a3
                  c.lui       s5, 16
                  c.and       a2, s1
                  addi        s6, s0, 1354
                  mulhsu      s9, ra, s8
                  add         t4, s0, s9
                  mul         gp, a7, s2
                  c.andi      a3, 25
                  mulhu       s8, t1, t5
                  c.addi4spn  a3, sp, 384
                  slli        s7, a5, 15
                  ori         ra, s2, 1295
                  c.sub       a4, a1
                  slt         zero, sp, s7
                  or          zero, t4, a6
                  srai        s5, s6, 15
                  auipc       zero, 720571
                  sra         s10, tp, s4
                  xori        s0, s7, 954
                  mulhsu      a2, gp, a2
                  xor         zero, t1, s9
                  c.andi      a3, 14
                  ori         t1, t3, -2002
                  c.lui       a5, 5
                  and         a1, t2, s9
                  and         a7, s6, s3
                  srai        s10, t2, 6
                  addi        s3, s3, -1038
                  slt         gp, s8, t3
                  divu        s7, t0, ra
                  c.lui       a5, 12
                  slli        zero, s6, 20
                  c.andi      s0, -1
                  c.addi16sp  sp, -16
                  c.srli      a3, 21
                  mulhu       s10, s1, a3
                  or          s10, s9, sp
                  c.mv        sp, t5
                  c.sub       a3, a3
                  c.addi16sp  sp, -16
                  c.addi4spn  a3, sp, 496
                  slli        a7, s5, 11
                  mulh        s9, t4, s10
                  c.addi4spn  a3, sp, 176
                  div         s5, s6, a2
                  c.addi      s1, 28
                  sltiu       a6, t0, -25
                  sltiu       s3, s1, 1063
                  c.or        a3, s1
                  c.and       a3, s1
                  sltiu       s2, a1, 1317
                  slli        s4, t6, 15
                  srl         s8, s11, s10
                  div         a6, t6, t0
                  rem         s7, t1, t2
                  c.srai      a3, 4
                  divu        t0, t6, tp
                  srai        s2, a7, 29
                  nop
                  xor         a5, tp, s7
                  c.sub       a4, a1
                  sra         s7, t0, sp
                  add         zero, a6, t4
                  and         s4, a3, s0
                  slt         s10, a0, tp
                  c.nop
                  sra         ra, s0, a2
                  c.addi      t0, -1
                  mulhu       s10, a7, s7
                  div         t3, s0, s2
                  slt         s10, t1, zero
                  mulh        s11, s6, t1
                  c.slli      s10, 28
                  c.andi      s0, 20
                  sub         gp, a2, gp
                  ori         gp, s5, 1778
                  c.nop
                  nop
                  slli        t1, t3, 27
                  c.addi16sp  sp, -16
                  c.and       a2, a1
                  or          s1, t1, s11
                  c.andi      a2, 17
                  lui         a5, 759060
                  and         a3, zero, s6
                  c.xor       a2, s0
                  rem         ra, s11, a3
                  mulhsu      a2, a2, t5
                  mulh        sp, sp, a1
                  c.srli      a3, 4
                  mul         sp, t6, t5
                  auipc       zero, 487658
                  sra         t4, t3, s1
                  andi        a7, a6, 1477
                  nop
                  mulhu       sp, ra, s11
                  c.sub       a2, a2
                  lui         a6, 791118
                  mul         t0, a1, s2
                  and         s6, s4, s11
                  sltu        t2, a0, s9
                  rem         t1, a0, a7
                  srl         s7, sp, a2
                  sra         t4, s4, s8
                  or          s7, sp, a5
                  mul         s4, s2, s0
                  slli        a1, s11, 16
                  c.lui       s3, 9
                  sll         sp, t3, a1
                  srl         t4, t0, gp
                  c.addi16sp  sp, 48
                  auipc       a5, 692374
                  sub         s2, a3, s8
                  c.addi      a7, 7
                  c.sub       a2, a2
                  sltiu       s11, zero, -1189
                  srl         gp, s1, s1
                  ori         s7, a6, 587
                  auipc       s5, 887645
                  ori         s3, t3, -1960
                  mul         sp, t6, gp
                  c.srli      a2, 18
                  slli        s4, a0, 21
                  ori         sp, a6, 1115
                  c.slli      t2, 24
                  lui         a6, 109648
                  c.addi      a2, 17
                  addi        s9, zero, 279
                  slti        s5, s4, 1266
                  sub         s11, sp, s8
                  c.addi16sp  sp, -16
                  c.srli      s0, 21
                  c.nop
                  divu        t1, s7, ra
                  divu        zero, s2, ra
                  sll         s3, s2, sp
                  srli        t4, s3, 29
                  and         gp, a2, tp
                  c.lui       s0, 11
                  nop
                  auipc       a6, 583280
                  c.srli      s1, 10
                  or          a6, s3, sp
                  xori        t0, a0, -263
                  c.addi      a3, 29
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_2
                  li         t3, 0x0
                  li         a4, 0x0
                  li         a5, 0x0
                  li         s0, 0x0
                  li         a2, 0x0
                  li         a3, 0x6d04e14a
                  li         s8, 0x1
                  li         s10, 0x1
                  li         s9, 0x235cfe82
                  c.addi4spn  a2, sp, 960
                  lui         s10, 668866
                  c.addi4spn  a3, sp, 752
                  c.li        a3, 6
                  c.addi      ra, 4
                  c.lui       s11, 26
                  div         s6, s4, s5
                  c.li        s6, 30
                  add         zero, tp, t2
                  addi        s9, s5, 1636
                  c.li        s6, 13
                  c.lui       t3, 8
                  lui         t2, 447094
                  c.addi      s6, 21
                  mul         a6, s6, t2
                  c.sub       s1, a0
                  srl         zero, s7, tp
                  add         t3, t6, a5
                  slti        s9, zero, 383
                  sltiu       a2, s9, -1893
                  c.mv        t2, a7
                  c.lui       a4, 1
                  mulhu       a5, s1, s5
                  c.lui       s7, 17
                  xor         s10, a2, s2
                  sub         zero, s11, t6
                  c.addi16sp  sp, -16
                  auipc       s10, 83810
                  c.srli      s1, 1
                  divu        s5, s0, a5
                  c.andi      a3, -1
                  add         t3, s1, zero
                  c.slli      t1, 3
                  c.add       s2, a5
                  mul         s3, t0, s2
                  mul         s11, s9, s7
                  mulhu       s8, s1, sp
                  c.nop
                  c.addi4spn  a1, sp, 736
                  rem         s8, s7, a6
                  c.addi      t1, 30
                  c.lui       ra, 28
                  c.add       s5, ra
                  c.sub       a4, a2
                  and         s8, t6, s9
                  div         a5, s8, zero
                  xor         tp, s3, s8
                  c.sub       a3, a0
                  mulh        s9, s11, s6
                  andi        s11, s1, 1699
                  slt         a4, s9, gp
                  divu        a1, a6, s5
                  andi        zero, zero, -1155
                  c.and       a3, a2
                  c.xor       a2, a3
                  or          a1, a3, a7
                  c.or        s0, a3
                  or          a5, gp, a7
                  c.addi      t1, 20
                  auipc       s2, 75399
                  mul         t4, s10, a0
                  auipc       s9, 284465
                  c.andi      s1, 2
                  c.or        a2, s1
                  c.lui       s9, 29
                  div         t1, gp, a6
                  c.add       s4, s3
                  sra         zero, t6, s4
                  slti        ra, a2, -1221
                  c.or        a2, a3
                  sll         zero, s3, t2
                  addi        a5, a6, -102
                  sub         s5, a0, a0
                  c.nop
                  srl         s1, s5, s8
                  sltu        a2, s2, tp
                  addi        a2, t1, -672
                  slti        a6, s2, -1529
                  srai        s9, s10, 12
                  c.nop
                  or          zero, s9, t0
                  c.addi16sp  sp, -16
                  c.li        s2, -1
                  lui         a6, 598166
                  sltu        zero, s3, s4
                  c.addi4spn  a4, sp, 16
                  sltu        zero, s11, t4
                  mulhu       s9, s10, s8
                  c.srai      s0, 1
                  c.addi      s8, -1
                  divu        zero, s3, zero
                  srl         s4, s10, s4
                  lui         zero, 540792
                  c.add       ra, s0
                  sltu        sp, ra, zero
                  sltu        gp, s11, t3
                  srl         sp, a2, s1
                  auipc       a7, 593269
                  sub         s3, a5, t1
                  addi        a6, sp, -872
                  c.xor       a1, a1
                  mulhu       a4, s5, s2
                  andi        tp, s4, -782
                  c.li        a1, 25
                  srl         t3, zero, t3
                  c.addi16sp  sp, 496
                  c.slli      s10, 4
                  sll         a7, a6, gp
                  c.addi      t0, 23
                  rem         s6, t3, a1
                  sltiu       a3, s3, -1719
                  add         sp, a7, ra
                  sltiu       zero, s5, 1669
                  c.addi      ra, -1
                  mulh        s2, zero, a5
                  lui         s4, 218779
                  mulhu       t3, a0, s7
                  lui         a6, 486986
                  mulhsu      s7, s6, t3
                  c.li        sp, -1
                  mulhu       a3, s9, s6
                  c.xor       a5, a2
                  nop
                  add         a3, t2, s1
                  lui         s8, 241359
                  c.srli      a2, 27
                  c.addi16sp  sp, -16
                  andi        a2, t3, -113
                  sll         s6, a4, a6
                  rem         ra, a0, a5
                  sub         gp, s3, t1
                  mulhu       a6, ra, a4
                  andi        s0, a6, -2027
                  c.and       a1, a4
                  c.add       a1, ra
                  mulh        a2, s3, a1
                  sub         s11, t2, s4
                  ori         t1, a5, -1251
                  addi        zero, s10, -422
                  c.sub       s1, a2
                  lui         s4, 72104
                  add         t3, s9, t3
                  divu        sp, gp, a6
                  c.srai      a2, 17
                  c.or        s1, a2
                  andi        a7, a4, 1280
                  srli        s4, s2, 25
                  c.or        a1, a0
                  slt         s10, t4, t1
                  auipc       t4, 20708
                  lui         t2, 719728
                  rem         zero, s10, s11
                  nop
                  c.or        a3, a1
                  divu        a7, t1, a0
                  c.slli      s7, 3
                  or          s9, a4, s5
                  c.or        a5, a3
                  c.sub       s1, a1
                  slli        s3, s2, 3
                  c.sub       a3, a0
                  srl         s3, a1, t5
                  div         t3, s5, a0
                  slti        s11, s2, -1996
                  c.andi      a1, -1
                  c.addi      sp, 5
                  and         gp, s2, ra
                  mulhu       s8, zero, a1
                  c.addi      a3, 28
                  c.srli      s0, 15
                  mul         t1, a3, ra
                  xor         s2, gp, s1
                  c.and       a2, a1
                  sltiu       a6, a7, -120
                  nop
                  sub         t3, t5, t1
                  slti        s4, a2, 405
                  addi        t4, a7, -1727
                  c.addi4spn  a4, sp, 592
                  c.nop
                  c.slli      t4, 16
                  lui         zero, 963503
                  c.sub       a1, a2
                  mulh        zero, s1, s10
                  c.andi      a1, -1
                  divu        zero, t3, s0
                  c.addi16sp  sp, -16
                  c.addi16sp  sp, 336
                  c.andi      a3, -1
                  c.and       a5, a0
                  div         a1, t2, s5
                  c.addi4spn  a3, sp, 752
                  c.srai      s1, 18
                  addi        s11, gp, 1555
                  c.addi4spn  a2, sp, 640
                  div         s10, a4, t3
                  c.andi      a2, -1
                  sltiu       gp, t6, -1200
                  c.slli      s3, 17
                  c.or        s0, a0
                  srai        zero, gp, 26
                  or          a2, a1, a7
                  srai        s8, s7, 8
                  auipc       a4, 396777
                  c.srai      s1, 15
                  or          tp, s1, t0
                  mulh        t3, s10, t2
                  slt         s5, gp, s8
                  c.slli      t0, 7
                  c.xor       a2, a1
                  or          s1, s10, t4
                  nop
                  nop
                  c.andi      a3, -1
                  sltiu       zero, t3, -1965
                  sub         s11, s4, s3
                  c.andi      a1, 28
                  add         s7, s2, ra
                  sltu        gp, a6, s10
                  c.nop
                  c.addi16sp  sp, 96
                  c.addi16sp  sp, -16
                  sub         s6, s2, s11
                  c.andi      a2, -1
                  sltiu       a2, s1, 1161
                  div         s1, s9, t0
                  srai        s0, zero, 14
                  srl         s5, s11, s7
                  rem         s10, zero, s4
                  lui         s4, 662312
                  srli        zero, s8, 30
                  addi        s11, s10, 855
                  addi        t4, s4, 1725
                  c.li        s9, 6
                  c.nop
                  mul         t4, t6, a4
                  mulh        gp, t1, t5
                  addi        sp, s6, -867
                  c.add       s9, a3
                  c.srli      a2, 4
                  c.addi16sp  sp, -16
                  lui         a5, 938437
                  slti        t3, s1, -361
                  c.mv        t0, s9
                  sltiu       a5, t6, 1168
                  c.addi      t2, 5
                  c.addi16sp  sp, 176
                  slli        s4, s7, 28
                  c.addi4spn  a1, sp, 624
                  divu        a1, s6, s4
                  mulhsu      s3, a5, s10
                  srai        zero, a3, 9
                  slti        s0, s10, 1523
                  add         s9, a7, t0
                  divu        t0, s11, s10
                  c.slli      t4, 26
                  xor         zero, t2, a5
                  srli        t4, s10, 24
                  addi        t4, s8, -984
                  c.li        s8, 10
                  c.and       a3, a3
                  and         t3, t0, s4
                  c.mv        s8, a5
                  or          zero, s2, ra
                  srl         s5, a3, t3
                  sra         s10, a3, a0
                  divu        tp, s2, s1
                  c.xor       a3, a1
                  rem         ra, t0, t6
                  sll         a3, s2, t4
                  slti        t0, s3, 704
                  mul         t3, s5, t1
                  slti        gp, tp, 321
                  c.addi4spn  a3, sp, 672
                  c.addi      ra, 22
                  srl         s2, t2, s1
                  xori        zero, s5, -815
                  mulhsu      zero, s2, a4
                  srai        s4, a4, 2
                  mulh        s6, a6, t1
                  and         s6, t6, sp
                  xor         zero, t0, s0
                  srai        tp, zero, 29
                  mulhsu      a7, t1, t6
                  andi        s11, t1, 1094
                  sltu        s9, t6, s0
                  nop
                  mulhsu      s9, tp, s7
                  and         tp, t6, zero
                  c.mv        ra, s1
                  c.xor       a2, a1
                  xori        a1, a7, -573
                  c.mv        t3, s0
                  sub         s5, s4, s10
                  ori         a7, s4, -1485
                  addi        s4, s9, -840
                  c.srli      s1, 11
                  mulh        s0, a6, a2
                  sub         zero, s5, t5
                  c.slli      gp, 1
                  andi        t1, s2, 724
                  or          s7, a3, t0
                  ori         s10, t4, -491
                  mulh        s7, s5, s2
                  c.and       s1, a2
                  c.andi      a3, -1
                  addi        s6, t3, -1308
                  sltiu       t1, t3, 975
                  auipc       s11, 859864
                  srl         zero, s3, s6
                  c.nop
                  sub         s5, sp, s1
                  mulhsu      ra, tp, t5
                  c.srai      a3, 5
                  xori        a5, s0, 2034
                  c.addi      ra, -1
                  auipc       a4, 408180
                  c.mv        ra, a3
                  mulhsu      zero, a7, t0
                  andi        s8, t1, -36
                  slli        s4, a0, 17
                  c.addi4spn  a2, sp, 112
                  c.or        a3, a0
                  rem         t4, a6, a1
                  c.nop
                  or          gp, a2, gp
                  or          a5, t4, tp
                  mulhu       s1, s9, s8
                  mulh        s4, s11, zero
                  c.srli      a3, 15
                  c.addi4spn  a3, sp, 752
                  c.and       a2, a2
                  c.mv        t2, s5
                  srli        zero, a1, 8
                  slt         a4, a6, tp
                  srli        t3, t2, 26
                  rem         s10, a4, s2
                  mulh        s2, sp, t4
                  c.and       a3, a0
                  divu        s10, s2, t6
                  c.add       gp, s2
                  div         a6, s4, gp
                  c.slli      a6, 8
                  c.or        a3, a2
                  andi        s11, a4, 481
                  xori        a7, tp, -512
                  slli        a4, s9, 17
                  c.nop
                  sltu        a5, s8, s10
                  c.xor       a3, a1
                  andi        s9, tp, 599
                  slt         s6, gp, a1
                  c.or        a3, s1
                  auipc       s9, 970189
                  c.and       s0, a2
                  c.or        a2, a0
                  c.li        s7, -1
                  div         a7, a1, t1
                  andi        s2, s6, -1674
                  c.addi16sp  sp, 64
                  srl         s4, s1, ra
                  lui         s1, 690165
                  andi        a5, t5, 1211
                  rem         s1, ra, s8
                  c.sub       a3, s0
                  auipc       tp, 712386
                  c.nop
                  and         s3, t5, t3
                  c.slli      ra, 18
                  c.li        s4, 27
                  slli        t1, s9, 30
                  sub         s5, t2, t3
                  c.or        s1, s1
                  sub         a2, s1, ra
                  xor         t0, s2, sp
                  sll         a1, ra, t5
                  c.andi      s0, -1
                  slt         a2, t2, s4
                  divu        a5, a6, s10
                  c.mv        s1, s5
                  divu        s5, s4, s5
                  srai        s1, gp, 9
                  c.lui       t1, 28
                  c.slli      s9, 7
                  auipc       s7, 70016
                  sll         zero, a4, a2
                  addi        a5, t5, 1167
                  auipc       s11, 769349
                  srl         s4, t5, t4
                  c.mv        s7, gp
                  or          tp, s3, s9
                  add         ra, t3, t5
                  sll         s2, a0, a3
                  mulhu       a5, s11, tp
                  c.xor       s1, a0
                  c.addi16sp  sp, -16
                  nop
                  mulhsu      t4, s10, a7
                  sll         s1, s9, t5
                  c.or        a3, a1
                  and         s8, s8, ra
                  lui         zero, 550653
                  and         t2, t3, sp
                  or          t3, t6, s1
                  slt         s4, s2, a5
                  add         t1, s9, a1
                  srl         s7, t4, s0
                  srli        zero, s6, 15
                  srl         a2, ra, t0
                  srli        gp, s7, 28
                  addi        s1, t4, 769
                  andi        ra, s4, 1708
                  or          s10, gp, a1
                  sltu        s5, s7, t4
                  lui         t3, 671169
                  sltu        t3, t4, s9
                  ori         t3, s1, 729
                  c.and       a3, a2
                  mulh        t3, sp, s5
                  sra         zero, a1, s8
                  div         zero, t2, t1
                  srai        gp, s1, 14
                  sra         zero, a3, s5
                  c.add       ra, s2
                  c.srai      a2, 4
                  auipc       zero, 721334
                  addi        s1, a7, 1578
                  mul         a3, s4, s2
                  slti        a5, sp, -298
                  srl         s0, ra, s5
                  srl         s7, s2, s5
                  lui         tp, 64984
                  c.srai      a1, 2
                  slti        s10, a1, 1929
                  c.srli      a2, 18
                  c.addi      t2, -1
                  andi        s1, a4, 886
                  c.srli      a3, 10
                  mulhu       a1, s9, s10
                  sra         s3, a1, t3
                  sub         a6, ra, t6
                  c.sub       a3, a4
                  nop
                  slli        zero, t1, 12
                  sra         s4, a5, s8
                  c.add       s10, t3
                  sltiu       t4, a0, -1692
                  andi        a2, tp, 164
                  c.addi4spn  a3, sp, 432
                  c.andi      a2, -1
                  rem         zero, a5, t5
                  ori         s5, a2, -1638
                  c.mv        s3, sp
                  c.addi4spn  s1, sp, 192
                  mulhu       t0, gp, t1
                  c.or        a2, s1
                  sltu        s10, gp, s8
                  div         a1, a1, sp
                  srai        a5, s7, 13
                  sll         s9, t0, t6
                  c.mv        ra, t2
                  c.addi      a3, -1
                  c.li        t0, -1
                  c.and       a3, a3
                  c.srli      a4, 13
                  and         zero, a4, t6
                  add         zero, s9, s4
                  mulh        tp, t5, a1
                  c.xor       s1, a2
                  rem         s0, a1, t3
                  mul         s9, t5, t3
                  sra         s7, a0, ra
                  andi        t0, ra, 1996
                  srai        s5, t3, 15
                  auipc       s7, 182041
                  c.sub       a2, a5
                  auipc       s10, 649136
                  c.nop
                  srai        tp, t4, 14
                  and         zero, s0, s1
                  slt         t3, t6, s9
                  slti        a3, a2, -660
                  xor         a3, t3, sp
                  or          s8, a5, a1
                  c.slli      s7, 16
                  slt         a6, s3, a0
                  sll         ra, a5, s3
                  srl         t2, t5, t3
                  mulhsu      zero, s9, s2
                  auipc       s6, 377226
                  li         s7, 0x1 #start riscv_int_numeric_corner_stream_0
                  li         t4, 0x0
                  li         t3, 0x613fe887
                  li         a4, 0x1a27f691
                  li         s11, 0x1
                  li         a6, 0x30693b5a
                  li         s8, 0x0
                  li         a1, 0x0
                  li         s10, 0x0
                  li         s3, 0x0
                  sub         t2, s4, tp
                  mulh        s9, a3, t0
                  c.sub       a5, a0
                  nop
                  nop
                  c.li        tp, 5
                  c.lui       gp, 26
                  c.addi      s4, -1
                  mulh        a1, a0, s1
                  rem         a1, a0, gp
                  mul         t3, t2, a3
                  divu        zero, a3, gp
                  mulhsu      s9, ra, a7
                  c.sub       a1, a2
                  mul         zero, s2, s8
                  c.addi16sp  sp, -16
                  c.addi4spn  a2, sp, 384
                  add         zero, sp, gp
                  c.nop
                  addi        a6, s10, 504
                  mulhu       s10, s4, s6
                  divu        t1, s6, t5
                  c.addi      tp, 26
                  lui         s0, 1027469
                  addi        tp, a0, 111
                  c.add       a5, a5
                  srl         s0, a6, t6
                  mulh        s3, a5, a7
                  c.nop
                  sll         sp, s9, s7
                  ori         a7, a6, 261
                  c.andi      a3, -1
                  mulh        s0, s6, s1
                  div         t3, ra, t1
                  c.lui       a3, 17
                  andi        tp, t2, -1510
                  srai        s7, s2, 0
                  c.srai      a2, 15
                  sra         sp, tp, s10
                  add         tp, zero, a6
                  c.mv        t2, s6
                  lui         t3, 859998
                  add         s9, s1, gp
                  sub         s6, s0, gp
                  addi        s6, s11, -334
                  divu        s11, a2, a0
                  c.andi      a1, -1
                  c.mv        gp, t1
                  srai        t0, s8, 28
                  and         s11, s10, t1
                  c.add       ra, t1
                  c.mv        a6, a7
                  slt         s3, zero, a5
                  c.srai      a3, 7
                  divu        gp, s5, s6
                  c.addi4spn  a2, sp, 528
                  and         s9, a0, tp
                  andi        t1, t5, 1536
                  mulh        s6, t3, s1
                  c.andi      a3, 26
                  sltu        a5, tp, a6
                  c.add       ra, s4
                  divu        sp, s6, s2
                  c.mv        a4, a6
                  slt         zero, ra, t1
                  c.lui       s7, 22
                  lui         a7, 306457
                  c.nop
                  slt         t1, a5, zero
                  div         ra, t4, s4
                  c.addi      t2, -1
                  andi        a3, s7, 1554
                  or          s6, a4, tp
                  ori         a5, s0, 1505
                  slti        s1, tp, -912
                  addi        s7, a6, -1090
                  c.addi      ra, -1
                  c.andi      a3, 24
                  andi        zero, t4, 1552
                  add         s4, t5, s11
                  c.srli      a4, 10
                  andi        zero, zero, -1854
                  slt         s3, t6, s1
                  ori         s4, t2, 1204
                  mulhu       ra, a4, a1
                  slt         t1, a7, t5
                  c.add       s5, s1
                  xor         s1, s9, s8
                  andi        s8, zero, 1643
                  slti        tp, s11, 792
                  xori        s5, sp, 1711
                  mulh        zero, t4, t6
                  slt         s2, s7, s10
                  c.addi      sp, 18
                  rem         s7, s6, gp
                  c.srai      a2, 8
                  ori         s6, t2, 1021
                  c.srli      s0, 14
                  sra         t0, t5, sp
                  srli        zero, t0, 26
                  c.andi      a2, -1
                  c.srai      a3, 28
                  c.andi      a3, -1
                  sub         s0, s1, a5
                  and         s11, s9, s1
                  c.xor       a2, a2
                  or          a5, s1, s7
                  c.lui       a1, 28
                  slti        s7, gp, -1957
                  c.or        s1, a3
                  xor         s7, tp, zero
                  c.add       tp, t0
                  slti        tp, a6, 1190
                  lui         gp, 829206
                  c.andi      s0, -1
                  sltiu       t1, a2, 522
                  c.add       s4, s4
                  c.slli      ra, 17
                  c.lui       ra, 14
                  ori         s6, a0, 239
                  c.add       a6, s9
                  ori         s6, s7, 530
                  xor         tp, s10, t5
                  mulhsu      s10, t3, a2
                  addi        a2, s11, 605
                  c.nop
                  srl         s7, s2, t3
                  mulhsu      s8, s5, a7
                  mulhsu      t4, ra, s3
                  sll         tp, s6, a6
                  lui         a4, 778622
                  auipc       s11, 454002
                  sltiu       a2, t5, -931
                  xor         a2, t3, s3
                  c.lui       t0, 15
                  c.xor       s0, a0
                  c.lui       s11, 1
                  c.addi16sp  sp, -16
                  sub         sp, s3, s3
                  slt         s1, s4, s3
                  mulh        t2, a2, tp
                  c.nop
                  sub         s0, s7, a4
                  nop
                  slti        s1, a5, 1415
                  divu        zero, a5, s7
                  sra         a4, a6, a2
                  and         tp, sp, tp
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_7
                  li         t3, 0xac99581
                  li         s11, 0x70540e0d
                  li         s10, 0x1
                  li         a4, 0x1
                  li         sp, 0x1
                  li         s3, 0x1
                  li         s1, 0x0
                  li         s2, 0x208fbd0d
                  li         a1, 0x1
                  c.add       t2, sp
                  c.mv        ra, s7
                  lui         t2, 489014
                  divu        a6, s5, t1
                  c.addi4spn  s1, sp, 784
                  div         zero, s1, a7
                  c.mv        ra, t4
                  div         zero, t6, s8
                  divu        sp, s7, a0
                  mul         gp, t5, s8
                  div         tp, t4, s5
                  sub         s11, s5, s3
                  sub         t3, a5, t0
                  c.li        t0, 1
                  mulhsu      s6, a5, s10
                  rem         a1, t2, s2
                  c.addi      a6, -1
                  mulhu       zero, s0, s5
                  div         s8, s1, s2 #end riscv_int_numeric_corner_stream_7
                  srli        s9, a1, 18
                  c.lui       s3, 12
                  auipc       a1, 814037
                  srli        s11, sp, 14
                  c.lui       ra, 3
                  divu        sp, tp, a6
                  mulhu       s10, a1, t0
                  c.mv        a1, s8
                  c.li        a7, 19
                  slli        s6, a6, 25
                  c.add       ra, t6
                  c.addi4spn  a3, sp, 16
                  srl         s3, t3, a7
                  c.srli      a3, 31
                  c.mv        a3, s6
                  sub         t1, s9, t3
                  sub         s3, a7, s9
                  c.srai      a3, 1
                  auipc       s3, 975130
                  c.lui       s4, 28
                  c.andi      s1, 24
                  mulhsu      zero, s8, a5
                  divu        s11, a6, s10
                  c.mv        t0, a2
                  addi        s6, s1, -1407
                  c.slli      ra, 22
                  c.li        s11, -1
                  srli        t3, s7, 18
                  c.andi      s0, -1
                  xori        s3, tp, -848
                  nop
                  auipc       t0, 64227
                  c.lui       s3, 13
                  sll         s6, t4, t5
                  addi        t4, a3, 1723
                  c.addi      s8, -1
                  mulh        s8, s11, a2
                  xori        s4, zero, -627
                  sltu        zero, s11, a3
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_9
                  li         t3, 0x778d48d4
                  li         s4, 0x1f68549b
                  li         s11, 0x3403ad7a
                  li         s10, 0x0
                  li         s5, 0x2fa5b177
                  li         t2, 0x0
                  li         s7, 0x0
                  li         a1, 0x23280e63
                  li         s2, 0x5e0c56e0
                  sub         s4, zero, ra
                  nop
                  addi        s3, s9, 862
                  c.addi      s9, 9
                  auipc       s7, 596783
                  addi        s10, s9, 1414
                  mulhu       s3, s10, a1
                  c.nop
                  addi        t4, s6, 817
                  lui         s9, 910240
                  add         a4, s7, t1
                  divu        zero, s0, s0
                  c.addi      s2, -1
                  c.nop
                  c.addi4spn  s1, sp, 624
                  divu        s8, s2, t6
                  c.mv        ra, a6
                  div         a3, t4, s9
                  mulhsu      t1, a1, s8
                  c.addi4spn  a2, sp, 976
                  c.mv        s11, a3
                  add         a1, t5, s3
                  c.lui       s0, 1
                  c.sub       a1, a0
                  add         s1, s4, s2
                  c.addi      a4, -1
                  srl         s7, a0, s0
                  divu        t0, s4, a4
                  mulhsu      t0, t3, t4
                  mulhsu      a4, s2, s9
                  div         s10, a2, zero
                  rem         s1, t0, tp
                  xor         t0, s9, s8
                  addi        sp, s5, -1074
                  sra         s2, tp, t3
                  divu        s0, tp, gp
                  slti        s11, a5, -1363
                  or          s5, t5, gp
                  and         s0, s6, t6
                  mulhu       zero, a2, s9
                  add         s10, s6, t3
                  sltu        a7, a1, a6
                  slti        s0, t4, -1354
                  slli        a4, t1, 6
                  mul         t3, t0, a7
                  or          s3, t2, a3
                  lui         ra, 724027
                  xor         a7, s3, a1
                  c.or        a2, a3
                  slt         s10, t5, zero
                  c.li        a7, 25
                  c.nop
                  c.andi      s1, -1
                  srai        tp, t4, 22
                  c.and       a2, a3
                  c.srli      a1, 2
                  and         a4, s1, a4
                  c.mv        a7, t3
                  sll         a4, a1, gp
                  c.addi4spn  a3, sp, 880
                  lui         s9, 153306
                  slt         a1, s2, sp
                  c.sub       a2, s1
                  slt         sp, t5, gp
                  c.addi4spn  s1, sp, 320
                  sll         sp, tp, s0
                  c.mv        t4, a2
                  mul         t1, a1, a2
                  divu        s11, s4, a4
                  nop
                  c.add       sp, a2
                  sltiu       s8, s9, -1982
                  c.xor       s0, s1
                  mulhu       s9, ra, s1
                  rem         s9, zero, s9
                  sltu        s10, t6, s4
                  addi        gp, t4, -462
                  add         s11, s8, s4
                  mul         s9, s6, t4
                  mulh        t2, s6, s11
                  lui         s9, 471807
                  divu        zero, s9, t0
                  sltu        sp, t3, s1
                  c.srli      a3, 5
                  andi        zero, a5, -2008
                  c.srli      a1, 6
                  c.lui       ra, 18
                  c.lui       s11, 24
                  slli        a1, s9, 3
                  xor         a6, s3, s5
                  c.sub       a3, a2
                  xor         a3, s10, t4
                  andi        zero, ra, 1810
                  c.mv        s2, tp
                  c.and       s1, a1
                  andi        s9, s9, 855
                  c.li        gp, -1
                  c.srai      a3, 7
                  ori         s6, a5, -75
                  slli        zero, s8, 3
                  srl         ra, s11, a4
                  sltiu       t0, s11, -434
                  sltiu       s1, t2, 209
                  c.srli      a2, 21
                  c.lui       gp, 27
                  andi        zero, a6, -1410
                  div         s11, t5, s1
                  rem         a5, t3, a5
                  c.xor       s0, a1
                  srli        s6, a5, 19
                  c.srli      s1, 24
                  c.add       a5, s0
                  sltu        zero, s6, t2
                  add         t2, a0, gp
                  c.addi4spn  a3, sp, 592
                  auipc       s1, 194094
                  div         sp, t2, s2
                  andi        a3, s5, 76
                  c.xor       s1, a1
                  c.sub       a3, a2
                  mul         ra, s1, zero
                  c.add       a4, s6
                  auipc       a4, 588040
                  c.addi4spn  a1, sp, 656
                  c.li        s9, 14
                  srl         ra, zero, a2
                  xori        t0, t5, -952
                  c.add       a5, s1
                  sra         ra, t4, ra
                  c.or        a2, a3
                  sra         t2, a3, t2
                  c.addi4spn  s0, sp, 544
                  c.li        ra, 20
                  mulhsu      s10, sp, a2
                  andi        sp, s6, 1909
                  add         zero, t6, a7
                  c.add       s4, s10
                  slt         gp, a0, a6
                  and         zero, s8, t6
                  c.andi      a2, 30
                  slt         t4, s7, a1
                  ori         s5, s8, -1909
                  auipc       s2, 34368
                  divu        t3, s8, a3
                  mul         zero, s5, s0
                  divu        s10, t6, s1
                  andi        a6, ra, -548
                  and         a2, a2, s3
                  c.xor       a1, a0
                  c.addi      s6, 28
                  c.addi16sp  sp, -16
                  c.nop
                  lui         s0, 887693
                  c.addi16sp  sp, -16
                  ori         a5, t0, 443
                  c.slli      s1, 16
                  c.nop
                  ori         s3, t1, 1678
                  andi        t1, s3, 598
                  xor         tp, s0, a6
                  c.lui       s9, 26
                  srai        s11, s7, 12
                  sltiu       s10, a2, 1360
                  srl         s0, s3, s11
                  slti        zero, s9, -1024
                  c.addi      a5, -1
                  c.xor       a2, a5
                  mulhsu      a1, a7, t0
                  c.addi16sp  sp, -16
                  ori         a5, a5, -1486
                  c.addi16sp  sp, 336
                  slli        s10, a5, 3
                  c.or        a3, a2
                  addi        a7, t3, -1154
                  c.or        s0, s0
                  andi        zero, zero, -288
                  sltiu       zero, a1, 16
                  c.li        a4, -1
                  c.addi16sp  sp, 480
                  sltu        tp, s6, a4
                  auipc       a2, 848803
                  xor         t1, t2, a1
                  mulh        t1, ra, zero
                  and         s1, s2, s7
                  c.addi      ra, 5
                  sltiu       s2, t4, 553
                  sltu        t4, s0, s3
                  c.add       gp, ra
                  c.addi4spn  a2, sp, 432
                  addi        zero, a0, -1679
                  c.xor       a1, a1
                  c.mv        s4, tp
                  c.xor       s1, s1
                  add         a5, gp, a0
                  mulhsu      t1, s4, a2
                  c.mv        t0, t1
                  c.mv        s10, s8
                  div         s4, t2, s2
                  sll         a5, a1, a0
                  rem         a3, t3, s10
                  mul         s4, t1, a6
                  srl         a5, a1, gp
                  c.addi4spn  a3, sp, 112
                  srl         ra, t2, t0
                  c.xor       a2, s0
                  c.addi16sp  sp, 192
                  slti        zero, a7, -911
                  c.addi      a6, 22
                  sltu        s6, gp, s1
                  c.andi      a2, 21
                  srli        s9, t6, 8
                  sltiu       s8, s7, 465
                  mulh        s9, gp, s3
                  andi        t4, s3, -434
                  c.srai      a1, 12
                  c.sub       a3, a2
                  sra         s8, t1, t0
                  c.addi      s2, 16
                  c.lui       tp, 4
                  c.xor       a5, a2
                  c.add       ra, t3
                  mulhsu      a4, a0, t2
                  add         zero, a0, t4
                  c.addi16sp  sp, 336
                  and         a2, s7, sp
                  divu        gp, s10, a3
                  c.lui       s2, 20
                  nop
                  slti        t4, s2, -1123
                  mulhu       a2, s11, s0
                  sub         s2, s6, a2
                  andi        a2, tp, 860
                  sra         sp, a6, s7
                  mulhu       s9, a5, t5
                  nop
                  div         s8, t4, s5
                  c.slli      s11, 6
                  divu        t2, t3, t4
                  add         a2, s2, s4
                  srli        s5, zero, 3
                  add         s0, a6, a4
                  c.addi      ra, 13
                  sll         a2, s7, a0
                  c.xor       a2, a1
                  and         s8, s8, s2
                  sltiu       a6, s9, -1213
                  sltiu       a4, t6, 1932
                  sub         s4, s11, a6
                  c.addi      s0, 6
                  srl         t4, s9, t3
                  c.srli      a3, 5
                  srai        a1, s11, 25
                  c.addi      s9, -1
                  c.and       s1, s0
                  srai        a7, a2, 23
                  c.srli      a3, 14
                  c.nop
                  c.addi      ra, -1
                  srli        zero, s2, 20
                  c.or        a3, a2
                  c.and       a3, a1
                  div         s4, s5, a3
                  c.srai      a1, 14
                  c.and       a1, a2
                  xor         s3, s9, s10
                  sub         a7, a6, s3
                  andi        zero, s5, -1034
                  mulhu       zero, t6, a2
                  xor         zero, ra, s1
                  c.or        s0, a1
                  srai        zero, gp, 7
                  slt         sp, t6, a4
                  c.addi      a3, -1
                  c.slli      s9, 19
                  and         a4, t5, t5
                  rem         zero, a3, a4
                  c.sub       a3, a1
                  mulhu       s0, s8, s1
                  srli        s7, t2, 0
                  c.addi16sp  sp, 352
                  nop
                  c.li        ra, 24
                  sltu        sp, s10, s7
                  auipc       a7, 30318
                  srl         s5, a1, tp
                  divu        t0, s6, sp
                  c.sub       a4, a0
                  xori        t4, s2, 799
                  c.addi16sp  sp, 448
                  c.nop
                  sra         a7, sp, t5
                  c.addi      s10, -1
                  c.nop
                  mulhsu      s9, gp, t2
                  slt         s6, zero, a6
                  sll         tp, t2, tp
                  c.li        s4, -1
                  c.li        a4, 3
                  c.xor       s0, a2
                  c.srai      s1, 12
                  c.nop
                  c.nop
                  or          ra, a5, s11
                  sub         s0, t3, t2
                  mulh        s4, s1, t5
                  mulhsu      zero, ra, t1
                  c.addi16sp  sp, 432
                  c.mv        ra, s5
                  c.or        a1, a1
                  add         a5, s0, zero
                  c.add       tp, sp
                  sll         a7, s2, tp
                  c.or        a2, a2
                  c.lui       s6, 5
                  sltu        t2, t5, s10
                  auipc       a7, 709811
                  or          zero, t5, s10
                  sll         zero, a2, a2
                  xor         t1, t5, ra
                  sub         gp, t5, a0
                  mul         s3, a6, a7
                  slli        a5, t6, 25
                  c.lui       t1, 13
                  c.srli      s0, 14
                  mulhsu      s3, a7, s9
                  xori        a6, a1, -535
                  c.addi4spn  s0, sp, 640
                  mulhsu      t3, t4, t0
                  c.lui       s3, 15
                  slli        gp, gp, 27
                  mulhu       s9, a1, a2
                  mulhu       zero, t0, t6
                  lui         t1, 165154
                  lui         a6, 561682
                  c.sub       a4, s1
                  c.srai      a1, 3
                  c.srai      a3, 11
                  slli        a1, s9, 5
                  c.lui       a7, 27
                  c.srai      s0, 28
                  c.mv        t4, s1
                  c.li        t4, 8
                  c.lui       a2, 31
                  sll         s10, a3, s10
                  sltiu       a5, s5, -1696
                  c.slli      ra, 15
                  c.andi      s1, 27
                  mul         s7, s5, sp
                  c.sub       a3, a2
                  c.andi      s1, -1
                  la x31, test_done
                  jalr x0, x31, 0
test_done:        
                  li gp, 1
                  ecall
write_tohost:     
                  sw gp, tohost, t5

_exit:            
                  j write_tohost

instr_end:        
                  nop

.section .data
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
.section .user_stack,"aw",@progbits;
.align 2
user_stack_start:
.rept 4999
.4byte 0x0
.endr
user_stack_end:
.4byte 0x0
.align 2
kernel_instr_start:
.text
mmode_intr_vector_1:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_2:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_3:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_4:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_5:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_6:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_7:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_8:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_9:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_10:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_11:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_12:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_13:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_14:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_15:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x342 # MCAUSE
                  srli x6, x6, 0x1f
                  beqz x6, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

.align 4
mtvec_handler:    
                  .option norvc;
                  j mmode_exception_handler
                  j mmode_intr_vector_1
                  j mmode_intr_vector_2
                  j mmode_intr_vector_3
                  j mmode_intr_vector_4
                  j mmode_intr_vector_5
                  j mmode_intr_vector_6
                  j mmode_intr_vector_7
                  j mmode_intr_vector_8
                  j mmode_intr_vector_9
                  j mmode_intr_vector_10
                  j mmode_intr_vector_11
                  j mmode_intr_vector_12
                  j mmode_intr_vector_13
                  j mmode_intr_vector_14
                  j mmode_intr_vector_15
                  .option rvc;

mmode_exception_handler:
                  csrrw x10, 0x340, x10
                  add x10, x30, zero
                  1: addi x10, x10, -124
                  sw x1, 4(x10)
                  sw x2, 8(x10)
                  sw x3, 12(x10)
                  sw x4, 16(x10)
                  sw x5, 20(x10)
                  sw x6, 24(x10)
                  sw x7, 28(x10)
                  sw x8, 32(x10)
                  sw x9, 36(x10)
                  sw x10, 40(x10)
                  sw x11, 44(x10)
                  sw x12, 48(x10)
                  sw x13, 52(x10)
                  sw x14, 56(x10)
                  sw x15, 60(x10)
                  sw x16, 64(x10)
                  sw x17, 68(x10)
                  sw x18, 72(x10)
                  sw x19, 76(x10)
                  sw x20, 80(x10)
                  sw x21, 84(x10)
                  sw x22, 88(x10)
                  sw x23, 92(x10)
                  sw x24, 96(x10)
                  sw x25, 100(x10)
                  sw x26, 104(x10)
                  sw x27, 108(x10)
                  sw x28, 112(x10)
                  sw x29, 116(x10)
                  sw x30, 120(x10)
                  sw x31, 124(x10)
                  csrr x6, 0x341 # MEPC
                  csrr x6, 0x342 # MCAUSE
                  li x23, 0xb # ECALL_MMODE
                  beq x6, x23, ecall_handler
                  li x23, 0x2 # ILLEGAL_INSTRUCTION
                  beq x6, x23, illegal_instr_handler
                  csrr x23, 0x343 # MTVAL
                  1: la x31, test_done
                  jalr x1, x31, 0

ecall_handler:    
                  la x6, _start
                  sw x0, 0(x6)
                  sw x1, 4(x6)
                  sw x2, 8(x6)
                  sw x3, 12(x6)
                  sw x4, 16(x6)
                  sw x5, 20(x6)
                  sw x6, 24(x6)
                  sw x7, 28(x6)
                  sw x8, 32(x6)
                  sw x9, 36(x6)
                  sw x10, 40(x6)
                  sw x11, 44(x6)
                  sw x12, 48(x6)
                  sw x13, 52(x6)
                  sw x14, 56(x6)
                  sw x15, 60(x6)
                  sw x16, 64(x6)
                  sw x17, 68(x6)
                  sw x18, 72(x6)
                  sw x19, 76(x6)
                  sw x20, 80(x6)
                  sw x21, 84(x6)
                  sw x22, 88(x6)
                  sw x23, 92(x6)
                  sw x24, 96(x6)
                  sw x25, 100(x6)
                  sw x26, 104(x6)
                  sw x27, 108(x6)
                  sw x28, 112(x6)
                  sw x29, 116(x6)
                  sw x30, 120(x6)
                  sw x31, 124(x6)
                  la x31, write_tohost
                  jalr x0, x31, 0

illegal_instr_handler:
                  csrr  x6, 0x341
                  addi  x6, x6, 4
                  csrw  0x341, x6
                  lw x1, 4(x10)
                  lw x2, 8(x10)
                  lw x3, 12(x10)
                  lw x4, 16(x10)
                  lw x5, 20(x10)
                  lw x6, 24(x10)
                  lw x7, 28(x10)
                  lw x8, 32(x10)
                  lw x9, 36(x10)
                  lw x10, 40(x10)
                  lw x11, 44(x10)
                  lw x12, 48(x10)
                  lw x13, 52(x10)
                  lw x14, 56(x10)
                  lw x15, 60(x10)
                  lw x16, 64(x10)
                  lw x17, 68(x10)
                  lw x18, 72(x10)
                  lw x19, 76(x10)
                  lw x20, 80(x10)
                  lw x21, 84(x10)
                  lw x22, 88(x10)
                  lw x23, 92(x10)
                  lw x24, 96(x10)
                  lw x25, 100(x10)
                  lw x26, 104(x10)
                  lw x27, 108(x10)
                  lw x28, 112(x10)
                  lw x29, 116(x10)
                  lw x30, 120(x10)
                  lw x31, 124(x10)
                  addi x10, x10, 124
                  add x30, x10, zero
                  csrrw x10, 0x340, x10
                  mret

pt_fault_handler: 

.align 2
mmode_intr_handler:
                  csrr  x6, 0x300 # MSTATUS;
                  csrr  x6, 0x304 # MIE;
                  csrr  x6, 0x344 # MIP;
                  csrrc x6, 0x344, x6 # MIP;
                  lw x1, 4(x10)
                  lw x2, 8(x10)
                  lw x3, 12(x10)
                  lw x4, 16(x10)
                  lw x5, 20(x10)
                  lw x6, 24(x10)
                  lw x7, 28(x10)
                  lw x8, 32(x10)
                  lw x9, 36(x10)
                  lw x10, 40(x10)
                  lw x11, 44(x10)
                  lw x12, 48(x10)
                  lw x13, 52(x10)
                  lw x14, 56(x10)
                  lw x15, 60(x10)
                  lw x16, 64(x10)
                  lw x17, 68(x10)
                  lw x18, 72(x10)
                  lw x19, 76(x10)
                  lw x20, 80(x10)
                  lw x21, 84(x10)
                  lw x22, 88(x10)
                  lw x23, 92(x10)
                  lw x24, 96(x10)
                  lw x25, 100(x10)
                  lw x26, 104(x10)
                  lw x27, 108(x10)
                  lw x28, 112(x10)
                  lw x29, 116(x10)
                  lw x30, 120(x10)
                  lw x31, 124(x10)
                  addi x10, x10, 124
                  add x30, x10, zero
                  csrrw x10, 0x340, x10
                  mret;

kernel_instr_end: nop
.align 2
kernel_data_start:
.section .kernel_stack,"aw",@progbits;
.align 2
kernel_stack_start:
.rept 4999
.4byte 0x0
.endr
kernel_stack_end:
.4byte 0x0
