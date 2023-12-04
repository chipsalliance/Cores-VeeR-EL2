.include "user_define.h"
.globl _start
.section .text
_start:           
                  .include "user_init.s"
                  csrr x5, 0xf14
                  li x6, 0
                  beq x5, x6, 0f

0: la x11, h0_start
jalr x0, x11, 0
h0_start:
                  li x9, 0x40001104
                  csrw 0x301, x9
kernel_sp:        
                  la x22, kernel_stack_end

trap_vec_init:    
                  la x9, mtvec_handler
                  ori x9, x9, 1
                  csrw 0x305, x9 # MTVEC

mepc_setup:       
                  la x9, init
                  csrw 0x341, x9

custom_csr_setup: 
                  nop

init_machine_mode:
                  li x9, 0x1800
                  csrw 0x300, x9 # MSTATUS
                  li x9, 0x0
                  csrw 0x304, x9 # MIE
                  mret
init:             
                  li x0, 0x80000000
                  li x1, 0xff9db0b3
                  li x2, 0x67c49e63
                  li x3, 0xd532ded0
                  li x4, 0x0
                  li x5, 0x0
                  li x6, 0xa111a2ef
                  li x7, 0x0
                  li x8, 0x0
                  li x9, 0x0
                  li x10, 0xa
                  li x11, 0x0
                  li x12, 0x5fdc69af
                  li x13, 0x0
                  li x15, 0x0
                  li x16, 0x80000000
                  li x17, 0x44903f8b
                  li x18, 0x80000000
                  li x19, 0xf48bf689
                  li x20, 0x6
                  li x21, 0xf7ff7b83
                  li x23, 0xf
                  li x24, 0xfe547a7b
                  li x25, 0xf483fc9a
                  li x26, 0xfd3b7127
                  li x27, 0xf43d9e72
                  li x28, 0x1
                  li x29, 0xfa0fa6fd
                  li x30, 0xf81924fa
                  li x31, 0x2
                  la x14, user_stack_end
main:             li           t5, 0x9f2db7e7 #start riscv_int_numeric_corner_stream_15
                  li           a7, 0xb302540
                  li           s3, 0x9ab3ef9d
                  li           t1, 0xffffffff
                  li           gp, 0xffffffff
                  li           tp, 0xffffffff
                  li           s1, 0x87d45c0c
                  li           s11, 0x0
                  li           s7, 0xffffffff
                  li           a2, 0xdf64860b
                  lui          a2, 439420
                  mulh         t5, a2, t5
                  lui          s1, 822898
                  lui          t1, 759709
                  add          t5, t5, s1
                  rem          gp, t5, t5
                  add          gp, tp, s1
                  mul          s1, s7, a2
                  mulhu        gp, gp, gp
                  divu         gp, t5, s1
                  mulhsu       s7, tp, t5
                  mulhsu       s7, s11, s7
                  div          s7, gp, a7
                  mul          a2, s1, gp
                  nop
                  remu         t5, s1, gp
                  nop
                  rem          t1, s3, t5
                  div          s3, s3, a7
                  addi         gp, s7, 1210
                  sub          s1, s11, s3
                  mul          a2, t5, s1
                  addi         tp, s11, 1669
                  remu         t1, s11, t5
                  mulhu        s7, s7, s1 #end riscv_int_numeric_corner_stream_15
                  li           t3, 0x0 #start riscv_int_numeric_corner_stream_14
                  li           s8, 0xffffffff
                  li           a5, 0x80000000
                  li           a2, 0xffffffff
                  li           s3, 0xffffffff
                  li           s9, 0x0
                  li           s11, 0x80000000
                  li           a3, 0x80000000
                  li           a0, 0x80000000
                  li           t6, 0x0
                  auipc        s8, 400220
                  mulh         a0, a3, a3
                  mulhu        s3, t6, s3
                  mul          s8, t6, s8
                  mulhsu       t3, s9, t6
                  div          s11, a2, a0
                  rem          a0, s11, a3
                  mulh         s3, s11, s8
                  nop
                  mulh         a2, s9, a5
                  div          s9, s8, a0
                  lui          s8, 881123
                  remu         a3, t3, a0
                  nop
                  remu         t3, s8, a5
                  div          t6, a3, s11
                  sub          a5, s9, s8 #end riscv_int_numeric_corner_stream_14
                  li           s7, 0x0 #start riscv_int_numeric_corner_stream_6
                  li           t4, 0x80000000
                  li           t0, 0xffffffff
                  li           a6, 0xffffffff
                  li           s9, 0x80000000
                  li           gp, 0xffffffff
                  li           ra, 0x58165ca9
                  li           a0, 0x0
                  li           tp, 0x0
                  li           s11, 0x80000000
                  div          t0, s11, gp
                  mul          t4, t4, s9
                  sub          t4, t0, tp
                  nop
                  mul          s11, s9, s7
                  lui          t4, 692976
                  rem          s7, tp, t4
                  div          s7, a6, s11
                  addi         t4, s11, 1994
                  add          s7, tp, gp
                  lui          t4, 121780
                  sub          gp, s9, s11
                  mulh         s7, s7, tp
                  nop
                  add          s7, tp, ra
                  add          a6, s7, t0 #end riscv_int_numeric_corner_stream_6
                  li           gp, 0xffffffff #start riscv_int_numeric_corner_stream_23
                  li           t5, 0x80000000
                  li           t2, 0x80000000
                  li           a2, 0xffffffff
                  li           s1, 0x0
                  li           s2, 0x80000000
                  li           t6, 0x0
                  li           s11, 0xf80ab73b
                  li           s0, 0xffffffff
                  li           a7, 0x80000000
                  rem          s1, t6, t6
                  remu         t2, s1, s0
                  div          s2, gp, s0
                  sub          a7, a7, t5
                  rem          t2, t2, a2
                  mulhsu       s2, gp, t6
                  remu         gp, a2, s2
                  auipc        a7, 207349
                  auipc        gp, 628202
                  mulhu        s11, gp, a7
                  remu         a7, t5, a2
                  mul          t6, s2, s11
                  lui          s11, 33173
                  mulhu        gp, t5, a2
                  addi         t5, t6, -644
                  mulhu        gp, t2, a7
                  sub          s0, t2, t2
                  rem          s2, s0, t5
                  mul          t5, t5, s11
                  nop
                  mulh         a7, t5, s11
                  addi         a7, s0, -545
                  sub          t2, a2, t2
                  addi         s0, t2, -1845
                  auipc        a7, 442015
                  remu         s0, s1, s2
                  mulh         s1, s11, s0
                  addi         t2, a2, 987
                  mulhsu       s0, s2, s0
                  remu         t2, s0, s1 #end riscv_int_numeric_corner_stream_23
                  li           s1, 0x1ad9b073 #start riscv_int_numeric_corner_stream_27
                  li           a0, 0xffffffff
                  li           s0, 0x0
                  li           t1, 0x5453fdae
                  li           a7, 0xc7f9e28e
                  li           s9, 0xddaeac51
                  li           s4, 0x80000000
                  li           t3, 0x0
                  li           s10, 0xffffffff
                  li           s7, 0xffffffff
                  lui          a7, 408467
                  div          s7, a0, t1
                  divu         s10, a7, s7
                  sub          s9, t3, a0
                  mulhu        t3, s7, s1
                  remu         s1, s10, s0
                  lui          a7, 791415
                  nop
                  sub          s9, t3, s9
                  addi         s7, t3, 2021
                  add          a7, t3, t3
                  rem          t3, a0, s1
                  mulh         s7, s7, s4
                  divu         t1, s0, s10
                  lui          s4, 1021600
                  add          s1, s7, t1
                  divu         a7, t3, s10
                  divu         t3, s0, t3
                  nop
                  mulhsu       a0, s10, t1
                  lui          s1, 729159
                  auipc        a0, 270551
                  div          s9, t3, t3
                  addi         s7, s0, -1663 #end riscv_int_numeric_corner_stream_27
                  li           s11, 0x80000000 #start riscv_int_numeric_corner_stream_22
                  li           s4, 0x80000000
                  li           s3, 0x0
                  li           a7, 0x8fd89f98
                  li           s2, 0x0
                  li           s1, 0xffffffff
                  li           a5, 0xffffffff
                  li           t0, 0x80000000
                  li           s0, 0x80000000
                  li           t4, 0x0
                  mul          a7, t4, t0
                  auipc        s11, 909291
                  auipc        s4, 668406
                  divu         a7, a7, t0
                  addi         s3, s2, -1630
                  remu         a7, s11, a5
                  remu         s4, s0, t4
                  mulhu        s11, s11, s3
                  rem          t0, t4, s4
                  nop
                  mulhu        s3, s11, s1
                  auipc        s1, 958566
                  add          s4, s4, s2
                  mulhu        s3, t4, s11
                  addi         t0, s11, 992
                  rem          s1, t0, s4
                  addi         s4, t4, -1652
                  mul          t4, a7, a7
                  rem          a7, s3, a5
                  auipc        t0, 688499
                  rem          s3, s0, s0 #end riscv_int_numeric_corner_stream_22
                  li           ra, 0x80000000 #start riscv_int_numeric_corner_stream_32
                  li           gp, 0x6bc331c3
                  li           t5, 0x0
                  li           a3, 0x0
                  li           t1, 0xffffffff
                  li           s1, 0xffffffff
                  li           s8, 0xffffffff
                  li           a2, 0xffffffff
                  li           s5, 0x0
                  li           a7, 0xffffffff
                  remu         t5, s5, s1
                  mul          s1, s1, gp
                  divu         s1, t5, t5
                  mulhsu       a3, t5, t5
                  sub          gp, gp, s1
                  add          s1, s1, ra
                  add          s8, t1, gp
                  lui          s8, 11208
                  remu         t1, s5, s8
                  auipc        ra, 450068
                  remu         s8, a7, s5
                  addi         t1, ra, 1100
                  mulhu        a7, ra, t5
                  mul          t1, a3, t1
                  auipc        s1, 944732
                  rem          t5, a2, a7
                  lui          t1, 617842
                  div          a2, s5, t1
                  div          s1, t5, s1 #end riscv_int_numeric_corner_stream_32
                  li           t2, 0xffffffff #start riscv_int_numeric_corner_stream_10
                  li           tp, 0x80000000
                  li           ra, 0x0
                  li           s8, 0xffffffff
                  li           t6, 0x80000000
                  li           sp, 0x6c78488e
                  li           s1, 0xffffffff
                  li           t0, 0x80000000
                  li           s11, 0x80000000
                  li           s9, 0xffffffff
                  mulhsu       s8, ra, t6
                  addi         t6, s1, -644
                  addi         tp, s9, 652
                  div          ra, ra, s9
                  mulhu        s8, t2, s1
                  add          s8, t0, s1
                  mulh         s1, t2, s1
                  mulh         t0, tp, s11
                  auipc        ra, 917868
                  rem          s8, s11, ra
                  sub          sp, s9, t2
                  sub          ra, s8, t0
                  add          ra, t6, ra
                  divu         t2, ra, sp
                  nop
                  mulh         s9, ra, sp
                  div          tp, s8, s11 #end riscv_int_numeric_corner_stream_10
                  li           a3, 0x0 #start riscv_int_numeric_corner_stream_26
                  li           s4, 0xa0a43691
                  li           tp, 0xffffffff
                  li           t6, 0x532bf4ef
                  li           t1, 0x0
                  li           t3, 0x7b07cd6b
                  li           a2, 0x0
                  li           sp, 0x80000000
                  li           s7, 0x80000000
                  li           s10, 0x0
                  nop
                  lui          s4, 376978
                  mulhsu       t6, a3, tp
                  mulh         t1, a3, tp
                  add          s7, a2, s7
                  add          sp, a3, s10
                  auipc        t1, 10246
                  rem          t6, t1, s7
                  add          tp, s4, a3
                  div          t1, a2, a2
                  sub          t3, t6, tp
                  remu         s4, s7, tp
                  lui          t6, 989206
                  nop
                  nop
                  mulh         a3, sp, tp
                  add          t1, t6, a2 #end riscv_int_numeric_corner_stream_26
                  li           ra, 0x0 #start riscv_int_numeric_corner_stream_5
                  li           s2, 0x894adc8e
                  li           s3, 0x0
                  li           sp, 0x3f2494b1
                  li           s4, 0x0
                  li           t2, 0x0
                  li           s9, 0x80000000
                  li           s10, 0x0
                  li           s7, 0x0
                  li           a3, 0x80000000
                  add          a3, s7, s10
                  div          s7, t2, s3
                  remu         s4, s7, s4
                  rem          t2, s7, ra
                  add          a3, sp, s7
                  div          a3, a3, s10
                  sub          s3, s4, s7
                  div          s3, a3, sp
                  addi         sp, ra, -1625
                  add          s3, s2, s9
                  add          s7, s4, s2
                  addi         s10, s3, -156
                  auipc        t2, 659347
                  div          ra, a3, s4
                  rem          s7, sp, s3 #end riscv_int_numeric_corner_stream_5
                  li           s2, 0xffffffff #start riscv_int_numeric_corner_stream_0
                  li           t1, 0x70c068ad
                  li           s11, 0x80000000
                  li           tp, 0x80000000
                  li           t5, 0x80000000
                  li           s5, 0x80000000
                  li           t2, 0x0
                  li           a6, 0xffffffff
                  li           s10, 0xffffffff
                  li           s1, 0x80000000
                  div          t5, a6, s5
                  auipc        t2, 21979
                  remu         t2, s10, a6
                  mulhsu       t2, s1, s11
                  auipc        s1, 712074
                  lui          s2, 1621
                  addi         s5, t5, -667
                  mulhu        s2, a6, a6
                  auipc        t5, 51308
                  lui          t1, 182784
                  nop
                  sub          s5, tp, a6
                  mulh         s5, t2, a6
                  mulhu        s2, t5, tp
                  mulh         s10, s11, t1
                  rem          a6, tp, s11
                  auipc        t5, 259344
                  divu         a6, t1, s11
                  rem          t5, t1, s11
                  remu         t5, tp, t1
                  sub          t2, s11, a6
                  lui          s10, 886543
                  sub          t2, t5, t1 #end riscv_int_numeric_corner_stream_0
                  li           sp, 0x3e9c6393 #start riscv_int_numeric_corner_stream_19
                  li           t3, 0x80000000
                  li           t5, 0x1180d20e
                  li           t1, 0xffffffff
                  li           tp, 0x0
                  li           s4, 0xffffffff
                  li           a3, 0xddbe2b28
                  li           gp, 0x0
                  li           s5, 0xffffffff
                  li           t0, 0xffffffff
                  lui          t1, 573320
                  mul          sp, t0, a3
                  remu         t3, a3, s5
                  lui          t3, 535038
                  mulhsu       t5, gp, sp
                  addi         gp, s4, 419
                  mulhu        t0, gp, a3
                  remu         t5, tp, a3
                  lui          t0, 30845
                  auipc        t0, 972355
                  mulhsu       gp, tp, s5
                  auipc        t1, 324577
                  mulhu        gp, sp, t1
                  lui          a3, 447289
                  lui          gp, 860628
                  mulhsu       s4, s4, t3
                  div          t5, tp, s5 #end riscv_int_numeric_corner_stream_19
                  li           t3, 0xfb6f665c #start riscv_int_numeric_corner_stream_38
                  li           s4, 0x80000000
                  li           s3, 0xffffffff
                  li           tp, 0xffffffff
                  li           s8, 0x0
                  li           s10, 0x80000000
                  li           t4, 0x0
                  li           gp, 0x5973b5e
                  li           s7, 0xffffffff
                  li           s2, 0x80000000
                  remu         tp, s10, s2
                  divu         tp, t4, s7
                  add          s3, t3, s7
                  remu         s10, s10, t4
                  lui          gp, 253086
                  add          s10, t4, gp
                  lui          s2, 263092
                  div          tp, tp, gp
                  mul          t4, s10, s10
                  div          s8, s4, s2
                  mulhu        s10, s7, s2
                  mulhsu       s3, t3, s4
                  sub          gp, s10, s10
                  sub          tp, s4, tp
                  rem          gp, s3, s8
                  mulhu        s7, s2, s3
                  add          gp, s7, s4
                  mul          t4, s10, s4
                  lui          t4, 788422
                  lui          s4, 125999
                  addi         t3, gp, 1405
                  add          s10, s2, s4
                  auipc        s2, 636432
                  mulh         s3, s3, t4 #end riscv_int_numeric_corner_stream_38
                  li           t3, 0xffffffff #start riscv_int_numeric_corner_stream_35
                  li           s2, 0xffffffff
                  li           a6, 0x0
                  li           t2, 0x80000000
                  li           s3, 0x80000000
                  li           a7, 0x0
                  li           s1, 0xffffffff
                  li           s5, 0x0
                  li           t0, 0xffffffff
                  li           a0, 0x0
                  mulh         s3, s5, a6
                  sub          a7, s3, t3
                  lui          s5, 731828
                  mul          a7, a7, s3
                  mulh         a7, a7, t3
                  add          t0, s3, a0
                  add          t3, a7, t2
                  nop
                  sub          t3, t0, s1
                  mulh         s3, s5, s1
                  addi         a6, s1, -1863
                  div          s5, t0, t3
                  auipc        a0, 749452
                  mulhu        t3, s2, t0
                  div          s1, t3, s3
                  div          s2, a6, s5
                  mul          t0, a7, a0
                  mulh         t2, t2, a6
                  mulhu        s3, t3, t0
                  add          s1, t2, s1
                  addi         s1, t0, 1757
                  div          a0, a0, t0
                  rem          t2, a7, t3
                  add          s1, s1, t2
                  addi         t3, a6, 258
                  mul          t0, s3, s2 #end riscv_int_numeric_corner_stream_35
                  li           s9, 0x0 #start riscv_int_numeric_corner_stream_3
                  li           t0, 0xaa6a9755
                  li           s0, 0x0
                  li           ra, 0xaf61bc32
                  li           gp, 0x69fe6a33
                  li           t2, 0x77c3e685
                  li           t3, 0x80000000
                  li           s8, 0xffffffff
                  li           s7, 0x80000000
                  li           sp, 0xffffffff
                  div          s9, ra, s7
                  divu         ra, ra, gp
                  remu         s7, s7, ra
                  nop
                  mulhsu       s8, ra, gp
                  divu         s8, t0, s0
                  rem          t0, s8, gp
                  mulhsu       gp, s8, sp
                  rem          s9, sp, s7
                  add          s8, s8, sp
                  mul          s0, s0, t0
                  remu         sp, t2, s9
                  addi         s7, s9, -113
                  mulhsu       t3, t3, t2
                  div          ra, s0, sp
                  add          t2, sp, s0
                  mulhu        sp, t3, gp
                  div          s7, s0, s8
                  rem          s8, ra, s7
                  lui          ra, 913979
                  add          t0, t2, s9
                  mul          gp, s7, t0
                  sub          s7, t0, s0
                  mulh         s7, t2, gp
                  add          t0, s0, ra
                  add          s9, t2, s9
                  rem          s7, sp, gp
                  mulh         s0, gp, t3 #end riscv_int_numeric_corner_stream_3
                  li           s7, 0xbe418703 #start riscv_int_numeric_corner_stream_33
                  li           s3, 0xffffffff
                  li           tp, 0x3d6f4db6
                  li           t2, 0x80000000
                  li           s1, 0xffffffff
                  li           t6, 0xb02eba0f
                  li           s2, 0xe7db1524
                  li           s4, 0x80000000
                  li           a6, 0x0
                  li           s5, 0xfe52312c
                  div          a6, s5, tp
                  lui          s4, 130562
                  mulhu        s5, s2, s4
                  auipc        a6, 894793
                  lui          s7, 307328
                  sub          tp, a6, s3
                  lui          a6, 108991
                  mulhsu       s1, s7, t6
                  lui          s1, 377778
                  mulh         t6, t2, tp
                  lui          s5, 188004
                  nop
                  lui          s3, 436255
                  add          s1, s3, s4
                  nop #end riscv_int_numeric_corner_stream_33
                  c.addi4spn   a3, sp, 176
                  c.and        a0, a5
                  and          t3, t6, s6
                  remu         gp, t1, s11
                  c.li         tp, 14
                  mulh         s9, s3, s2
                  c.mv         t4, t0
                  andi         gp, t0, 1631
                  mulhsu       t6, t1, s2
                  lui          t1, 138936
                  mulh         s1, gp, ra
                  srai         a6, s1, 30
                  li           t1, 0xffffffff #start riscv_int_numeric_corner_stream_13
                  li           sp, 0x80000000
                  li           t0, 0x0
                  li           s11, 0x4fe142ee
                  li           a2, 0xffffffff
                  li           a5, 0x80000000
                  li           t2, 0xe09a3b29
                  li           s0, 0x0
                  li           t4, 0xffffffff
                  li           s2, 0xecb51bc3
                  add          s2, t1, t0
                  mulhsu       t2, sp, s2
                  auipc        t0, 747291
                  div          a2, a2, t1
                  remu         a5, t1, t4
                  mulhsu       s2, t4, t1
                  div          s2, a2, a5
                  nop
                  divu         a5, t2, s11
                  add          sp, t1, a2
                  divu         t4, s11, t4
                  sub          sp, t0, sp
                  mulhu        t0, sp, s2
                  lui          s0, 729397
                  mulhsu       s2, a5, sp
                  divu         sp, t0, s2
                  div          a5, t2, s11
                  addi         sp, a2, -713
                  addi         s11, a5, -1424
                  mul          s0, s11, s0
                  nop
                  auipc        t2, 446015
                  addi         s2, a5, 1823
                  divu         s0, s2, t0
                  lui          t4, 1018912
                  mulhsu       t4, s0, a5
                  auipc        s0, 312833 #end riscv_int_numeric_corner_stream_13
                  c.srli       a2, 22
                  sltu         sp, s5, a1
                  c.srli       s0, 25
                  mulhu        s2, a6, s7
                  srli         s5, sp, 8
                  andi         s10, a4, 900
                  c.srli       a0, 17
                  c.nop
                  c.nop
                  c.add        a0, t4
                  srai         s10, s8, 18
                  srli         s11, t1, 1
                  c.mv         t1, a2
                  c.addi16sp   sp, -16
                  or           s2, a3, a5
                  c.addi16sp   sp, 304
                  c.andi       a2, 19
                  c.mv         s0, a5
                  xor          s11, s6, s3
                  div          s2, a0, a1
                  mulhu        s9, a1, t4
                  andi         t0, t3, -1148
                  c.srli       s1, 13
                  c.mv         s3, t3
                  mul          t3, t6, t2
                  sltiu        a6, a3, 2032
                  mulh         s9, sp, sp
                  xor          tp, s6, s6
                  c.xor        a2, a1
                  addi         a2, s8, 184
                  c.addi       a6, 8
                  mulhu        a6, a1, tp
                  add          zero, s10, a4
                  mulhsu       t2, t5, gp
                  add          a3, a7, t2
                  slt          t1, s9, s2
                  c.lui        t0, 6
                  andi         s10, sp, 698
                  c.add        t4, a6
                  ori          a2, s9, -367
                  sltu         a5, a3, a7
                  c.srai       a5, 19
                  rem          zero, t5, ra
                  c.and        a3, a1
                  c.srai       a3, 19
                  c.srli       a3, 12
                  rem          t1, tp, s10
                  remu         gp, gp, t1
                  c.lui        t5, 29
                  slt          t0, t1, t0
                  xori         sp, t2, -1258
                  c.andi       a3, -1
                  c.sub        a0, a1
                  c.addi16sp   sp, 16
                  slli         s11, t5, 1
                  sltu         s3, a4, t1
                  sltiu        a5, s1, 1432
                  c.nop
                  addi         zero, a2, -1002
                  lui          s11, 46111
                  c.add        s11, s7
                  sra          s5, s4, s1
                  c.nop
                  addi         s4, a3, -1016
                  div          s8, a5, s5
                  c.and        a3, s1
                  divu         t4, t5, t5
                  c.nop
                  slli         a2, s10, 7
                  lui          s4, 447584
                  andi         gp, s3, -424
                  mul          a6, t5, a0
                  rem          s4, t4, t1
                  mulhu        tp, s5, t6
                  xori         s4, s5, -89
                  slli         sp, t4, 30
                  sra          t1, t6, a1
                  auipc        s4, 499533
                  div          t6, s11, a1
                  lui          tp, 409853
                  slt          s8, t5, t6
                  c.nop
                  sltu         a5, a3, sp
                  auipc        a6, 758072
                  c.mv         t1, a5
                  c.slli       s9, 4
                  c.srli       a2, 29
                  rem          t5, s9, t1
                  srl          sp, zero, a7
                  c.or         s0, s1
                  c.andi       a0, -1
                  sll          t2, ra, s6
                  divu         zero, a3, a4
                  div          a7, zero, zero
                  srai         t3, t1, 11
                  remu         sp, s10, ra
                  c.addi       t4, 17
                  xor          s4, t6, s6
                  c.addi16sp   sp, 16
                  or           s7, a3, s4
                  auipc        t2, 864282
                  sll          s3, a3, t3
                  sltiu        zero, a4, -997
                  c.mv         tp, a7
                  c.slli       t3, 21
                  sltu         a0, s8, t3
                  c.and        a2, s1
                  c.li         a0, 4
                  addi         t6, s3, -894
                  c.andi       a5, -1
                  c.or         s1, a5
                  srl          t4, s7, sp
                  sra          s9, a0, s10
                  add          s1, s1, s6
                  c.addi       t4, -1
                  nop
                  xori         s1, a7, -1318
                  xori         s7, a7, -1762
                  c.andi       s0, -1
                  or           s3, a3, tp
                  c.addi4spn   a0, sp, 720
                  srl          s4, a7, t0
                  remu         s11, sp, s3
                  c.addi       a5, 13
                  c.srai       s0, 5
                  mulhu        t4, s5, sp
                  xor          s2, a4, s5
                  c.xor        s1, a4
                  c.li         s5, -1
                  lui          t0, 491292
                  c.slli       a7, 31
                  c.lui        s5, 1
                  c.andi       s1, -1
                  c.or         a3, s0
                  slt          ra, s8, tp
                  nop
                  sltu         s10, s5, a1
                  sra          t5, t1, a0
                  sra          t6, t0, t4
                  mulhu        a3, t1, s10
                  mulhsu       tp, s11, t2
                  and          tp, ra, a4
                  c.andi       a2, 21
                  add          s8, s2, a6
                  srl          s10, s7, s6
                  div          tp, s9, s5
                  sltiu        t3, s1, 944
                  c.lui        a6, 12
                  srai         ra, s1, 19
                  xor          sp, a6, s9
                  c.nop
                  slli         gp, s2, 24
                  auipc        t1, 709278
                  c.addi4spn   a2, sp, 128
                  and          s10, a6, a3
                  slt          a7, sp, s1
                  c.sub        a2, s0
                  auipc        s1, 452180
                  c.nop
                  and          s2, ra, t4
                  c.sub        a0, a2
                  nop
                  c.sub        a5, a3
                  c.sub        a0, a0
                  c.mv         s1, t2
                  c.srai       a2, 24
                  srl          t6, s11, zero
                  mul          a5, tp, s6
                  c.addi16sp   sp, -16
                  srai         s5, a7, 17
                  andi         s8, s8, 1010
                  sra          s8, t5, s8
                  mulh         t3, a6, tp
                  c.slli       a2, 21
                  c.nop
                  c.add        t3, t6
                  auipc        s0, 396195
                  c.andi       s0, 16
                  c.addi       s7, 9
                  mul          s1, t2, a2
                  c.and        a0, a1
                  c.and        a0, a0
                  mulhsu       a3, a4, s8
                  addi         a7, t4, 488
                  add          s0, s7, a7
                  sltiu        t4, t5, 1349
                  nop
                  addi         s8, s10, 1165
                  sra          a5, a6, t4
                  sub          s0, a1, s6
                  c.add        s9, t6
                  lui          t0, 345812
                  c.mv         s8, a1
                  mul          t0, sp, s11
                  sra          ra, zero, t0
                  c.lui        s4, 30
                  c.andi       a3, -1
                  sll          s8, s4, s10
                  divu         s3, s7, t3
                  sltiu        a0, zero, 1664
                  c.sub        a0, a4
                  sll          s10, t6, s9
                  mul          a0, s5, s5
                  c.and        a2, a5
                  sll          a2, t1, t2
                  and          t2, tp, t5
                  or           s4, ra, tp
                  mulhsu       a5, s5, s11
                  mul          s11, t4, t5
                  c.addi16sp   sp, -16
                  c.mv         t6, a5
                  xor          t5, tp, a0
                  c.srli       a0, 31
                  slt          s0, t2, a3
                  sll          t1, ra, a0
                  mul          tp, zero, s7
                  slti         t1, s9, -684
                  c.nop
                  c.lui        s3, 3
                  remu         a2, t1, t3
                  srli         a6, s3, 26
                  c.srai       s1, 4
                  c.mv         s11, s11
                  nop
                  mulhsu       gp, s3, s0
                  c.li         s1, -1
                  c.add        gp, a5
                  c.li         tp, -1
                  c.nop
                  c.addi4spn   s1, sp, 928
                  sub          a7, s8, s9
                  slli         s1, s5, 13
                  ori          sp, s1, -668
                  c.mv         a3, s3
                  c.addi16sp   sp, -16
                  slt          t2, s9, a3
                  sltiu        a5, a3, -1529
                  c.addi4spn   a3, sp, 320
                  auipc        s8, 830712
                  and          a5, s10, s11
                  rem          s8, s1, s10
                  sra          ra, t3, s2
                  sll          zero, a6, s3
                  c.li         s4, 28
                  c.mv         t4, t6
                  slti         t0, s0, 458
                  c.sub        a3, s0
                  add          t1, t3, s9
                  xori         s3, s2, 1005
                  sll          a7, t3, s3
                  sltu         sp, t5, a1
                  c.srai       a2, 10
                  mul          s7, ra, t0
                  srai         s3, t3, 5
                  ori          a2, s7, 1493
                  mulhsu       tp, a2, a1
                  c.and        s1, s1
                  rem          t1, s5, t2
                  c.slli       s2, 26
                  div          s7, s5, t0
                  c.mv         ra, s11
                  mulhu        gp, a6, a3
                  c.lui        t3, 8
                  remu         a2, s3, s4
                  andi         s0, a0, 642
                  andi         t5, sp, -1730
                  sra          t5, s11, s3
                  rem          t1, a3, t5
                  c.nop
                  mul          a7, t3, a0
                  rem          s7, s8, t1
                  xor          ra, s7, a0
                  rem          s0, s2, s6
                  sltu         gp, s7, s8
                  or           t6, tp, a6
                  mul          a5, t6, a4
                  auipc        s11, 105646
                  and          s8, a0, gp
                  add          t1, gp, t3
                  addi         t5, s7, 1046
                  sll          s8, t4, t6
                  c.nop
                  c.or         a2, s0
                  c.add        t6, t2
                  c.sub        a2, a1
                  c.li         s11, 23
                  addi         t1, s11, 1105
                  rem          s3, s10, s6
                  rem          sp, s0, a4
                  sltu         t2, s2, s7
                  xor          a3, s5, s6
                  add          t0, s4, s9
                  div          a3, s10, s2
                  div          a2, ra, zero
                  ori          t6, t6, -1233
                  c.addi16sp   sp, -16
                  ori          t0, t6, -533
                  slti         t0, a5, -498
                  srl          t0, tp, s1
                  mul          a6, tp, a4
                  c.addi16sp   sp, -16
                  c.addi16sp   sp, -16
                  sll          s4, a1, s9
                  c.mv         s3, s6
                  c.andi       a0, 11
                  c.nop
                  mulhsu       s7, tp, s9
                  ori          s3, t6, -200
                  c.srli       a3, 25
                  nop
                  c.or         a0, a5
                  sltu         a3, a1, s7
                  mulh         a3, s6, zero
                  and          a7, s4, s6
                  remu         a2, s0, s11
                  auipc        a3, 893500
                  div          a6, zero, a3
                  c.addi16sp   sp, -16
                  sll          a2, t6, s11
                  mulhu        s4, t0, ra
                  srl          s8, a2, gp
                  andi         t0, zero, 1687
                  srli         a3, t6, 7
                  c.lui        a3, 22
                  c.nop
                  rem          ra, a7, t6
                  slt          a3, s3, a1
                  addi         s3, s0, -11
                  addi         zero, t2, -1906
                  sra          t5, gp, t4
                  c.andi       s0, -1
                  mulhu        t0, a2, s0
                  div          t4, t6, s8
                  div          t4, t6, s5
                  slti         t3, s8, -89
                  ori          t5, t2, -1300
                  xori         s10, a6, -2034
                  srli         s8, t3, 25
                  srl          t2, t1, a3
                  sra          t5, a0, t6
                  c.srai       a3, 25
                  div          t4, t3, t4
                  andi         a3, a1, -1536
                  sub          t3, s9, s4
                  c.nop
                  mulhsu       a5, t2, s2
                  mulhu        a0, t0, a6
                  c.or         a2, a2
                  sra          s10, a6, a6
                  lui          t0, 531223
                  mulh         s1, s0, a6
                  add          a0, gp, t4
                  sll          a6, s9, t1
                  div          ra, sp, t5
                  mulhsu       t6, ra, s7
                  ori          s2, s11, 32
                  c.and        a5, a4
                  c.srai       a2, 1
                  andi         ra, t6, 1774
                  sra          s11, t5, s1
                  divu         s10, t4, s6
                  srai         tp, t0, 6
                  slti         t6, s3, -1201
                  sll          s5, zero, s3
                  c.li         a6, 12
                  c.and        s0, a4
                  c.xor        s0, a3
                  srli         t3, s4, 17
                  lui          s7, 86033
                  div          t6, t5, a2
                  and          sp, a0, a0
                  slt          s10, t2, s6
                  or           s0, s2, a6
                  mulhsu       t4, a5, sp
                  mulhsu       a3, t5, a3
                  slti         a0, s7, 1875
                  c.sub        a0, a3
                  sltu         s2, s3, t4
                  slt          t1, t4, s4
                  srli         s4, a3, 15
                  xori         t0, a7, -682
                  mul          a7, t1, s6
                  xor          s10, s11, t6
                  c.addi4spn   s1, sp, 464
                  xori         s7, t6, -783
                  c.xor        a5, a1
                  c.addi       s8, 16
                  mulhu        t4, sp, s2
                  sra          tp, t1, a6
                  c.addi4spn   a2, sp, 176
                  mulhsu       gp, a2, s5
                  c.addi4spn   a2, sp, 64
                  slti         t3, zero, -1191
                  c.slli       t6, 25
                  c.srai       a5, 30
                  andi         sp, s3, -1383
                  c.or         s1, a1
                  c.addi16sp   sp, 448
                  nop
                  divu         a5, ra, ra
                  c.slli       a2, 27
                  mulh         t0, s10, t2
                  divu         s2, s5, s0
                  c.addi16sp   sp, -16
                  sltu         s9, s11, a2
                  c.add        sp, a0
                  slli         s11, sp, 7
                  slti         s4, s6, -1872
                  c.lui        a7, 1
                  divu         t5, s9, a4
                  div          s1, sp, a7
                  srli         s7, s5, 1
                  sltiu        s10, s4, 850
                  li           t4, 0x80000000 #start riscv_int_numeric_corner_stream_16
                  li           s4, 0x754dd705
                  li           s3, 0xffffffff
                  li           a6, 0x90a30809
                  li           a5, 0x80000000
                  li           s2, 0xffffffff
                  li           s1, 0xffffffff
                  li           t5, 0xfd946005
                  li           s7, 0x3fc7a7c4
                  li           a0, 0x4211946a
                  div          a0, t4, a0
                  remu         s2, t5, t4
                  nop
                  rem          s2, a0, a0
                  mulh         a6, a5, a6
                  nop
                  divu         t5, s4, s3
                  rem          s7, s4, s3
                  add          a6, s2, a0
                  divu         a5, a0, s2
                  div          s3, a0, t4
                  nop
                  lui          a5, 549478
                  mulh         a5, s2, s3
                  sub          t4, t4, s7
                  remu         s7, s7, a0
                  nop
                  add          s7, t5, s2
                  mulh         s4, a0, s4
                  divu         s4, s4, s2
                  add          a6, a6, a6
                  nop
                  auipc        a6, 353967
                  lui          a6, 57636
                  sub          s1, s4, s2
                  sub          s2, a6, a5 #end riscv_int_numeric_corner_stream_16
                  xor          a6, s3, a2
                  rem          a3, s11, s6
                  srai         s0, a0, 20
                  c.addi4spn   a0, sp, 912
                  c.addi       s11, -1
                  c.nop
                  c.or         s1, s0
                  c.addi4spn   s1, sp, 320
                  c.srai       s1, 1
                  xori         s1, s9, 501
                  c.li         a6, -1
                  mulh         a2, s3, ra
                  addi         gp, a6, 1197
                  andi         t6, s10, -2029
                  mul          zero, a2, a1
                  sltiu        s1, t5, -1688
                  c.or         s1, a2
                  auipc        tp, 406945
                  c.addi4spn   a2, sp, 352
                  mulhsu       a6, s1, ra
                  c.li         s2, -1
                  sub          t6, s4, t2
                  c.nop
                  mulhu        s3, s6, t1
                  c.add        a7, s2
                  mulh         s8, a1, s11
                  xori         t1, a3, 1598
                  sltu         a5, a1, a1
                  srli         s1, sp, 9
                  add          t3, a6, s10
                  srai         s2, tp, 23
                  auipc        s4, 456532
                  and          t3, s0, s4
                  c.addi16sp   sp, -16
                  sltiu        a0, s10, -1061
                  andi         s1, sp, 1660
                  c.lui        a6, 11
                  c.add        t0, a5
                  sll          zero, a5, s2
                  slti         s5, t1, -75
                  c.srai       s1, 28
                  sub          s2, tp, t2
                  sub          a0, s5, s1
                  addi         a0, zero, -1028
                  c.addi4spn   s1, sp, 816
                  c.addi4spn   s1, sp, 896
                  slli         t6, t6, 9
                  remu         a0, a6, s4
                  and          a3, s1, a4
                  c.xor        a3, a0
                  mulhu        t1, s0, gp
                  nop
                  and          t3, s6, a6
                  c.andi       a3, 13
                  xor          s8, a7, s10
                  and          t5, a0, a2
                  c.sub        a2, a2
                  andi         t5, sp, 1086
                  or           s5, t3, zero
                  srai         s3, t1, 8
                  srli         t6, ra, 28
                  auipc        a2, 300708
                  c.and        s1, s0
                  c.srai       a5, 29
                  c.srli       a0, 31
                  sltiu        a3, t3, -1896
                  sra          s4, a1, t5
                  srl          s2, tp, a4
                  remu         s5, t0, a2
                  c.andi       a2, -1
                  sltu         a7, t6, s5
                  mulhsu       t3, s7, a0
                  add          s7, t5, s6
                  rem          s0, s7, s0
                  add          t3, s5, a0
                  slli         s2, s8, 23
                  c.xor        a2, a5
                  c.srli       a3, 27
                  srli         a7, t3, 28
                  c.nop
                  sll          s7, s9, t0
                  c.andi       a3, 20
                  srli         s1, t2, 13
                  xor          s2, zero, s4
                  mulhsu       s11, s5, s10
                  mulhsu       s9, s6, s7
                  c.addi4spn   a3, sp, 368
                  mulh         a6, s1, t4
                  mul          s10, ra, a3
                  c.add        s1, gp
                  xori         a5, t4, 404
                  srli         t5, s3, 17
                  andi         zero, sp, 421
                  c.xor        a0, a2
                  c.lui        t6, 8
                  ori          s3, t3, 1908
                  c.addi       a0, -1
                  remu         gp, t2, a7
                  c.srli       s1, 18
                  c.or         a0, a4
                  c.or         a3, s1
                  or           s3, tp, s2
                  add          s7, s7, a0
                  li           s5, 0x80000000 #start riscv_int_numeric_corner_stream_1
                  li           s0, 0xffffffff
                  li           gp, 0xffffffff
                  li           a2, 0xffffffff
                  li           s2, 0x97e89765
                  li           s10, 0x0
                  li           a5, 0xbb318caa
                  li           t1, 0x80000000
                  li           t3, 0xffffffff
                  li           t5, 0x0
                  lui          a5, 80284
                  nop
                  nop
                  divu         s5, s0, t3
                  lui          t5, 391507
                  sub          t1, gp, a2
                  divu         s5, a5, a2
                  mulh         a2, t1, t1
                  rem          a2, t1, a5
                  lui          t5, 91565
                  sub          a5, s0, s5
                  mulhu        t1, t5, s10
                  add          a5, gp, s0
                  mul          t3, s2, s5
                  add          s10, s0, s5
                  div          a2, s10, t3
                  mulh         t5, s0, t5
                  mulhsu       s5, s2, t1
                  mulhsu       gp, a2, s2
                  lui          s5, 1048454
                  rem          t1, s2, s0 #end riscv_int_numeric_corner_stream_1
                  auipc        s1, 792446
                  nop
                  or           t5, s8, zero
                  c.or         a5, a5
                  mulh         zero, ra, ra
                  mulhu        s8, a7, s8
                  srli         ra, t2, 31
                  srli         a2, s0, 0
                  c.srai       a2, 9
                  c.slli       a2, 22
                  c.addi16sp   sp, -16
                  slli         t4, a6, 17
                  slt          gp, a5, s5
                  remu         t1, s7, s5
                  c.add        sp, s4
                  srl          tp, s10, tp
                  andi         s5, s2, 1055
                  c.nop
                  xori         s9, s10, 166
                  xori         t0, ra, 203
                  ori          a0, t1, 1183
                  mul          t3, s9, a6
                  c.addi16sp   sp, -16
                  sub          t6, a5, tp
                  lui          tp, 26673
                  auipc        s1, 982296
                  c.and        s0, s0
                  c.add        tp, s8
                  sltiu        s8, gp, -628
                  xor          t2, a0, s8
                  remu         t6, a1, s0
                  slt          t3, s1, a3
                  mulhu        s11, a1, sp
                  ori          ra, s0, 1018
                  mulhsu       tp, t1, t2
                  or           s5, s11, a2
                  c.mv         sp, gp
                  add          s2, t5, s3
                  srl          t6, s3, s5
                  slli         sp, s0, 2
                  c.addi       a0, 11
                  c.addi       s10, -1
                  c.or         s0, a5
                  slt          s7, zero, t5
                  srl          gp, s5, s5
                  add          a5, s7, ra
                  mul          s11, s1, s3
                  ori          t5, gp, 998
                  c.lui        t5, 24
                  andi         tp, s3, -978
                  sub          ra, t2, a4
                  c.xor        a5, s0
                  sub          sp, a3, s1
                  sll          s3, s10, s5
                  c.nop
                  sra          t2, a2, s8
                  c.srli       a2, 10
                  slti         a0, zero, -1145
                  c.addi16sp   sp, -16
                  c.li         a0, 18
                  and          s9, s2, s5
                  c.li         a5, 23
                  srl          t2, t2, a4
                  auipc        a5, 135218
                  c.nop
                  slti         a3, a7, -123
                  div          a2, s4, s8
                  c.lui        t5, 6
                  c.xor        a0, a0
                  sra          s3, s6, s5
                  sll          s10, t6, s8
                  c.andi       s0, 1
                  c.li         sp, -1
                  c.add        ra, s2
                  c.xor        a0, a4
                  c.addi       t1, -1
                  sra          ra, s10, sp
                  c.and        a0, a0
                  sltu         a5, sp, t3
                  c.lui        gp, 16
                  andi         t2, t6, 224
                  sub          a7, s2, zero
                  rem          tp, a4, t4
                  auipc        a2, 729660
                  c.addi       s7, 19
                  c.andi       a5, -1
                  c.slli       s7, 18
                  srl          tp, a2, a5
                  c.andi       a3, -1
                  c.srai       s0, 17
                  li           t1, 0x54162771 #start riscv_int_numeric_corner_stream_25
                  li           t3, 0x76fa2703
                  li           t4, 0x0
                  li           a6, 0xffffffff
                  li           s5, 0x0
                  li           s9, 0x80000000
                  li           s10, 0x0
                  li           s3, 0xcaffbce2
                  li           a0, 0x31c21fa3
                  li           sp, 0x80000000
                  nop
                  addi         t3, sp, 1374
                  div          s3, sp, s10
                  addi         a0, s5, 761
                  div          a6, s9, t3
                  rem          t3, sp, sp
                  mul          t1, a6, t4
                  auipc        s5, 1006984
                  mulhsu       t1, s9, sp
                  mulhsu       s10, t1, s9
                  rem          t3, t4, sp
                  mulhu        t1, s5, s9
                  sub          a6, a0, a0
                  nop
                  mulhsu       s10, t1, s3
                  mulh         s3, s10, t1
                  mulhu        sp, s9, t4
                  div          sp, t4, s5
                  remu         t1, sp, s10
                  mulhu        s9, t4, t3
                  divu         t4, t1, a6
                  remu         s9, s5, a0
                  remu         s9, t1, t1
                  add          t1, sp, t3
                  sub          sp, t3, s5
                  div          s10, t3, a6
                  sub          s10, s3, t1
                  mul          s5, t3, s3
                  mulhu        t4, s5, sp
                  remu         sp, s5, t3 #end riscv_int_numeric_corner_stream_25
                  c.add        s5, t5
                  auipc        t1, 872385
                  lui          s3, 334690
                  c.add        ra, s8
                  mulhsu       gp, s1, ra
                  addi         a6, t4, 955
                  c.slli       s0, 1
                  sltu         s7, a1, t5
                  c.srli       a0, 12
                  c.or         a2, a0
                  auipc        s8, 32099
                  mulhsu       gp, s8, tp
                  sll          ra, t3, a2
                  c.and        s0, a2
                  c.nop
                  sll          gp, tp, a7
                  c.slli       t5, 8
                  c.li         s10, -1
                  auipc        a6, 766893
                  c.add        t3, t4
                  sll          t3, a1, gp
                  c.lui        a6, 14
                  mulhu        t1, t1, s11
                  slt          zero, a2, a7
                  c.srli       a5, 24
                  c.li         s7, 11
                  c.mv         a6, gp
                  or           a2, zero, t1
                  andi         sp, s0, -1641
                  sub          a3, a5, a2
                  or           s5, a5, sp
                  xori         s2, s6, -1450
                  andi         t1, a0, 1169
                  c.li         s0, 31
                  c.mv         a0, a0
                  ori          t5, a7, 417
                  addi         t0, t1, 1216
                  c.nop
                  c.srai       s0, 30
                  c.li         t3, -1
                  mulhu        a6, s7, t2
                  sll          t4, s4, s9
                  c.li         a5, -1
                  c.andi       s1, 21
                  c.andi       s1, -1
                  div          s5, t3, t4
                  sltiu        t5, sp, -1377
                  c.sub        a0, a1
                  andi         t5, gp, 1680
                  c.addi       s7, 31
                  c.xor        a2, a4
                  c.and        s0, s1
                  mulhsu       t1, a5, s0
                  auipc        s2, 671651
                  c.srai       s0, 6
                  divu         zero, s2, a5
                  c.nop
                  mulhu        ra, a0, s0
                  c.srli       s1, 21
                  mulhu        a5, s11, s2
                  nop
                  remu         tp, s8, a6
                  sra          t5, ra, s7
                  c.addi4spn   s0, sp, 64
                  c.srli       s0, 30
                  add          a7, s3, a3
                  mulhsu       s0, ra, sp
                  c.addi4spn   a0, sp, 592
                  c.addi4spn   s0, sp, 272
                  c.srai       a0, 26
                  andi         a6, s8, 839
                  c.slli       t3, 14
                  srai         sp, t2, 30
                  mul          t5, t2, a0
                  c.and        s0, a3
                  c.add        a7, a4
                  c.sub        s0, a3
                  srai         a5, t2, 11
                  srai         t4, a0, 19
                  c.addi4spn   s0, sp, 416
                  c.add        s8, tp
                  auipc        t0, 510729
                  c.slli       s1, 17
                  c.lui        s1, 13
                  c.slli       s7, 31
                  slt          s0, s4, sp
                  c.add        a2, a6
                  or           s3, s2, a0
                  srai         s2, a5, 23
                  mul          a3, t5, s5
                  nop
                  ori          s11, t3, 25
                  srl          t4, t0, tp
                  or           a0, t2, s0
                  srli         s11, t3, 3
                  sll          sp, zero, t3
                  c.lui        a0, 24
                  sll          t0, t6, t6
                  srl          t1, s9, t5
                  mulhsu       a7, s1, t6
                  c.and        a3, a1
                  c.li         s5, -1
                  c.add        s2, s3
                  lui          t4, 296834
                  c.nop
                  remu         a5, a1, a0
                  sll          s8, t2, s7
                  c.li         a2, 6
                  addi         s2, ra, -302
                  add          s11, gp, sp
                  c.add        s4, sp
                  div          a3, gp, s6
                  sll          ra, a7, t6
                  srli         zero, s7, 9
                  xori         a7, t3, 1743
                  add          a3, t2, t3
                  slt          tp, t1, a0
                  andi         t6, zero, -626
                  c.mv         t6, s10
                  ori          a5, t6, 407
                  c.xor        a3, a3
                  and          t4, a1, s5
                  slti         s4, t5, -1452
                  slti         s3, t3, 923
                  c.li         a6, 23
                  c.andi       a0, -1
                  c.addi4spn   a2, sp, 608
                  c.addi16sp   sp, -16
                  divu         sp, t3, t4
                  auipc        s10, 281245
                  c.addi       ra, 12
                  c.mv         s1, t4
                  add          a5, s8, s5
                  srai         a0, t5, 8
                  c.mv         sp, s9
                  slti         sp, a7, -524
                  andi         s8, t6, 1619
                  c.nop
                  ori          a7, a4, 684
                  lui          t5, 553653
                  c.and        a5, a3
                  c.or         a0, a1
                  xori         t1, t0, 845
                  mulh         a0, s7, s3
                  mul          t5, a0, a3
                  c.xor        s1, a5
                  sltu         zero, s1, a6
                  c.slli       s3, 11
                  srli         t3, a6, 18
                  sll          s0, tp, t4
                  mulh         t6, zero, t1
                  c.addi4spn   s0, sp, 176
                  andi         tp, a5, 1854
                  c.srli       a0, 11
                  c.mv         a7, a3
                  c.srai       a2, 6
                  c.addi16sp   sp, -16
                  andi         s4, a0, 952
                  or           a2, a0, s10
                  mul          tp, sp, s5
                  add          s11, t4, s7
                  c.or         a3, a4
                  mulh         s5, zero, t0
                  srai         t2, tp, 11
                  sll          s2, t6, t5
                  c.srai       a5, 21
                  slt          t4, a7, s11
                  c.srli       a3, 5
                  or           tp, s3, s9
                  nop
                  slt          s2, t5, t5
                  sll          s5, t4, s3
                  sltiu        s7, t5, -604
                  slt          t2, s10, t2
                  sub          a2, t0, tp
                  c.slli       a6, 10
                  c.mv         s3, t1
                  ori          s10, s4, 1683
                  c.mv         t6, ra
                  auipc        gp, 900883
                  sub          t5, tp, t0
                  nop
                  mulhsu       zero, a2, a5
                  srli         a7, s11, 26
                  srl          gp, tp, a2
                  or           t0, s10, t0
                  mulhu        t3, s7, a3
                  c.sub        s0, a1
                  slli         gp, a5, 17
                  mul          t4, t0, t2
                  mul          a6, t2, t5
                  rem          s0, s3, s2
                  c.addi4spn   a0, sp, 288
                  sltu         tp, t4, ra
                  sub          s5, s4, s4
                  c.srai       s1, 18
                  slt          s10, a0, s4
                  c.addi4spn   a5, sp, 352
                  lui          t3, 344774
                  c.or         a0, a2
                  mul          gp, a4, a0
                  div          t3, a4, s1
                  c.add        gp, s1
                  c.slli       ra, 10
                  mulhsu       s9, s2, s5
                  nop
                  slli         a3, s10, 12
                  c.srli       a3, 19
                  srl          s9, sp, a7
                  c.nop
                  slli         t0, a2, 19
                  addi         gp, a7, 1711
                  c.slli       t2, 22
                  slt          s3, t4, s8
                  c.xor        a3, a4
                  or           ra, s7, s1
                  c.addi16sp   sp, 16
                  c.addi4spn   a0, sp, 416
                  div          a0, a2, t1
                  srl          t4, t4, s11
                  or           s9, t3, t3
                  xor          s4, sp, t3
                  srli         s5, s11, 29
                  c.sub        a0, a2
                  nop
                  sltiu        s3, s9, -1418
                  mulh         t4, t1, t2
                  add          t1, t5, a4
                  slti         s2, a7, 1019
                  add          s9, a4, s1
                  sub          gp, a5, a4
                  c.addi       s8, 1
                  mul          s7, t5, gp
                  sltiu        s4, t2, -1415
                  slti         a2, s7, 1119
                  c.or         a0, s0
                  xori         a6, t2, 423
                  sltu         t6, s7, s7
                  andi         sp, s6, 187
                  c.and        s1, a4
                  divu         s10, a3, zero
                  andi         a7, a1, 325
                  sra          t2, t3, gp
                  sra          s0, s6, s5
                  c.addi16sp   sp, 400
                  mulhsu       s7, a4, s10
                  li           s11, 0x80000000 #start riscv_int_numeric_corner_stream_2
                  li           tp, 0xffffffff
                  li           s2, 0xffffffff
                  li           a5, 0x80000000
                  li           t6, 0x0
                  li           t0, 0x19313e63
                  li           s0, 0xffffffff
                  li           a7, 0x80000000
                  li           s5, 0x0
                  li           s1, 0xffffffff
                  mulh         s0, t0, s11
                  rem          a5, s1, s2
                  mulhu        s11, s0, s1
                  nop
                  nop
                  sub          a5, s11, a5
                  div          a7, s5, t6
                  sub          s2, s0, a5
                  divu         a7, t6, t6
                  divu         t6, a5, s11
                  lui          s2, 850289
                  add          a5, a7, tp
                  add          t0, tp, s11
                  nop
                  auipc        s11, 596017
                  remu         s1, a7, a7
                  divu         s1, s1, a7
                  mulh         s2, tp, s0
                  addi         tp, t6, 1918
                  sub          s5, t0, t6
                  mulhu        s5, s2, t0
                  mul          t0, a5, t6 #end riscv_int_numeric_corner_stream_2
                  mul          ra, a5, a4
                  c.li         t1, -1
                  c.sub        a0, a0
                  li           t4, 0x0 #start riscv_int_numeric_corner_stream_17
                  li           t5, 0x0
                  li           t2, 0x80000000
                  li           s10, 0x0
                  li           sp, 0x2e32aab6
                  li           s8, 0x80000000
                  li           t1, 0xffffffff
                  li           a3, 0xffffffff
                  li           a2, 0x0
                  li           t3, 0x0
                  div          a3, a3, a2
                  remu         t3, sp, sp
                  mulhsu       t2, sp, t5
                  mulhsu       t4, t4, t4
                  mulh         a3, t3, sp
                  nop
                  nop
                  add          t5, t3, sp
                  lui          t1, 351420
                  sub          sp, t2, t4
                  rem          s8, a3, s10
                  addi         t4, t1, 1247
                  lui          t5, 21707
                  mulh         t4, t5, sp
                  nop
                  mulhu        s8, t2, a2
                  rem          t4, t5, t3 #end riscv_int_numeric_corner_stream_17
                  divu         a2, a0, s0
                  c.nop
                  addi         s1, t2, 1029
                  slti         a3, s3, 1575
                  c.srai       a5, 9
                  c.addi       gp, -1
                  c.add        a3, gp
                  div          s1, a7, gp
                  slti         a7, s8, 270
                  mul          a3, s2, s0
                  andi         t0, sp, 137
                  divu         sp, t5, zero
                  auipc        t6, 884367
                  c.mv         a3, t0
                  c.nop
                  sll          a6, a7, t5
                  or           s8, a5, a7
                  srli         gp, sp, 5
                  mulhsu       s1, s6, gp
                  nop
                  c.li         t0, -1
                  rem          a3, a0, ra
                  or           s10, s3, s11
                  sra          t6, a1, t4
                  c.nop
                  srl          zero, tp, a1
                  slli         a7, zero, 13
                  c.srli       s1, 12
                  slli         s4, a0, 20
                  c.andi       a5, -1
                  slti         zero, gp, 844
                  addi         t1, t6, -471
                  or           s4, s8, s1
                  sltu         s4, s0, t2
                  rem          t3, a6, s7
                  sra          t0, a3, s7
                  andi         s0, s9, -569
                  c.sub        a5, a1
                  srai         sp, s2, 0
                  c.srli       a3, 28
                  addi         s9, zero, -380
                  slli         t6, s2, 25
                  mul          s5, s11, s10
                  addi         s4, a1, -1450
                  slti         s1, t6, -1572
                  mulhsu       s8, t2, a7
                  c.addi16sp   sp, -16
                  div          t3, s9, sp
                  c.nop
                  mulh         a0, a2, t2
                  c.slli       tp, 13
                  srl          t4, s8, s8
                  slli         a5, t2, 5
                  sub          tp, a3, ra
                  div          s4, s5, s0
                  mul          s1, s4, ra
                  c.addi16sp   sp, 256
                  srli         t4, t0, 23
                  slti         s5, t5, -1083
                  mulhsu       sp, s11, s4
                  c.xor        s1, a5
                  mulhu        s3, s4, s2
                  remu         a6, s0, a1
                  mulhu        s9, t2, s3
                  xori         s8, s1, 2006
                  c.lui        s7, 27
                  c.nop
                  mulhu        t1, t4, a7
                  c.mv         s2, a1
                  auipc        s8, 608349
                  rem          t3, s1, s2
                  c.mv         s2, t6
                  srai         s4, s2, 25
                  sra          a3, a0, t4
                  or           t2, s10, a4
                  slli         t5, s7, 1
                  c.addi16sp   sp, 384
                  c.xor        a5, a2
                  c.xor        a3, a4
                  auipc        s10, 679157
                  c.mv         t1, s7
                  and          s3, t6, a4
                  c.nop
                  c.and        a3, a2
                  c.add        s5, t2
                  sltu         s3, a2, s6
                  slt          a2, a2, gp
                  mulh         a6, t4, s9
                  remu         t5, t2, s3
                  c.andi       a5, -1
                  sltiu        a2, t4, 1263
                  srl          sp, s0, s7
                  c.srai       s1, 25
                  srai         t4, a3, 16
                  c.and        a2, a5
                  xor          a3, a4, a5
                  xori         t5, s7, -394
                  c.addi       s4, 28
                  mul          sp, t0, s9
                  slti         s9, s10, -1982
                  c.xor        a2, a5
                  or           s9, a3, t3
                  sra          s8, a4, s11
                  srli         a7, s7, 22
                  xor          t5, a3, t2
                  c.sub        a5, s1
                  mulhu        tp, zero, a6
                  c.or         s0, a2
                  c.addi       tp, 18
                  srai         s11, a2, 23
                  c.and        s0, a4
                  auipc        zero, 9333
                  div          s10, zero, s3
                  c.srai       s1, 6
                  mulh         s5, zero, a6
                  sub          a7, ra, ra
                  divu         t3, t2, s11
                  c.slli       s1, 2
                  c.srli       a2, 10
                  sltiu        t4, sp, -1000
                  add          s1, t0, a6
                  mulh         a7, t6, s2
                  c.slli       s10, 18
                  slt          t4, a3, a1
                  c.addi       tp, -1
                  c.sub        s0, a4
                  c.lui        s10, 5
                  remu         a3, t0, zero
                  slli         s11, t3, 6
                  andi         t4, s4, 1839
                  c.addi4spn   s1, sp, 432
                  mulhu        a5, s1, a3
                  divu         a5, s3, t4
                  c.andi       a3, 3
                  c.lui        s7, 17
                  addi         t1, s6, -1617
                  addi         t3, t6, -56
                  c.or         s1, a1
                  rem          s9, gp, s8
                  c.nop
                  slti         tp, gp, -978
                  slt          a0, t1, s0
                  xor          s1, s6, a2
                  c.addi16sp   sp, 64
                  c.and        a0, a3
                  c.and        a5, s1
                  sltiu        t6, s1, -993
                  c.addi4spn   s1, sp, 352
                  xori         a2, s9, -250
                  c.or         a0, a0
                  c.or         s0, a0
                  c.xor        s1, a2
                  and          ra, s4, a3
                  sra          s11, t6, s8
                  c.addi       s1, 14
                  c.xor        s1, a2
                  sll          s11, gp, a5
                  remu         s8, a0, t2
                  c.add        s5, t6
                  auipc        tp, 500994
                  add          s0, s11, zero
                  sltiu        a7, t3, -1526
                  c.srli       a3, 31
                  c.or         a2, a1
                  c.nop
                  srli         gp, t6, 9
                  andi         s3, a2, 872
                  sltiu        s8, s11, 1550
                  c.add        s10, s4
                  c.and        a5, a1
                  c.lui        s7, 28
                  mulh         s0, t4, s2
                  sub          t1, t0, t5
                  slt          t0, s10, s2
                  c.srai       a2, 15
                  c.xor        a0, s0
                  sltiu        s4, a4, 2036
                  mulh         gp, a1, s1
                  c.sub        a3, a4
                  sll          a3, a7, s8
                  c.addi4spn   s1, sp, 96
                  slt          t1, t3, a7
                  addi         s1, s4, -1899
                  sltu         s2, s6, t1
                  sll          s3, a7, s10
                  divu         tp, a7, a0
                  c.nop
                  sltiu        a5, t4, 65
                  auipc        t1, 1028958
                  rem          tp, t0, s4
                  rem          zero, zero, s2
                  rem          a6, t6, t4
                  sra          s5, s10, t0
                  srai         t4, s7, 13
                  divu         a7, t3, sp
                  c.add        tp, t1
                  lui          t4, 334067
                  c.mv         s11, t6
                  slli         sp, s11, 31
                  sub          t0, t3, t2
                  c.sub        a2, a4
                  divu         tp, s11, a2
                  srl          a6, t1, s3
                  c.add        s8, s0
                  auipc        s9, 529367
                  div          s0, s9, a0
                  and          tp, ra, a7
                  lui          a0, 166756
                  c.addi16sp   sp, 432
                  andi         t0, zero, -1460
                  lui          t6, 585966
                  slti         s11, a1, -962
                  c.nop
                  andi         t6, s3, -1639
                  c.sub        a0, a5
                  srli         t6, t5, 28
                  c.nop
                  sub          s10, t5, t0
                  c.lui        a0, 19
                  divu         s2, s8, t5
                  c.nop
                  c.lui        gp, 21
                  xor          tp, t3, t6
                  c.addi16sp   sp, 224
                  c.mv         a6, t2
                  srli         t5, sp, 28
                  slti         s0, s4, -590
                  mul          s7, a7, sp
                  c.sub        s0, a1
                  c.srli       s0, 11
                  c.addi       t3, 8
                  c.lui        a2, 21
                  sra          a2, t1, s3
                  ori          a0, s3, 321
                  slt          a7, s0, a7
                  xor          s2, t1, a7
                  mulhsu       s0, ra, sp
                  c.srai       a5, 19
                  or           s2, s11, a3
                  sltu         t6, s2, s11
                  and          t6, a7, a1
                  c.li         ra, 2
                  auipc        a0, 796758
                  add          s7, zero, a2
                  c.xor        s0, s1
                  c.addi16sp   sp, 288
                  c.nop
                  sra          sp, s1, s4
                  add          s2, s8, ra
                  and          t5, a4, s1
                  c.or         s0, a2
                  remu         s1, s11, t2
                  sll          s11, a4, t2
                  slli         gp, s10, 12
                  c.slli       s2, 11
                  mulhsu       s3, a6, s0
                  c.mv         t4, a7
                  sltiu        sp, a7, -25
                  c.mv         s3, ra
                  srai         a5, s0, 0
                  c.slli       s2, 31
                  srli         s5, a5, 6
                  xori         gp, s5, -696
                  and          s11, t4, t6
                  add          s0, ra, a1
                  mul          sp, t0, s8
                  slt          ra, t4, s2
                  slli         s3, s3, 28
                  c.addi       s10, 3
                  srli         tp, gp, 0
                  and          s0, s4, a5
                  xor          s8, s6, t4
                  or           t5, zero, a5
                  xor          s7, tp, s4
                  c.slli       t4, 7
                  c.srli       a0, 14
                  c.and        s0, a5
                  slti         t0, ra, -9
                  xor          s2, tp, t1
                  c.and        a3, a2
                  sltiu        s7, s7, 1626
                  srl          a6, a5, a5
                  sub          gp, s1, sp
                  sll          s0, gp, tp
                  sltiu        s0, t0, -1944
                  mul          s1, s2, s1
                  andi         tp, s7, 1693
                  sltu         a6, t5, t2
                  mulhu        s4, s4, s6
                  sra          t3, a5, a0
                  c.addi16sp   sp, 48
                  mul          s9, a6, t3
                  mulh         zero, sp, a7
                  c.mv         s4, s1
                  c.li         s2, 26
                  slli         s7, s6, 13
                  ori          a5, s7, 831
                  c.or         a0, a1
                  nop
                  addi         t5, s9, -920
                  srai         t5, t3, 29
                  slli         t4, gp, 26
                  c.add        s8, s6
                  andi         ra, s9, -1023
                  c.xor        a5, a2
                  and          ra, a6, a1
                  c.addi16sp   sp, -16
                  c.addi4spn   a3, sp, 64
                  mulhu        a7, s1, s3
                  slti         t5, s5, 1711
                  slti         t1, t4, -1179
                  slti         s4, s5, 1733
                  c.li         t6, 16
                  auipc        s2, 209667
                  nop
                  nop
                  nop
                  xori         a0, s7, 666
                  c.srai       a5, 11
                  xori         s2, tp, 1546
                  sll          s4, t5, a2
                  c.addi16sp   sp, -16
                  or           s4, s10, s0
                  sltu         t5, a7, t5
                  sub          s4, s9, gp
                  andi         s2, s2, 420
                  add          a2, t0, t6
                  c.slli       s8, 17
                  remu         a7, a7, a5
                  sltu         gp, s7, s8
                  ori          zero, a4, -269
                  sub          a3, s8, t1
                  sltu         t4, s2, s4
                  slti         t1, a7, 93
                  nop
                  and          ra, s5, tp
                  srli         a0, s4, 2
                  c.srai       s0, 2
                  mulhsu       s5, t0, t1
                  c.add        s5, s5
                  c.andi       a2, -1
                  auipc        a5, 275348
                  c.xor        a5, s0
                  sltu         s1, a2, a0
                  auipc        a5, 97252
                  xori         a5, gp, 1052
                  c.mv         a5, t5
                  divu         s5, zero, t0
                  srl          gp, t0, s0
                  or           a2, s4, s9
                  slli         a0, a2, 29
                  sltiu        s3, s0, -937
                  mulh         s5, t0, a7
                  slt          a3, a6, s8
                  div          s2, t3, t6
                  c.li         t5, 17
                  xor          s9, s4, s1
                  sra          t5, s9, s4
                  sub          t1, t1, a4
                  c.mv         s2, a0
                  c.addi4spn   a0, sp, 656
                  c.srai       a3, 28
                  div          s7, t2, s3
                  lui          a7, 485444
                  c.slli       t1, 28
                  mulhsu       gp, s2, s4
                  mulhsu       gp, s2, s4
                  c.and        a3, a0
                  sll          t6, zero, a7
                  divu         ra, sp, a2
                  sll          sp, s10, s4
                  c.slli       sp, 6
                  c.lui        tp, 29
                  divu         s8, a1, gp
                  auipc        s9, 183473
                  c.lui        s7, 31
                  auipc        t2, 432297
                  addi         s11, s8, 365
                  c.srai       a0, 17
                  c.lui        t0, 20
                  srl          s0, ra, a5
                  andi         gp, a3, 613
                  slli         s0, s1, 16
                  rem          s10, s0, s9
                  c.or         a3, a3
                  srl          s2, s7, a7
                  srli         t5, sp, 16
                  srl          t0, a3, s4
                  mulhsu       t3, s7, s6
                  xori         a3, a1, -1827
                  add          s9, a5, a1
                  divu         a7, t1, s2
                  lui          t3, 995450
                  remu         zero, t1, a7
                  slt          gp, zero, s9
                  c.addi4spn   s1, sp, 640
                  c.slli       gp, 6
                  nop
                  c.srai       a2, 31
                  c.srai       a0, 28
                  slt          ra, sp, s5
                  mulhu        t3, s9, sp
                  c.li         t1, -1
                  xor          s0, s2, s1
                  rem          s9, sp, s1
                  srli         ra, t5, 31
                  c.li         t2, 30
                  andi         s11, s11, -1410
                  slli         t5, t3, 8
                  mul          t5, a5, s1
                  divu         s3, s11, t4
                  xori         a6, t6, -922
                  c.add        s11, a0
                  c.slli       tp, 11
                  c.xor        a0, a1
                  c.andi       a3, -1
                  or           t5, gp, t3
                  c.srli       s0, 14
                  ori          ra, s11, 139
                  c.mv         a3, s3
                  c.xor        a3, a1
                  ori          t4, a0, -1889
                  sll          s2, tp, ra
                  slt          t5, s10, s3
                  mul          a6, s5, s8
                  sll          s10, s3, a0
                  div          t1, tp, sp
                  c.srai       a0, 3
                  c.srai       a3, 2
                  c.sub        a2, a2
                  add          t0, gp, a6
                  mulh         a7, t3, t3
                  slti         s5, s2, 1654
                  c.srai       s1, 21
                  mulh         a6, t2, a6
                  c.srli       s1, 2
                  c.mv         t6, tp
                  lui          s5, 1007528
                  rem          a3, a0, s7
                  c.sub        s1, a0
                  c.nop
                  c.addi16sp   sp, 416
                  c.nop
                  auipc        a7, 376505
                  or           s10, s1, s2
                  add          s5, s7, a5
                  c.li         s11, 10
                  sltiu        s3, t0, -1478
                  sltiu        s7, t0, -1695
                  srli         t0, a0, 4
                  add          a5, s2, t0
                  andi         t6, s8, 1811
                  mulh         gp, a0, t1
                  c.xor        a3, s1
                  c.and        s1, a0
                  srai         s7, s2, 11
                  remu         tp, s8, ra
                  c.slli       a5, 17
                  c.slli       sp, 6
                  srl          tp, t0, s5
                  lui          s0, 411738
                  c.addi4spn   a5, sp, 624
                  slli         a0, ra, 17
                  c.lui        t1, 10
                  sub          s3, sp, gp
                  c.mv         s0, s10
                  c.nop
                  slt          a3, a5, sp
                  c.li         s0, 17
                  andi         s5, s11, 516
                  ori          s5, s4, -1647
                  lui          a6, 878811
                  srl          s11, s3, a5
                  lui          t3, 567488
                  mulhu        sp, a1, s1
                  divu         s2, s5, sp
                  lui          s4, 265148
                  c.addi       a7, -1
                  rem          t2, sp, t6
                  nop
                  srli         zero, a0, 19
                  sltiu        s1, t5, -735
                  remu         a5, t3, s7
                  slt          s3, s4, a4
                  auipc        t5, 604589
                  xori         t5, s8, -374
                  xori         s1, t3, -1841
                  or           s2, s10, a7
                  c.andi       a0, 12
                  slt          t6, s2, t0
                  c.addi4spn   s1, sp, 480
                  srli         t1, zero, 10
                  c.srai       a5, 4
                  c.addi4spn   a5, sp, 64
                  xori         t0, s4, -619
                  srl          t2, s5, a5
                  and          t2, s5, a2
                  sll          a3, t0, t0
                  c.srai       s0, 2
                  srli         s10, s0, 11
                  slt          s2, s10, s11
                  c.addi16sp   sp, -16
                  c.or         a3, a5
                  c.addi       a0, 9
                  slti         a6, s0, -240
                  sra          gp, s7, t6
                  c.mv         s7, t6
                  c.andi       a5, -1
                  c.andi       s1, 16
                  c.srli       a2, 14
                  or           a7, a4, s8
                  divu         s0, zero, s8
                  divu         s1, t1, s5
                  sll          t4, t4, t1
                  c.nop
                  c.or         a2, a1
                  divu         t5, s0, t3
                  sll          a7, a7, s11
                  div          s0, t1, s5
                  and          ra, s6, t3
                  sra          s10, a6, s5
                  sra          ra, t3, s3
                  ori          t3, a2, 346
                  divu         s2, a2, s1
                  sub          a3, gp, s4
                  c.srli       s0, 7
                  c.addi16sp   sp, -16
                  sltu         t3, zero, a4
                  mul          a7, s8, t0
                  c.xor        a2, a4
                  c.srli       a3, 10
                  or           zero, s10, s2
                  c.and        s0, a4
                  nop
                  and          a5, s4, t6
                  sra          a5, s2, s11
                  rem          s9, ra, tp
                  xori         t0, a7, 176
                  srai         t4, s1, 23
                  mulhu        a0, s1, t2
                  mul          s11, s10, t3
                  nop
                  srl          gp, a6, a0
                  c.slli       sp, 15
                  nop
                  slti         t1, a6, 1860
                  c.sub        a2, s1
                  srai         s8, s5, 20
                  c.andi       a2, -1
                  sltu         tp, s2, t6
                  div          a2, t1, a1
                  c.or         a2, a5
                  c.lui        a0, 2
                  or           a6, a0, s4
                  c.lui        a3, 8
                  c.xor        a3, s1
                  sltiu        s8, s8, 1470
                  remu         t1, s2, a3
                  add          a5, s3, s7
                  add          t4, t5, s3
                  div          t2, s7, t1
                  andi         a0, a6, 656
                  slti         s4, a7, 1596
                  andi         t6, tp, 1432
                  mulhu        a5, s2, t3
                  div          s0, t6, gp
                  c.lui        s7, 9
                  c.mv         s7, a6
                  c.srai       s1, 29
                  c.li         t5, -1
                  mulh         s5, a2, s4
                  c.or         a5, a4
                  lui          a6, 535131
                  ori          t2, t0, 1687
                  c.nop
                  sub          s3, s11, s8
                  srl          a6, s9, s11
                  c.slli       s1, 30
                  c.srai       s0, 11
                  c.and        s1, a1
                  nop
                  divu         s2, t0, s11
                  c.or         a5, s1
                  auipc        s9, 173232
                  sll          ra, a5, a7
                  slti         a5, t3, -49
                  sltiu        s10, s0, -1757
                  c.slli       t3, 19
                  div          t3, sp, a1
                  c.slli       tp, 12
                  and          t3, s6, zero
                  addi         t5, t1, 341
                  c.slli       s10, 27
                  c.add        ra, s0
                  ori          s1, s0, -2027
                  slt          s5, s4, a0
                  lui          t1, 34797
                  xor          a0, zero, a0
                  c.and        s0, a1
                  c.andi       s0, 28
                  sltu         a2, s8, ra
                  srai         s0, sp, 20
                  andi         t2, ra, 1074
                  c.add        ra, a3
                  sra          s2, s8, s9
                  lui          s8, 796234
                  c.addi       s1, -1
                  c.lui        a6, 24
                  divu         a0, a3, t5
                  c.and        a5, s1
                  c.and        a0, a2
                  div          t0, ra, a0
                  c.mv         s4, t4
                  xor          ra, s4, a6
                  srai         zero, s2, 11
                  srl          a3, t4, s11
                  slt          gp, sp, t6
                  c.mv         a2, tp
                  srai         a7, s5, 10
                  c.andi       a5, -1
                  slti         t6, t5, -469
                  c.addi4spn   s1, sp, 576
                  c.lui        s9, 14
                  add          a0, t3, s9
                  xor          a5, s0, t0
                  c.lui        a5, 31
                  sltu         t6, s5, s0
                  c.slli       s11, 25
                  c.srli       s0, 7
                  sub          s8, s7, a3
                  c.addi16sp   sp, 32
                  addi         gp, a6, -1837
                  auipc        s4, 308902
                  c.addi4spn   s1, sp, 320
                  srli         t0, s3, 1
                  c.lui        s7, 23
                  c.slli       t6, 11
                  ori          zero, s5, 1229
                  c.addi       s1, 11
                  c.slli       a5, 5
                  c.li         s1, -1
                  c.nop
                  sll          a2, t3, s9
                  c.andi       a5, -1
                  c.add        sp, s0
                  sltiu        a3, a4, -1917
                  c.or         a3, s0
                  srli         t1, sp, 5
                  srli         s4, s8, 7
                  sltu         t3, t4, t5
                  c.lui        t0, 26
                  sll          ra, t1, a6
                  mulhsu       s4, s3, a5
                  c.li         t3, -1
                  add          s10, t1, s4
                  auipc        s1, 657892
                  c.xor        a5, a4
                  c.andi       a3, -1
                  c.addi16sp   sp, 176
                  andi         t2, gp, 1307
                  c.addi16sp   sp, -16
                  c.xor        a2, a3
                  addi         a0, zero, -595
                  mul          t0, s1, s11
                  srai         a7, s4, 10
                  lui          sp, 697296
                  srl          gp, s9, a3
                  c.or         s0, a3
                  sub          zero, s5, s5
                  srai         s8, s5, 26
                  remu         s2, s10, a7
                  c.addi       s5, 18
                  c.addi4spn   s0, sp, 688
                  nop
                  srli         t3, t0, 3
                  or           ra, s8, t2
                  mulhsu       a7, s8, zero
                  c.add        a7, t5
                  nop
                  sra          gp, zero, s8
                  or           s11, tp, t1
                  c.or         s0, s1
                  c.andi       a3, 26
                  c.addi       tp, -1
                  rem          t3, s1, t1
                  xor          t6, s5, t3
                  c.mv         ra, a1
                  and          tp, t4, s4
                  sltu         s10, a4, t3
                  c.and        a0, a3
                  mulh         a7, t1, t0
                  div          t3, ra, sp
                  nop
                  srai         s11, s3, 15
                  ori          a7, a5, 1513
                  c.nop
                  div          a5, s6, s4
                  c.xor        a2, a5
                  mulh         t6, t2, s1
                  sll          a2, a6, s5
                  c.li         a2, 26
                  c.slli       a5, 19
                  c.and        a3, s1
                  sra          t6, s2, t2
                  sub          t0, s2, t4
                  mul          t0, t6, a3
                  andi         s2, zero, -202
                  addi         s9, a0, -1110
                  sll          a0, a4, s10
                  nop
                  ori          s3, a0, -307
                  xori         zero, t0, 1044
                  c.xor        a0, s1
                  sll          a7, s10, s10
                  sltiu        zero, a3, 471
                  sub          s3, s8, a0
                  xori         s9, zero, 786
                  c.addi16sp   sp, -16
                  mulhu        s1, t1, t3
                  addi         s11, a5, -207
                  nop
                  mulhu        t4, s2, s9
                  ori          t1, s0, -1880
                  c.mv         a3, s6
                  mulhu        t2, t1, s0
                  c.or         s0, a5
                  sltiu        a5, a5, -1538
                  andi         ra, s4, 1467
                  nop
                  ori          a5, sp, 640
                  rem          s11, t4, a1
                  mulh         ra, a1, gp
                  mulhu        s2, a0, s2
                  addi         a0, zero, -1360
                  mulhsu       s1, t2, s9
                  sltiu        a5, s6, -1298
                  c.nop
                  slti         s3, s2, 1798
                  sltiu        t1, tp, -873
                  sltiu        s9, a4, -57
                  srai         t0, sp, 19
                  nop
                  remu         sp, s8, tp
                  c.add        t6, t5
                  c.addi4spn   a3, sp, 336
                  xor          sp, s0, t6
                  c.andi       s0, -1
                  c.sub        s0, a3
                  c.nop
                  slti         s9, t2, 2007
                  c.slli       s3, 1
                  c.add        t6, a4
                  divu         zero, t2, t3
                  remu         a2, t6, s4
                  remu         a0, a5, sp
                  c.srai       a0, 17
                  c.or         s0, a5
                  or           zero, s10, s0
                  mulh         a6, zero, s1
                  sra          s5, t3, s2
                  c.andi       s0, -1
                  mul          t1, t6, s11
                  rem          a5, t5, t1
                  c.srli       a3, 13
                  mulh         s3, t3, zero
                  divu         a3, t0, t4
                  slti         t2, t0, -703
                  div          s8, s6, a0
                  c.nop
                  c.mv         t4, t5
                  sra          s7, t4, s10
                  sra          gp, a3, tp
                  ori          a0, a6, -1675
                  remu         t4, t2, a3
                  or           t4, t5, sp
                  srl          s9, s5, s4
                  srai         t1, a4, 21
                  c.or         a5, a5
                  mulhu        sp, s3, t4
                  remu         t1, s8, tp
                  c.addi16sp   sp, -16
                  c.xor        a2, a0
                  sra          tp, a3, s11
                  c.xor        a5, a1
                  rem          a3, gp, a2
                  auipc        a6, 773147
                  andi         t4, a6, 656
                  mulhsu       s0, a4, s7
                  ori          a5, a0, -1186
                  c.xor        a5, a0
                  add          t6, t4, a6
                  sltu         s0, gp, s1
                  c.addi       tp, 28
                  c.lui        t5, 31
                  mul          a2, s9, a4
                  c.addi16sp   sp, 272
                  auipc        s11, 105739
                  c.andi       s0, 0
                  c.li         a5, 1
                  slli         t5, s0, 8
                  c.srai       s1, 25
                  c.add        a5, tp
                  srl          t5, t4, tp
                  c.srli       s0, 25
                  c.srli       s1, 3
                  ori          zero, t1, 1247
                  auipc        t1, 892178
                  or           a7, t3, s5
                  xor          s4, zero, a7
                  divu         t5, s3, s6
                  remu         t2, a0, t3
                  mulhsu       s4, t6, a4
                  slt          s4, s11, a7
                  c.slli       a5, 22
                  c.srai       s1, 3
                  addi         a5, t0, -1000
                  slli         s10, s6, 5
                  c.and        a2, a0
                  c.srli       a2, 13
                  c.li         s0, -1
                  c.or         s1, a4
                  sra          t4, t3, a6
                  nop
                  remu         t1, t1, tp
                  mulh         gp, s9, a2
                  xor          t2, s7, a1
                  c.and        s1, s0
                  or           s11, a1, zero
                  sltiu        t2, s8, 1180
                  mul          a0, s11, t3
                  mulhu        t3, t0, ra
                  ori          s8, gp, -924
                  c.mv         a5, s7
                  xor          a7, a7, a6
                  c.andi       s1, -1
                  sltiu        a7, t1, 1311
                  c.srli       a2, 8
                  c.slli       tp, 18
                  sub          s3, t0, a1
                  c.or         a0, a0
                  c.nop
                  lui          s11, 512141
                  mulh         s0, tp, tp
                  c.addi16sp   sp, -16
                  mul          s8, zero, t2
                  nop
                  c.and        a0, a4
                  sub          s1, t5, t5
                  mulhsu       a2, a3, s8
                  c.addi       gp, -1
                  sltu         t0, t4, t1
                  lui          gp, 625932
                  xori         t4, s8, -624
                  c.nop
                  c.slli       a5, 9
                  c.srai       a2, 16
                  or           t4, a3, t1
                  c.lui        a0, 14
                  c.add        s0, s11
                  addi         s8, s4, -855
                  remu         ra, zero, s5
                  srai         t6, t1, 7
                  divu         sp, t3, s0
                  c.lui        a5, 28
                  c.li         a2, 17
                  c.addi4spn   s0, sp, 560
                  srl          t5, s9, s11
                  or           s9, s11, t5
                  c.mv         s3, t0
                  div          s5, s9, sp
                  c.add        t0, a7
                  or           t1, tp, t3
                  div          a0, s0, s9
                  addi         tp, s8, -1955
                  c.addi4spn   a3, sp, 320
                  c.addi       ra, 27
                  srl          s1, s8, s10
                  c.add        tp, s5
                  addi         t5, gp, -754
                  addi         s2, a7, -180
                  c.slli       a7, 22
                  srl          a6, s8, t0
                  c.srli       a2, 8
                  slli         t5, gp, 15
                  mulhsu       a2, a7, gp
                  c.li         ra, 28
                  xori         s9, s8, -424
                  and          t2, t5, a5
                  srl          t4, sp, s11
                  remu         s8, s4, t0
                  rem          a7, tp, a0
                  mulhu        gp, s9, a2
                  li           a7, 0x80000000 #start riscv_int_numeric_corner_stream_20
                  li           a2, 0x365e3060
                  li           s1, 0xde2386bf
                  li           ra, 0x80000000
                  li           s3, 0x80000000
                  li           t0, 0x80000000
                  li           s2, 0x80000000
                  li           s5, 0xadc80288
                  li           s9, 0xffffffff
                  li           s8, 0x80000000
                  lui          s5, 878692
                  mulhu        s9, s9, s5
                  nop
                  mulhu        a2, t0, a2
                  mulh         s1, a2, s8
                  divu         ra, ra, a7
                  mulhu        a7, a7, a7
                  mulh         s1, s9, s1
                  divu         a7, s8, s2
                  divu         s9, t0, a7
                  sub          a7, a7, s9
                  remu         s5, s1, s2
                  div          s9, s8, s9
                  divu         a2, s5, s8
                  add          ra, t0, t0
                  add          s3, s8, s9
                  addi         s2, s5, 1739
                  rem          ra, t0, s1 #end riscv_int_numeric_corner_stream_20
                  slt          s5, sp, t1
                  mulh         tp, t6, s6
                  c.srli       a5, 21
                  mulhsu       s7, s1, s1
                  add          s2, s3, s10
                  c.xor        s1, s1
                  addi         ra, s2, 51
                  sub          t2, s6, zero
                  or           sp, sp, a6
                  c.or         s0, a0
                  c.slli       gp, 4
                  rem          t6, s6, s10
                  div          a2, s6, a2
                  xor          s8, a6, s4
                  srl          a0, s8, gp
                  c.and        s0, a2
                  lui          t0, 153334
                  c.slli       s1, 6
                  c.slli       t1, 29
                  c.sub        s0, a2
                  sub          a3, t2, a5
                  c.and        s0, s1
                  remu         s8, s8, s0
                  mulhu        t1, ra, a3
                  ori          s11, a6, 1221
                  rem          s3, s4, a3
                  srli         s7, t6, 4
                  c.xor        s0, s0
                  mulhu        t5, a3, a6
                  sub          t0, zero, t5
                  sub          t2, t6, gp
                  c.or         a3, a5
                  remu         tp, s7, t1
                  andi         a7, s4, -1741
                  srai         s4, ra, 29
                  c.mv         s8, a1
                  srli         s11, s2, 0
                  sltu         t3, t1, s10
                  remu         a3, t1, tp
                  add          a5, s7, s0
                  mulhsu       sp, tp, t2
                  div          a7, s11, a0
                  c.slli       sp, 20
                  slt          s0, t3, a7
                  addi         s3, s5, 918
                  c.li         t6, 22
                  remu         t6, s2, t6
                  divu         s7, gp, s11
                  auipc        s0, 830104
                  c.addi4spn   a2, sp, 112
                  addi         s10, a3, -387
                  c.lui        a0, 11
                  lui          t2, 816238
                  c.andi       s0, 5
                  c.add        s3, sp
                  slti         s2, gp, 707
                  c.xor        a5, a3
                  rem          t4, t6, s3
                  addi         sp, zero, 1792
                  rem          s7, s3, t1
                  sub          s7, s0, s2
                  or           s4, t4, a0
                  divu         a5, tp, ra
                  c.srli       a2, 8
                  mulhsu       s2, t0, a3
                  c.srai       a0, 28
                  c.li         a5, -1
                  c.add        t6, a3
                  srli         t1, sp, 10
                  auipc        ra, 746284
                  c.nop
                  c.or         s0, s0
                  srai         s0, a7, 4
                  sra          t5, t6, s8
                  mul          s11, sp, sp
                  c.and        a2, a3
                  c.nop
                  auipc        s2, 749668
                  srai         a6, s4, 21
                  div          s11, s11, tp
                  c.srai       a2, 28
                  sub          sp, a7, sp
                  mulhu        gp, s7, s4
                  mul          t4, a7, zero
                  sltu         t3, a2, t2
                  c.srai       s0, 11
                  sll          t1, s9, s1
                  c.nop
                  div          t2, s8, a1
                  lui          t0, 789563
                  div          s3, s5, t0
                  andi         s3, zero, 1185
                  srli         a2, s4, 11
                  c.lui        t3, 28
                  lui          s2, 694869
                  mul          s0, t2, s2
                  lui          a7, 867856
                  ori          tp, a5, 1379
                  sub          s11, t5, t5
                  mul          sp, t0, a5
                  c.or         a3, s1
                  xori         a7, s6, 245
                  mul          t5, a5, s10
                  c.addi16sp   sp, -16
                  nop
                  rem          s2, t3, tp
                  or           t4, sp, t3
                  div          s5, ra, t0
                  mulhsu       t4, a6, t6
                  slt          a3, a4, a6
                  sub          a6, a6, a0
                  c.andi       a3, 1
                  divu         s0, sp, s10
                  sub          s7, ra, s8
                  slli         t5, tp, 10
                  xori         a5, s7, 1571
                  c.add        a6, t0
                  sub          s0, t1, ra
                  slt          t6, ra, tp
                  c.srai       s1, 2
                  slli         gp, gp, 3
                  slli         t4, s5, 29
                  mul          t0, gp, s11
                  sra          s10, s4, s6
                  or           s3, t1, a7
                  c.nop
                  remu         ra, s10, t3
                  xor          t6, s4, s6
                  c.mv         s0, a1
                  c.nop
                  sub          s4, s5, s8
                  c.xor        a0, a5
                  c.addi       t0, 15
                  or           t1, t5, a1
                  c.andi       a2, -1
                  xor          a5, s4, a5
                  div          s4, a4, t1
                  mulhu        a2, t0, t2
                  c.mv         t6, s11
                  c.srai       a0, 10
                  slli         s9, gp, 13
                  and          s2, t6, gp
                  mulh         a0, s2, s5
                  c.mv         s1, s7
                  c.addi       s5, 16
                  slli         s9, s1, 23
                  c.mv         t5, s1
                  sra          s0, tp, s2
                  remu         s11, s1, s6
                  c.mv         s0, tp
                  c.addi16sp   sp, 320
                  lui          s3, 889688
                  sltiu        gp, t5, -338
                  c.addi       t0, -1
                  c.lui        s3, 13
                  sll          tp, t5, a0
                  rem          a6, a5, a5
                  c.nop
                  c.andi       a2, 20
                  or           zero, s7, t0
                  xori         ra, a4, -1001
                  mulhsu       s1, sp, tp
                  addi         s4, t3, 1228
                  sll          s1, s0, s5
                  c.addi4spn   a2, sp, 960
                  c.and        a5, s0
                  nop
                  and          s9, a1, t5
                  add          zero, a5, s3
                  auipc        s10, 401999
                  andi         s7, t1, -1535
                  c.sub        s1, a1
                  c.slli       t2, 25
                  mulh         s3, zero, sp
                  addi         t5, t0, -1799
                  and          s10, t4, a1
                  c.addi4spn   a3, sp, 64
                  c.li         a0, -1
                  c.andi       s1, 8
                  srli         s7, s7, 1
                  lui          a7, 74023
                  c.addi4spn   a2, sp, 672
                  auipc        ra, 66926
                  c.slli       tp, 1
                  nop
                  remu         s9, t1, s9
                  srl          t1, t6, gp
                  c.nop
                  c.xor        s0, s0
                  c.slli       s8, 24
                  mulh         s2, a1, a2
                  sltiu        a6, s7, -1171
                  c.srli       a3, 10
                  andi         zero, a4, -1589
                  xori         tp, s5, -1624
                  slti         s0, a2, -910
                  c.xor        s1, a0
                  c.andi       a3, 11
                  and          s1, a6, a1
                  srli         t1, t6, 11
                  c.xor        a3, a3
                  c.xor        s1, a3
                  c.addi4spn   a0, sp, 352
                  c.sub        a0, a0
                  addi         a3, gp, 1113
                  c.add        a7, t6
                  divu         tp, sp, s8
                  remu         s10, s7, t6
                  c.sub        s0, a1
                  ori          s8, a0, -1654
                  c.addi4spn   a5, sp, 208
                  c.and        a5, a0
                  xori         gp, t2, 483
                  sra          a3, a0, tp
                  nop
                  and          s3, a3, s1
                  sll          s9, s6, a7
                  sltu         s11, t4, s5
                  c.xor        a0, a3
                  c.xor        a5, s0
                  srli         s3, t3, 2
                  remu         s4, s6, s7
                  add          s7, t6, tp
                  c.or         a5, a0
                  divu         t6, tp, t4
                  mulh         t1, a7, t4
                  c.nop
                  remu         s9, a6, a2
                  xor          t6, sp, ra
                  c.srai       a2, 3
                  andi         a6, a7, 150
                  and          s11, t4, ra
                  li           gp, 0xc8af86d8 #start riscv_int_numeric_corner_stream_29
                  li           t0, 0x80000000
                  li           s5, 0x0
                  li           s11, 0x80000000
                  li           s2, 0xffffffff
                  li           t4, 0x80000000
                  li           a2, 0xffffffff
                  li           s8, 0x0
                  li           a7, 0x80000000
                  li           t3, 0x6475c3bb
                  rem          gp, t3, t3
                  remu         s8, a2, s2
                  lui          gp, 401399
                  auipc        s11, 143185
                  add          a7, s11, a2
                  nop
                  remu         a7, s11, s2
                  mulh         s2, gp, a7
                  mulh         s5, t0, a7
                  div          t3, t0, s2
                  mulh         s8, t4, s2
                  add          s2, t3, t3
                  mulh         s2, t3, s11
                  addi         a7, t4, 841
                  remu         a2, s11, s11
                  sub          s8, a7, s5
                  div          s11, s11, t0
                  mulhsu       s11, t3, t0
                  lui          a7, 897275 #end riscv_int_numeric_corner_stream_29
                  c.or         s0, a4
                  or           gp, t4, a3
                  c.li         s8, -1
                  add          s8, a0, t6
                  c.nop
                  srai         a0, a0, 18
                  xori         t5, a2, -1406
                  c.srli       s1, 25
                  addi         s10, s9, -11
                  slli         tp, a7, 15
                  slt          s8, ra, s11
                  sll          sp, s4, a7
                  xori         t3, s7, -906
                  slt          t6, a4, a3
                  slt          s3, a6, t4
                  andi         a3, s7, -1571
                  c.addi       s3, -1
                  lui          a0, 706678
                  slti         s5, t2, -1373
                  c.andi       a2, -1
                  slti         s9, tp, 883
                  add          t4, a3, s1
                  c.sub        s1, a3
                  c.mv         ra, s9
                  sltu         ra, s0, s1
                  xori         s2, zero, -102
                  remu         s8, s6, t1
                  mulh         t2, s2, a6
                  c.srai       a5, 18
                  andi         t2, s3, -377
                  c.addi4spn   a0, sp, 448
                  slli         s3, zero, 27
                  andi         gp, s8, 1712
                  andi         s1, sp, 782
                  c.and        a5, a5
                  xor          gp, s1, t0
                  sll          t4, s3, s8
                  sltiu        t4, s8, -1239
                  sltiu        s8, s2, -1893
                  c.addi4spn   s1, sp, 960
                  or           s10, a3, s6
                  rem          tp, tp, a4
                  c.or         a3, s0
                  c.xor        s0, s1
                  c.nop
                  divu         s3, s9, zero
                  c.lui        ra, 11
                  mulhsu       t6, s11, s5
                  slli         s0, s0, 16
                  c.mv         sp, s3
                  nop
                  addi         a0, s7, -1463
                  slt          a6, zero, a6
                  c.andi       a2, -1
                  c.addi4spn   s1, sp, 896
                  nop
                  divu         tp, s2, a4
                  andi         s7, s8, -534
                  sll          t4, a0, s0
                  sll          t4, s10, a0
                  divu         a6, s3, t1
                  auipc        t0, 219202
                  sra          a2, t3, a1
                  mul          a7, s3, t1
                  c.addi4spn   a3, sp, 784
                  sra          t2, t2, t1
                  c.add        t5, a7
                  xori         t6, a3, 2008
                  div          a5, a1, t1
                  c.srai       a3, 19
                  div          s10, s2, s9
                  c.li         a2, 30
                  andi         sp, t2, -485
                  c.nop
                  srli         a0, s0, 30
                  add          t0, t4, sp
                  srl          t1, a7, t4
                  andi         a7, a0, -1405
                  mul          s1, s11, a4
                  c.li         a7, 31
                  sll          a3, t4, s7
                  sub          zero, t5, s9
                  c.li         a6, 23
                  div          a2, s8, t3
                  sra          s10, s3, t5
                  sltu         s9, a4, s8
                  c.srai       a3, 22
                  c.srli       a0, 13
                  c.lui        s5, 28
                  xori         s9, ra, 897
                  sll          ra, s2, s4
                  slli         s0, s10, 15
                  c.andi       a2, -1
                  addi         t0, tp, -1159
                  c.or         s0, s0
                  c.and        s0, a1
                  c.srli       a2, 24
                  c.or         s0, a2
                  mul          t1, a2, s4
                  srai         s0, a0, 8
                  srai         a3, s4, 2
                  sra          s4, s10, a3
                  mulhsu       t2, s2, s9
                  divu         t2, s2, a0
                  mulhsu       s4, t3, s1
                  c.li         s8, -1
                  c.and        a5, a5
                  c.xor        a2, a3
                  c.srai       s0, 1
                  c.sub        a5, a1
                  mulhsu       t2, s8, a1
                  remu         a6, a4, s0
                  sltu         s2, a5, s8
                  srli         ra, a7, 22
                  divu         a0, s0, a0
                  c.srli       a5, 28
                  addi         s3, s8, 927
                  mulhu        s8, t5, t0
                  rem          tp, s1, a1
                  sltiu        a6, a1, -1051
                  lui          a3, 81034
                  or           s9, a1, zero
                  c.nop
                  remu         t1, s4, s1
                  srl          s7, a0, zero
                  or           t6, ra, a6
                  srai         t2, zero, 10
                  sltu         t0, t2, a1
                  c.srli       a5, 26
                  remu         a6, zero, t1
                  srl          t4, sp, a2
                  and          a3, t5, s2
                  lui          s9, 137441
                  and          s1, t4, sp
                  c.lui        t2, 12
                  lui          zero, 599095
                  c.sub        a0, s1
                  slti         s1, t6, -2048
                  divu         a5, a3, sp
                  xori         s7, s6, 817
                  c.addi       s2, -1
                  ori          t0, a2, 750
                  srl          gp, t1, s4
                  c.or         s0, s1
                  srli         s0, a0, 14
                  srli         t4, t0, 24
                  nop
                  auipc        t0, 754108
                  addi         t6, t2, 1104
                  c.sub        a3, a4
                  divu         t5, t3, a2
                  rem          tp, a0, t4
                  c.srli       s0, 4
                  mul          t5, t1, a2
                  remu         a0, s11, tp
                  srli         s11, s2, 20
                  c.lui        a7, 5
                  srli         s7, t0, 22
                  sub          s5, s8, a6
                  sltu         ra, t3, s8
                  c.lui        gp, 16
                  auipc        s4, 933662
                  mulhsu       s5, s7, s0
                  slli         a6, s0, 22
                  auipc        sp, 671596
                  lui          zero, 136925
                  remu         zero, s6, zero
                  c.addi       s1, -1
                  c.or         a5, s0
                  or           t4, a3, a1
                  c.sub        a2, a4
                  slli         t3, tp, 18
                  c.srli       a0, 11
                  c.and        a0, s0
                  add          s9, s6, s11
                  div          s7, s2, s8
                  c.andi       s0, 8
                  c.nop
                  rem          s0, a1, t6
                  c.sub        a0, a4
                  mul          s7, s2, s5
                  c.li         tp, 24
                  c.sub        s1, a2
                  mul          t2, s10, s9
                  c.li         t2, -1
                  andi         s10, s10, 621
                  mulh         ra, t6, s10
                  mulhsu       s10, a3, ra
                  c.or         s0, s1
                  c.nop
                  ori          s4, s0, 1934
                  sltu         t4, t4, t3
                  ori          s2, s4, -1509
                  c.addi16sp   sp, 176
                  c.xor        s1, a4
                  c.addi       s2, 22
                  c.sub        s0, a3
                  srai         a3, s10, 27
                  slt          gp, ra, t3
                  remu         s5, s8, a5
                  sub          sp, t0, s11
                  c.or         a0, a1
                  c.andi       a5, 22
                  xor          a6, t2, s5
                  c.srai       s0, 22
                  and          t3, t1, s3
                  c.xor        a3, s0
                  or           t6, a2, s3
                  xori         tp, s7, -1002
                  sub          s8, a2, a4
                  srli         s4, a7, 19
                  c.srai       s0, 29
                  mulhsu       a2, s3, t2
                  c.lui        s9, 14
                  c.add        a5, s2
                  c.lui        s0, 18
                  c.srai       a0, 11
                  c.mv         s9, s0
                  c.nop
                  remu         zero, t6, t2
                  sltu         t1, a4, s5
                  sltiu        s4, sp, -824
                  slli         s1, s4, 5
                  and          s9, s1, tp
                  add          s10, s2, t6
                  ori          a2, gp, 304
                  xori         zero, s5, -1669
                  mulhsu       sp, s6, a2
                  mul          s3, s10, a6
                  nop
                  andi         tp, s8, -1750
                  nop
                  mul          s9, t1, a6
                  c.add        s7, t2
                  and          zero, s10, s2
                  ori          s4, t1, -399
                  lui          a2, 937679
                  c.slli       a7, 20
                  slti         s7, t4, 787
                  andi         a2, s0, 119
                  lui          sp, 670187
                  c.nop
                  sra          t1, ra, gp
                  div          s4, s3, s8
                  c.srli       a2, 13
                  c.or         a2, a5
                  or           t2, a3, t1
                  c.srli       a0, 2
                  xori         t0, s10, -1455
                  srl          t2, ra, a0
                  nop
                  c.addi4spn   a3, sp, 112
                  c.add        tp, s11
                  mul          s4, s5, s10
                  srai         a6, a2, 22
                  mulh         a3, s9, s11
                  c.and        a5, a5
                  addi         t2, s4, 800
                  sub          t1, t4, s10
                  addi         s4, s11, -1863
                  slti         s5, t2, -1490
                  sll          s11, t6, s2
                  c.lui        s10, 24
                  xor          ra, s6, ra
                  sltiu        s10, s5, 1643
                  c.addi       t2, 27
                  and          s11, t1, tp
                  xor          gp, s8, a7
                  or           a2, a1, tp
                  c.andi       a3, 5
                  nop
                  slt          s0, t5, t6
                  xor          s1, s10, a5
                  ori          s4, a5, 613
                  c.mv         a2, s5
                  ori          s3, tp, -1924
                  lui          s10, 931091
                  c.slli       a7, 19
                  slt          a2, t0, s9
                  c.li         sp, -1
                  slt          ra, s5, t0
                  auipc        t1, 646319
                  c.sub        a5, a1
                  slt          a6, s11, t4
                  div          s8, s5, s3
                  lui          t2, 350614
                  srai         s8, t2, 8
                  mulhsu       t5, s11, s3
                  xor          s2, t3, s3
                  srli         t3, s9, 5
                  slti         s11, a1, 1602
                  c.sub        a0, a4
                  remu         ra, s6, gp
                  addi         a2, s1, -1760
                  c.andi       a5, -1
                  mulhu        s4, a0, t3
                  c.mv         s5, t0
                  sll          s4, s3, s1
                  mul          gp, t1, t1
                  and          a2, s3, t3
                  lui          s4, 179373
                  divu         a3, s2, a3
                  xori         t2, t3, 616
                  c.mv         t2, ra
                  c.srai       a2, 17
                  c.srai       a5, 31
                  c.addi4spn   a0, sp, 560
                  c.andi       a0, 8
                  divu         s8, t2, zero
                  mulh         s9, sp, t6
                  c.sub        s0, s1
                  c.add        t3, s4
                  c.andi       a3, 8
                  slli         s1, ra, 4
                  srli         a2, a4, 27
                  sub          a3, t5, t2
                  c.mv         s2, tp
                  andi         s4, a6, -1955
                  divu         sp, t4, zero
                  c.and        a3, a2
                  rem          a3, s5, a0
                  xori         gp, s6, -1775
                  sll          t3, s10, t1
                  mulhu        t5, t2, zero
                  sltu         t5, a6, gp
                  c.nop
                  lui          s11, 120913
                  c.or         s0, s0
                  and          t4, s1, a4
                  c.srli       s0, 7
                  nop
                  sltu         sp, t4, s10
                  remu         s11, s3, t4
                  c.and        s0, a4
                  c.sub        s0, s0
                  c.addi4spn   a5, sp, 112
                  xor          s8, ra, s3
                  c.li         a2, 26
                  c.lui        a0, 30
                  c.addi16sp   sp, -16
                  c.xor        s0, a3
                  sltu         t5, t5, a7
                  auipc        s7, 326008
                  auipc        a6, 516615
                  c.addi16sp   sp, 464
                  c.sub        a0, a2
                  divu         s0, s0, s7
                  mulhsu       s5, s3, s7
                  srli         s1, t2, 7
                  c.addi16sp   sp, 208
                  xori         tp, t5, -394
                  slti         sp, a3, 201
                  auipc        s7, 615864
                  add          a5, a4, s11
                  c.addi       s4, 14
                  mulhu        a0, s5, s6
                  srl          s5, tp, sp
                  addi         a3, t2, 1213
                  mulhu        t4, a5, s2
                  slli         s5, a0, 24
                  lui          t0, 715558
                  c.or         a3, a2
                  slli         t2, t6, 27
                  c.andi       s1, -1
                  c.li         s2, 3
                  nop
                  srai         s10, s11, 22
                  c.xor        s0, a0
                  c.or         a2, a5
                  lui          sp, 177570
                  nop
                  c.mv         ra, t3
                  c.srli       a3, 15
                  nop
                  c.or         a0, a4
                  mulhsu       s9, t1, a3
                  addi         a5, s9, 567
                  auipc        a5, 384626
                  sltu         t0, s11, s6
                  mul          t6, t2, t1
                  c.addi       s8, 26
                  c.slli       s1, 15
                  nop
                  mulhsu       a2, t1, ra
                  mulh         s0, t2, t2
                  or           s0, t3, s4
                  srai         t1, t0, 30
                  c.srai       a2, 29
                  c.andi       a5, 25
                  mulh         s0, a6, s9
                  c.sub        a2, s0
                  xori         a0, a7, -1129
                  rem          t2, a0, s10
                  c.srai       a2, 2
                  remu         t1, gp, a7
                  ori          a7, s9, 1522
                  auipc        s11, 696202
                  mulhsu       t4, ra, t4
                  andi         s0, t5, 1071
                  sra          ra, s1, t2
                  andi         s3, a4, -569
                  slt          ra, s2, tp
                  sll          s7, t6, t3
                  c.andi       a0, -1
                  c.li         s7, -1
                  c.sub        a5, s1
                  mulhu        s8, s8, s6
                  sll          s8, s11, a1
                  c.andi       a5, -1
                  mulhu        gp, s11, t1
                  ori          zero, s6, -1600
                  rem          s9, gp, s2
                  mul          t3, t4, s3
                  sll          s11, s3, s9
                  mulhu        a0, s6, s0
                  sra          s1, tp, s5
                  c.addi4spn   a0, sp, 608
                  c.srli       a5, 2
                  c.xor        a3, s1
                  mulhu        a3, s10, a1
                  xor          s7, s6, s8
                  xori         s9, a0, -1071
                  sll          t4, s7, a7
                  mulhu        s10, t2, s5
                  c.addi       ra, 9
                  c.srli       a2, 15
                  mul          s7, gp, a5
                  c.addi16sp   sp, 80
                  mulh         a3, a7, s6
                  c.lui        a3, 22
                  ori          s8, a2, 748
                  rem          t0, a4, gp
                  c.lui        s0, 12
                  c.addi16sp   sp, -16
                  mulhu        s3, s8, s3
                  ori          a3, ra, -891
                  c.andi       a2, -1
                  add          gp, s1, s7
                  sltiu        t6, s9, -819
                  srl          a0, s7, a3
                  addi         a6, t4, -771
                  c.srai       a0, 24
                  divu         a7, s4, s3
                  c.and        a5, s1
                  c.and        a0, s1
                  divu         s8, s3, s11
                  c.addi16sp   sp, 272
                  mul          s11, s0, t2
                  c.sub        a2, a0
                  sll          s5, zero, a0
                  c.and        a0, a0
                  auipc        zero, 144871
                  c.sub        a3, a5
                  sltu         t5, a5, a7
                  c.srli       a2, 25
                  add          s10, t0, sp
                  srai         t0, t4, 9
                  slli         s7, s8, 19
                  mulhsu       s10, s7, a6
                  mul          a7, s10, s3
                  nop
                  c.slli       gp, 8
                  sra          s4, s4, a2
                  slli         a6, t3, 11
                  or           s10, a0, t6
                  div          ra, s4, t0
                  rem          s7, t3, t0
                  srai         zero, t3, 17
                  c.mv         t1, s10
                  remu         ra, gp, s7
                  lui          ra, 732222
                  c.addi       s4, -1
                  c.addi16sp   sp, -16
                  div          s4, gp, a2
                  c.addi4spn   s0, sp, 592
                  xori         t4, a1, 1999
                  ori          s0, s2, 975
                  sltiu        t6, a7, 9
                  c.xor        a3, a5
                  mulh         zero, t3, s11
                  xori         s3, t6, -1663
                  sltu         zero, s9, a5
                  c.addi4spn   s1, sp, 608
                  div          s1, a1, zero
                  c.sub        a5, a0
                  slt          s9, s10, gp
                  mulhu        s3, a2, t5
                  lui          s9, 58827
                  mul          s10, s4, gp
                  sub          s11, a0, a3
                  c.slli       t1, 19
                  mulh         s3, a6, ra
                  srli         s8, s2, 17
                  mulhsu       sp, a4, t0
                  sltu         t2, s10, t5
                  c.lui        tp, 28
                  c.xor        a0, a2
                  sra          gp, a2, t4
                  c.addi16sp   sp, 160
                  sltiu        s2, a5, 1545
                  c.slli       s11, 1
                  xori         a2, s10, 1262
                  c.andi       s0, 13
                  c.nop
                  c.lui        s2, 31
                  auipc        a2, 131838
                  xor          gp, s3, tp
                  auipc        a0, 982639
                  sll          a3, s9, s2
                  div          t4, zero, a1
                  sltu         s1, s5, a1
                  mulhu        tp, s4, s0
                  nop
                  srai         a2, a2, 20
                  nop
                  add          s10, s3, s4
                  ori          a7, s8, -2012
                  sltiu        t5, gp, 41
                  c.and        a3, a0
                  lui          a6, 702649
                  slti         s4, t1, 1149
                  slt          a6, a0, a2
                  c.addi4spn   s0, sp, 784
                  c.sub        a5, a0
                  srli         t1, s9, 31
                  sltu         s8, t0, zero
                  c.or         s1, a4
                  srl          s4, s3, s9
                  c.xor        a2, a1
                  c.mv         t6, s9
                  mulh         t5, a3, s8
                  sub          s7, t4, s8
                  sll          a3, t5, s9
                  c.slli       tp, 14
                  c.addi4spn   s1, sp, 736
                  c.srli       a5, 1
                  c.and        a5, s0
                  c.srli       a2, 14
                  mulhu        s0, t5, gp
                  c.or         a5, s0
                  sltu         a7, s0, s6
                  c.addi       s11, 12
                  or           zero, ra, t1
                  slti         s0, s4, -1701
                  or           s2, t2, s1
                  sll          a3, s2, s8
                  lui          t3, 396052
                  rem          t6, s2, a0
                  slti         t5, s7, -1884
                  andi         t5, s1, 409
                  ori          s10, a6, 1786
                  sltu         a2, tp, a7
                  mul          zero, s1, t3
                  sub          tp, s9, zero
                  c.and        s1, s1
                  c.add        t2, t0
                  slli         tp, a0, 16
                  c.sub        a5, a1
                  nop
                  sltu         s7, a2, a5
                  sub          t1, s8, t4
                  xori         t4, s10, -1710
                  mul          a6, s1, a1
                  c.lui        t1, 31
                  sltiu        t1, s11, 973
                  andi         t0, a2, -1471
                  slli         s7, s9, 24
                  sltu         s5, t0, s1
                  c.addi16sp   sp, 208
                  sltu         a5, s7, sp
                  sll          a2, tp, a2
                  c.sub        s0, s1
                  c.lui        tp, 12
                  c.mv         sp, t5
                  mulhu        a7, ra, t5
                  sltu         s0, a2, s4
                  c.or         a2, a4
                  c.addi       s2, -1
                  slli         t2, a4, 24
                  xori         a2, s8, 267
                  mulhu        a2, s0, s3
                  rem          a0, s5, t2
                  ori          a3, a6, -1490
                  sll          t6, a3, s1
                  c.addi       s5, 15
                  sra          ra, s6, ra
                  srl          tp, s3, t1
                  c.lui        s3, 16
                  ori          sp, a4, -1703
                  c.slli       a7, 6
                  c.or         a0, a0
                  c.andi       a3, -1
                  and          t6, a4, s7
                  auipc        a2, 920305
                  c.xor        s0, a2
                  slti         s2, a1, -1031
                  remu         ra, s1, s9
                  c.addi16sp   sp, -16
                  add          s2, s10, zero
                  mul          a5, t4, t0
                  c.or         a5, a3
                  c.srai       a3, 24
                  lui          s3, 238809
                  c.add        t0, s4
                  srli         s8, s9, 28
                  nop
                  c.slli       a7, 15
                  auipc        t1, 572033
                  sll          s7, s4, s0
                  srl          t3, a2, ra
                  c.li         a7, 5
                  lui          s5, 273365
                  lui          a2, 852190
                  or           gp, s10, zero
                  mulhu        s11, s4, ra
                  c.srli       s0, 25
                  c.xor        a3, a4
                  lui          a3, 856604
                  c.srli       a5, 22
                  andi         a0, s5, -346
                  slt          a0, a7, sp
                  divu         s1, ra, t3
                  c.andi       s0, 7
                  add          gp, s6, a3
                  srai         s4, zero, 9
                  sll          s4, s6, s3
                  ori          s11, a5, 854
                  c.addi4spn   a0, sp, 896
                  auipc        t2, 779219
                  ori          s4, t1, -1220
                  c.addi4spn   a3, sp, 672
                  c.xor        s0, a3
                  divu         s1, a0, t3
                  sll          tp, s1, t1
                  c.srai       a0, 29
                  c.addi4spn   a2, sp, 1008
                  slli         s9, s5, 26
                  c.mv         a6, t4
                  sub          s7, s0, s10
                  sll          s10, a7, a2
                  remu         t4, t1, sp
                  addi         t0, a6, 862
                  c.srli       s0, 10
                  andi         sp, t3, 1904
                  c.addi16sp   sp, 384
                  c.add        tp, t3
                  or           s0, s2, s2
                  c.add        a3, s10
                  nop
                  xor          s5, s2, s2
                  sub          s9, s7, a5
                  addi         a0, zero, 273
                  c.lui        gp, 15
                  c.lui        a3, 22
                  mul          a7, t4, s10
                  sll          s4, t0, s7
                  add          s2, t4, ra
                  c.slli       s1, 2
                  xori         gp, s6, -1439
                  or           t4, s11, a1
                  c.or         a5, a5
                  c.or         a2, a1
                  sll          t5, t6, gp
                  srai         gp, a4, 15
                  sub          a0, s1, s8
                  c.and        a5, a2
                  slli         tp, t0, 18
                  c.addi16sp   sp, 256
                  c.or         a0, s1
                  sra          a7, s0, s7
                  remu         s0, t5, s10
                  c.or         a0, a1
                  mul          t1, t5, s2
                  c.sub        a2, s1
                  c.nop
                  auipc        s5, 210845
                  add          a6, t0, tp
                  xor          t5, s7, s11
                  mulh         s9, s11, sp
                  srli         gp, gp, 7
                  c.addi4spn   a5, sp, 864
                  slt          t2, a2, tp
                  divu         s10, t4, s10
                  or           a5, a5, t5
                  mulhu        gp, a3, t5
                  addi         a7, a0, 393
                  c.sub        s0, s1
                  sub          t6, s11, s1
                  sra          a5, s7, s11
                  div          tp, s6, s8
                  auipc        zero, 472445
                  mulhu        a5, t2, t4
                  sub          a5, a4, s10
                  srli         gp, gp, 6
                  srai         sp, a0, 31
                  add          s3, t2, sp
                  sub          s0, t5, s5
                  c.and        a2, a3
                  sltu         sp, t0, s3
                  c.srai       s1, 9
                  slti         tp, a5, -59
                  xori         t1, t1, 1673
                  sub          s1, t1, s11
                  nop
                  c.addi4spn   s0, sp, 336
                  slli         s9, t5, 9
                  c.mv         s10, gp
                  slti         s11, s7, -657
                  c.addi16sp   sp, 192
                  rem          t1, a7, tp
                  c.addi16sp   sp, -16
                  c.slli       a5, 22
                  c.mv         gp, s4
                  nop
                  c.addi       a3, 12
                  c.addi16sp   sp, 32
                  c.andi       a0, -1
                  sltu         t5, zero, a1
                  xor          t3, t6, s3
                  srai         ra, s5, 20
                  rem          a2, s6, t6
                  divu         t6, tp, s0
                  auipc        zero, 31635
                  c.add        s0, a1
                  div          s5, gp, a5
                  mulh         t4, a0, t0
                  c.addi4spn   s0, sp, 224
                  mulh         s2, tp, t2
                  div          t3, s8, s1
                  add          s2, s9, t4
                  c.addi16sp   sp, 144
                  slti         t2, a1, -1786
                  xor          s7, s0, zero
                  c.lui        tp, 17
                  lui          t0, 207923
                  mul          s9, t4, s6
                  sltu         t1, t3, t0
                  srli         a5, t0, 10
                  c.nop
                  srli         s5, s6, 2
                  slt          t5, s5, s1
                  mulhsu       s5, a6, tp
                  sll          t0, t3, s6
                  srl          sp, a3, t4
                  nop
                  sub          a7, t1, s3
                  sltu         a7, t4, s0
                  lui          s11, 14435
                  srai         a5, sp, 13
                  add          a0, t1, a2
                  sub          s2, a7, s4
                  c.addi4spn   a2, sp, 544
                  xori         s10, gp, -253
                  c.lui        s8, 2
                  addi         a2, tp, -1540
                  c.and        a5, a4
                  slt          s1, s5, t3
                  c.and        a2, a3
                  mulhu        s10, t1, s9
                  c.or         a3, s0
                  c.or         s1, a1
                  sltiu        t2, a3, -1682
                  c.addi4spn   a2, sp, 16
                  mulhu        t4, t5, t1
                  or           a3, a4, ra
                  xor          a0, t0, s6
                  divu         t1, s9, s2
                  rem          a6, t1, a4
                  xori         t0, zero, -678
                  sll          s0, ra, a2
                  mulhsu       t6, s1, a5
                  remu         s0, a6, t3
                  c.srli       a0, 25
                  c.li         t4, -1
                  c.srai       s0, 23
                  srl          s10, a5, a1
                  slti         a7, a6, 1013
                  rem          s5, s10, t5
                  and          a7, a1, sp
                  c.sub        a5, a1
                  andi         t2, t4, 209
                  mulhsu       a7, s11, t0
                  xor          zero, s4, a5
                  srli         a3, s10, 31
                  andi         sp, t2, -1678
                  xori         s7, s8, -1196
                  and          s3, s11, s8
                  c.li         sp, 30
                  divu         s3, ra, s7
                  mul          s10, t6, a5
                  rem          s11, a6, a2
                  xori         s4, t0, 350
                  c.li         s4, 9
                  sra          ra, t4, t0
                  srai         t1, ra, 16
                  rem          s0, t3, a1
                  rem          s4, s3, ra
                  c.li         a7, -1
                  xori         s10, t0, -1712
                  c.add        a3, ra
                  lui          s3, 255506
                  c.addi4spn   a2, sp, 128
                  remu         s9, t2, t0
                  andi         s5, s7, -932
                  slli         s11, a2, 12
                  slt          a0, a6, a5
                  sub          s9, a5, a4
                  c.andi       a5, 12
                  auipc        t3, 352361
                  rem          t2, t3, a7
                  remu         a6, s0, gp
                  sra          a6, gp, s4
                  c.mv         t0, a2
                  divu         a6, s6, a3
                  sll          t3, tp, a5
                  divu         s1, s9, s6
                  sll          s3, ra, s2
                  remu         s2, a0, s1
                  slti         gp, t2, -1747
                  slti         a3, s1, -1393
                  addi         a2, sp, -752
                  c.srli       a5, 21
                  sub          t0, a0, s9
                  c.addi4spn   s1, sp, 784
                  slli         s4, a5, 31
                  remu         gp, a1, a5
                  addi         zero, s6, 1230
                  slli         a6, a0, 27
                  c.add        s11, tp
                  mulhu        t6, s7, s2
                  c.and        a5, a2
                  c.srli       s0, 12
                  sltiu        a6, s10, 901
                  rem          t6, s4, s9
                  add          t0, t1, s4
                  div          a0, t6, a4
                  slti         a6, s2, -1921
                  slli         a6, a5, 19
                  andi         s2, tp, 802
                  xor          s7, gp, gp
                  sltu         t6, t3, t0
                  c.li         s2, 19
                  srli         t6, gp, 27
                  c.addi4spn   s0, sp, 80
                  sltiu        s0, a7, 1321
                  andi         ra, ra, -167
                  mulh         a2, zero, zero
                  c.mv         t3, ra
                  mulhu        s3, a6, a7
                  c.andi       s1, 1
                  remu         sp, a0, s2
                  slt          a5, t2, sp
                  xor          s4, t2, t0
                  sltu         ra, s6, a1
                  xori         sp, a2, -1268
                  c.lui        s2, 26
                  sltiu        s7, t1, 1293
                  xor          t1, s9, s7
                  c.sub        s1, a1
                  c.mv         a0, s7
                  c.andi       a5, 12
                  auipc        s9, 614669
                  xori         a0, tp, -602
                  ori          a3, t1, 270
                  li           t2, 0x0 #start riscv_int_numeric_corner_stream_39
                  li           t1, 0x80000000
                  li           t3, 0x80000000
                  li           s11, 0xa497c847
                  li           s8, 0x6fa8c119
                  li           gp, 0xaccad537
                  li           ra, 0x798dfd99
                  li           s9, 0x522c2a5e
                  li           s4, 0xffffffff
                  li           t4, 0x74880a4f
                  divu         s8, s9, s8
                  add          s9, s9, t3
                  addi         s8, s11, -594
                  remu         s4, t4, t1
                  addi         s4, t2, 612
                  mulhsu       t1, t1, t1
                  add          ra, s4, s4
                  auipc        t3, 41037
                  auipc        t3, 336022
                  lui          t3, 563045
                  mulhu        t2, t3, ra
                  mulhsu       s4, gp, ra
                  remu         t4, t1, s8
                  mulhsu       s8, t3, t2
                  mulh         s11, t3, t2
                  mulhu        s8, t2, t2
                  add          ra, ra, t3 #end riscv_int_numeric_corner_stream_39
                  add          a2, zero, tp
                  sltiu        sp, t6, -1291
                  sltiu        a5, ra, -1342
                  sll          a3, t2, gp
                  mulhsu       t2, s11, a4
                  slt          t1, t2, s1
                  div          s10, ra, a0
                  ori          t2, ra, 191
                  lui          s5, 479723
                  c.nop
                  c.add        tp, gp
                  c.nop
                  c.xor        a0, a4
                  srli         t3, a6, 12
                  add          s7, a3, t3
                  c.addi16sp   sp, -16
                  c.slli       s5, 13
                  sra          t1, t5, s5
                  c.addi       a5, -1
                  divu         t5, a1, t0
                  xori         t1, a3, 2
                  rem          gp, a0, s0
                  c.addi16sp   sp, 336
                  srai         t1, a4, 16
                  add          s7, a5, a5
                  c.addi16sp   sp, -16
                  c.addi16sp   sp, -16
                  slli         s4, s1, 29
                  auipc        s9, 14335
                  mul          t5, a4, t0
                  mul          a7, s8, a7
                  c.addi4spn   a0, sp, 592
                  and          t3, ra, s8
                  add          s9, s10, s10
                  c.addi16sp   sp, 496
                  c.add        t2, t4
                  c.or         a0, a3
                  addi         s10, s10, -345
                  add          a2, s4, tp
                  and          t2, a2, t6
                  c.addi       tp, -1
                  ori          tp, s6, -1593
                  ori          s8, tp, 1287
                  remu         s9, a4, t2
                  c.andi       a5, 26
                  mul          t1, t5, a6
                  lui          t2, 733146
                  sltu         t2, t4, t0
                  c.sub        a5, a1
                  c.nop
                  srl          t5, t6, ra
                  slt          s4, t4, s0
                  divu         s8, t5, t0
                  c.xor        s1, a5
                  nop
                  mulh         sp, s5, s6
                  rem          t6, t4, t5
                  slt          s4, a0, t0
                  andi         s0, t2, 1405
                  c.addi       s11, -1
                  mul          tp, s6, s7
                  c.sub        s1, a1
                  sltu         a0, t3, t6
                  sll          s5, t4, a4
                  rem          s4, tp, s3
                  c.andi       s0, 8
                  addi         s8, ra, 2039
                  andi         s10, s9, -2035
                  mulhsu       tp, s2, t6
                  c.sub        a2, s1
                  c.mv         s0, a3
                  c.mv         s0, t2
                  sltu         t1, s11, t3
                  c.lui        s7, 18
                  c.andi       s1, 7
                  addi         t4, s0, -1598
                  mulh         s3, t2, s11
                  sltu         t5, s11, sp
                  c.srli       a0, 1
                  sra          s10, a1, zero
                  c.or         s1, a4
                  c.or         a2, a5
                  c.lui        s0, 28
                  c.addi       s7, 15
                  addi         a7, ra, -1246
                  sltu         zero, s4, s1
                  c.addi4spn   a3, sp, 160
                  c.mv         a6, a5
                  lui          a2, 474616
                  c.addi4spn   a3, sp, 624
                  li           a6, 0x80000000 #start riscv_int_numeric_corner_stream_31
                  li           sp, 0x0
                  li           s11, 0x5ab9681a
                  li           a2, 0x9db1449b
                  li           s4, 0xffffffff
                  li           t3, 0x8b47ccd8
                  li           s1, 0xffffffff
                  li           s5, 0x0
                  li           s8, 0xffffffff
                  li           t6, 0x0
                  lui          s5, 783156
                  nop
                  mulhsu       t6, sp, sp
                  mulhsu       s1, t3, s11
                  mulh         a2, a2, t3
                  lui          a2, 1002105
                  divu         t3, a6, t3
                  mulhu        a2, s8, a2
                  div          s5, s8, s11
                  div          a2, s4, sp
                  add          s11, s1, s11
                  div          a6, s1, a6
                  add          s4, s5, s11
                  divu         a2, a6, s1
                  nop
                  add          t6, a2, s8
                  div          s8, a6, a2
                  remu         s5, s4, s8
                  sub          s1, s5, s1
                  lui          s8, 860185
                  mulh         a2, a2, s8
                  add          s5, a2, s11 #end riscv_int_numeric_corner_stream_31
                  sltu         t6, s2, s4
                  c.or         a0, a3
                  slli         a6, t1, 19
                  c.add        t4, s9
                  c.add        s9, a7
                  c.li         s7, -1
                  srli         sp, t3, 29
                  mul          a0, t4, s6
                  c.addi16sp   sp, -16
                  slli         a2, s5, 30
                  sra          a3, t3, s0
                  mul          ra, a2, sp
                  rem          tp, s4, t5
                  rem          s4, a6, s4
                  c.mv         s0, t2
                  slt          gp, s7, s0
                  c.andi       s0, -1
                  c.and        s1, a1
                  sll          a2, gp, s9
                  xor          s9, a1, zero
                  xori         a6, s7, -2014
                  sra          s0, s3, ra
                  srai         s4, s0, 19
                  c.srai       a2, 11
                  rem          tp, t5, s3
                  srai         s7, s5, 17
                  or           s4, ra, s1
                  slti         t2, a1, -1263
                  c.andi       a3, -1
                  c.srai       a0, 23
                  c.slli       tp, 9
                  srli         sp, ra, 1
                  c.mv         s5, t1
                  c.lui        t2, 18
                  sub          s5, t2, a0
                  c.xor        s0, a5
                  c.slli       ra, 22
                  srai         a2, a2, 23
                  xori         t4, s4, -879
                  c.addi16sp   sp, 320
                  mulhu        ra, zero, t4
                  div          s2, a6, t6
                  sll          t2, a4, zero
                  c.andi       a2, 9
                  and          s7, t5, t6
                  nop
                  sub          s5, s10, s11
                  c.nop
                  sub          s0, s8, t4
                  c.srli       a5, 26
                  slti         s0, s6, -1605
                  andi         s8, a0, 888
                  mulhsu       s9, s6, a1
                  c.andi       s0, 5
                  c.add        t0, a1
                  c.xor        a0, a1
                  remu         s2, a3, s2
                  srl          s9, t3, s11
                  c.addi4spn   a0, sp, 928
                  xori         t6, t6, -1279
                  rem          s2, s4, s8
                  c.addi16sp   sp, 144
                  nop
                  srai         a2, a0, 9
                  add          a0, ra, s5
                  nop
                  remu         s8, t2, tp
                  mulhsu       tp, zero, s3
                  auipc        s5, 118653
                  divu         s8, s11, s9
                  c.xor        s0, s1
                  sll          s5, s10, a6
                  sra          t0, a3, s8
                  sra          a6, s6, s5
                  slti         s8, a3, 1500
                  c.li         t3, 23
                  nop
                  divu         t1, s0, s9
                  c.xor        a0, a4
                  and          s2, s6, s11
                  c.addi16sp   sp, 272
                  slti         s7, t6, -843
                  c.addi       t1, -1
                  andi         a6, s3, 196
                  c.nop
                  c.srli       a3, 29
                  sltiu        a7, a6, 1157
                  slti         s9, a7, 944
                  and          s5, s4, t3
                  c.addi4spn   a0, sp, 848
                  slt          t6, ra, s8
                  c.xor        a0, a2
                  c.nop
                  auipc        t5, 142780
                  c.andi       a2, 3
                  c.li         t1, 9
                  srl          s8, s8, a2
                  c.mv         s7, s3
                  add          t2, t4, t4
                  li           a0, 0x0 #start riscv_int_numeric_corner_stream_4
                  li           s9, 0x80000000
                  li           s2, 0xffffffff
                  li           a2, 0x80000000
                  li           s1, 0xffffffff
                  li           a7, 0xffffffff
                  li           tp, 0x80000000
                  li           t4, 0x6ee58220
                  li           ra, 0xffffffff
                  li           t1, 0xe243db35
                  lui          ra, 1041709
                  mulhu        tp, s2, a0
                  add          a2, t1, a7
                  lui          t4, 364668
                  add          a2, a0, ra
                  mulh         s2, s9, tp
                  remu         a0, t1, a7
                  addi         a7, t1, -1109
                  mulhu        ra, a0, ra
                  add          a7, tp, t1
                  mulh         a7, s1, s1
                  lui          s1, 634478
                  auipc        ra, 131006
                  mulh         s2, a0, a7
                  mulhsu       a2, a2, s2
                  divu         a2, s2, a0
                  mulhsu       s1, a0, a0
                  sub          s9, a2, s9
                  nop #end riscv_int_numeric_corner_stream_4
                  c.srli       a3, 20
                  slt          t0, s11, t5
                  auipc        a7, 21841
                  c.addi16sp   sp, 80
                  c.and        a5, a0
                  nop
                  addi         s11, s0, 1307
                  c.andi       a0, -1
                  nop
                  c.addi4spn   a3, sp, 736
                  c.add        ra, a0
                  sll          a7, t2, ra
                  div          s10, a7, s9
                  add          tp, s2, t6
                  or           tp, s0, t3
                  ori          s5, s6, -831
                  andi         zero, sp, -1928
                  xor          t5, a6, s10
                  mulhu        s3, a7, s0
                  srli         s9, s1, 9
                  mul          t6, a5, sp
                  slt          t3, t4, s6
                  add          s10, s11, zero
                  c.srai       a5, 14
                  rem          t2, ra, a2
                  lui          s10, 375638
                  xor          a0, s10, s8
                  srai         t3, s3, 30
                  c.or         s0, s1
                  c.mv         a3, gp
                  c.addi       a3, -1
                  srli         s9, s3, 9
                  xori         a3, ra, 1110
                  sub          gp, t5, ra
                  srli         a3, a4, 7
                  c.and        a0, a1
                  addi         zero, s5, 1804
                  c.srli       a0, 18
                  c.li         t1, 22
                  slli         t0, a5, 4
                  lui          s10, 25428
                  xor          a6, a0, s9
                  div          ra, s5, t2
                  mulh         s9, s7, t4
                  c.li         s0, 4
                  sra          s11, t2, s1
                  c.srai       a2, 26
                  c.and        a2, a1
                  nop
                  srai         t0, s10, 16
                  c.mv         s7, a2
                  xor          s3, ra, a3
                  addi         s10, t4, 741
                  ori          t3, a7, -281
                  sltiu        s0, t1, -114
                  srli         t3, a3, 29
                  mulhu        t2, a1, gp
                  c.slli       a5, 24
                  c.add        s2, t4
                  c.sub        s0, a0
                  slt          a5, t2, s8
                  xori         a5, a3, -1715
                  c.addi4spn   a2, sp, 480
                  c.mv         a5, s7
                  sltiu        s11, a2, 258
                  xori         a2, s9, -115
                  c.add        s7, s0
                  add          gp, a6, t6
                  slt          s0, sp, s2
                  nop
                  c.mv         a7, s0
                  addi         t4, t4, -1555
                  sltu         t5, s3, s7
                  auipc        a5, 917872
                  c.mv         s5, t1
                  and          ra, s11, a2
                  c.and        a3, a4
                  andi         a0, s10, -1050
                  c.addi16sp   sp, 400
                  rem          a5, t6, a6
                  div          a5, s5, s1
                  sub          s0, a2, t3
                  c.srli       a0, 4
                  slti         s1, s2, -276
                  c.srli       s1, 21
                  c.slli       a3, 5
                  nop
                  or           t5, s8, s1
                  c.addi       s0, -1
                  srai         s5, s7, 0
                  c.srli       a5, 6
                  addi         s7, a5, 1469
                  and          t5, ra, a4
                  c.slli       sp, 22
                  sub          s8, a3, gp
                  c.nop
                  c.addi       t5, -1
                  c.slli       a6, 9
                  c.andi       s0, -1
                  mul          a5, s2, a6
                  addi         a7, gp, 943
                  c.srli       a2, 9
                  mulhsu       t2, a3, t4
                  c.srai       a3, 8
                  rem          s10, t6, s1
                  sll          t0, s0, a0
                  lui          s7, 962736
                  c.or         a5, a0
                  divu         ra, gp, s10
                  slli         gp, t5, 15
                  add          t1, t5, t6
                  c.andi       a3, -1
                  sub          a7, t3, t2
                  divu         t6, zero, s0
                  sll          a0, s6, a1
                  or           sp, a5, a2
                  c.slli       s2, 31
                  andi         t2, s11, 1134
                  divu         s2, t1, a3
                  xor          s0, t5, a5
                  add          s8, s5, s11
                  divu         gp, s5, a7
                  rem          a0, s0, s0
                  c.slli       a6, 25
                  andi         a5, s6, -663
                  ori          t3, a2, 1254
                  auipc        a2, 894743
                  mulhu        s3, s6, a0
                  c.or         a0, a4
                  andi         ra, s8, 731
                  divu         sp, s1, s10
                  divu         s3, t6, t5
                  srai         s11, s8, 9
                  c.nop
                  rem          a6, gp, a2
                  c.addi       ra, 21
                  sltu         s11, s11, t2
                  remu         s9, a7, t1
                  sltu         a6, t3, a6
                  slli         gp, a5, 15
                  remu         t4, s11, a1
                  slli         tp, a1, 18
                  srl          s10, s2, a1
                  add          t1, t3, s1
                  c.addi16sp   sp, 368
                  mul          s9, tp, s3
                  mulh         a7, s0, t6
                  c.srli       a2, 3
                  remu         a2, s5, t2
                  c.andi       a5, -1
                  sra          s8, s0, s4
                  xori         t1, sp, 265
                  nop
                  sub          a7, a5, t4
                  c.li         t4, -1
                  slli         s3, a4, 29
                  and          s5, t3, a1
                  srl          a3, zero, s11
                  xori         s3, s3, -1470
                  mulh         a3, s10, a3
                  sltu         s2, s10, t1
                  mulhsu       t1, t5, s5
                  xori         t0, t1, 1594
                  mulhu        t1, a7, a7
                  c.mv         t0, t0
                  c.or         s0, a0
                  srli         s0, s2, 21
                  c.add        a3, a7
                  c.andi       s0, 10
                  mulh         s9, a0, a5
                  xor          zero, t0, s11
                  sra          a2, s11, s5
                  c.lui        t6, 10
                  or           s5, a6, s5
                  c.addi       a3, -1
                  srai         tp, t1, 19
                  div          a7, s4, a1
                  divu         a2, a7, a0
                  divu         tp, a2, t5
                  c.or         a0, s1
                  and          zero, t3, t3
                  mulhsu       s7, s8, a3
                  c.add        s0, a1
                  srai         s11, a7, 10
                  remu         s8, tp, a7
                  c.addi16sp   sp, 32
                  c.and        a2, a2
                  c.add        s7, a5
                  sra          s10, a1, t0
                  and          s7, s6, zero
                  divu         a0, s7, a2
                  sltiu        t2, a3, -1144
                  c.and        a3, s1
                  c.nop
                  nop
                  lui          sp, 688300
                  sub          s11, t6, t1
                  sub          a3, a1, a5
                  slli         s7, s4, 29
                  c.mv         gp, tp
                  srli         ra, s6, 12
                  divu         s4, t3, a4
                  c.andi       a3, 25
                  c.addi16sp   sp, 464
                  sltu         a3, t5, t0
                  c.addi       t0, -1
                  xori         t3, t1, 583
                  c.and        a5, a2
                  add          a7, a2, a4
                  sub          t2, t5, s7
                  mul          a6, s9, t1
                  slt          s1, s0, a3
                  c.sub        a2, a1
                  c.addi4spn   a5, sp, 80
                  lui          a7, 294233
                  mulhsu       ra, a6, a2
                  lui          s10, 521541
                  divu         zero, a6, t4
                  addi         a5, t0, -1423
                  slt          s3, a7, gp
                  c.srli       a2, 3
                  xori         s10, a2, -695
                  sll          s4, t2, ra
                  c.li         t5, -1
                  srli         a3, a0, 22
                  mulhsu       zero, s7, sp
                  c.addi4spn   a2, sp, 304
                  divu         zero, s5, t6
                  c.srli       a5, 12
                  srli         zero, a3, 31
                  sltiu        a3, t1, -454
                  slli         a5, s0, 13
                  c.srai       a2, 28
                  ori          t4, sp, 905
                  slli         ra, s7, 7
                  lui          s10, 598896
                  divu         s7, a2, a2
                  sra          a2, t5, tp
                  rem          t6, s5, sp
                  sltu         a7, t0, gp
                  c.li         a0, 4
                  c.addi       a6, -1
                  xori         gp, t3, 2043
                  srl          s9, s11, zero
                  c.and        s1, a4
                  mulhsu       ra, a3, s9
                  mulhu        a3, s6, s5
                  slti         a3, a2, -1144
                  divu         t2, a1, gp
                  or           s2, s8, a5
                  mulhu        s1, a6, t6
                  nop
                  c.srli       a2, 9
                  c.mv         a3, s3
                  andi         ra, a0, -1351
                  and          gp, t1, sp
                  c.xor        a3, s0
                  slli         s2, s4, 6
                  mulhsu       zero, a5, t0
                  sll          s10, s7, t0
                  mulh         gp, s1, s3
                  c.addi       s10, 7
                  c.or         s0, s0
                  c.xor        s0, s0
                  mulh         s3, s3, t5
                  sra          s8, a0, s7
                  c.srli       a0, 2
                  auipc        t1, 802568
                  c.sub        a5, a0
                  remu         s0, a6, a7
                  divu         ra, tp, ra
                  c.lui        a3, 3
                  c.slli       s2, 31
                  lui          a7, 375238
                  nop
                  ori          s9, t0, -1721
                  c.lui        t5, 17
                  sub          s3, t6, a6
                  c.xor        s0, s1
                  sra          t4, s7, s4
                  c.addi4spn   a0, sp, 960
                  c.xor        a0, a3
                  li           t4, 0x0 #start riscv_int_numeric_corner_stream_21
                  li           t0, 0xffffffff
                  li           sp, 0x80000000
                  li           t6, 0xaaad5c21
                  li           s0, 0x83acd39
                  li           a3, 0x80000000
                  li           s2, 0x799813cf
                  li           ra, 0x80000000
                  li           s5, 0xffffffff
                  li           a2, 0xffffffff
                  mulhu        ra, a3, t0
                  sub          s0, s2, s2
                  rem          s2, sp, a3
                  mulh         ra, s0, a2
                  divu         t0, s2, s5
                  rem          t0, ra, a3
                  lui          sp, 282175
                  add          ra, a2, sp
                  add          a3, a3, s5
                  mul          a3, t6, s0
                  add          sp, t0, a2
                  mulhu        sp, t6, t0
                  mulh         t0, ra, t0
                  mulhsu       ra, sp, a2
                  mulhu        t6, s0, s2
                  sub          t0, s0, sp
                  lui          t4, 638215
                  lui          t4, 578991 #end riscv_int_numeric_corner_stream_21
                  c.addi       t4, -1
                  sub          tp, a6, a1
                  c.nop
                  remu         s5, s7, t2
                  c.slli       a2, 10
                  sub          s1, t6, t2
                  mulh         t3, t6, a1
                  c.li         s0, -1
                  c.addi4spn   a5, sp, 208
                  and          s0, s2, a6
                  c.addi16sp   sp, 336
                  mulhsu       t4, s0, zero
                  mulhu        s3, a4, s9
                  sra          s11, a1, s11
                  c.xor        s0, s0
                  nop
                  xor          s1, t0, t1
                  xori         s8, a7, -1760
                  add          s5, s8, s0
                  c.srai       s0, 5
                  xor          t1, s8, s8
                  divu         s8, s7, t6
                  xori         t0, sp, 1249
                  c.sub        a2, a4
                  sltu         s7, s10, s5
                  ori          t4, s4, -2008
                  slli         sp, t6, 20
                  c.xor        a5, a4
                  sltiu        a7, sp, 131
                  sltu         a6, a4, t0
                  lui          gp, 488920
                  xori         a5, s5, -309
                  divu         s9, s11, s9
                  and          t0, t6, t3
                  div          sp, s0, a3
                  slt          zero, t6, s9
                  c.nop
                  mul          t5, gp, s5
                  ori          a5, s7, -1528
                  c.or         s0, a1
                  mul          t3, t3, a4
                  rem          sp, s6, a4
                  c.nop
                  c.addi4spn   a0, sp, 720
                  srai         a7, tp, 21
                  c.nop
                  mulh         s7, s3, a4
                  c.li         tp, 11
                  c.li         t4, -1
                  c.mv         s8, t2
                  rem          s0, s2, s6
                  and          zero, a7, s8
                  c.and        a2, s1
                  c.addi       t6, -1
                  mulhsu       s2, s6, s8
                  or           s2, a7, s7
                  c.srai       a5, 3
                  c.add        t1, s10
                  add          s11, s9, t4
                  sub          s2, a1, a4
                  mulhsu       tp, s7, s0
                  srai         s1, s3, 7
                  sra          tp, s4, s6
                  auipc        s10, 287042
                  slt          a7, a1, s9
                  xor          ra, t4, a0
                  c.xor        a0, s1
                  c.or         s1, s1
                  xor          a6, a7, s9
                  c.or         s1, s0
                  c.sub        a5, a3
                  sub          s7, a1, t4
                  sltiu        a7, a6, 1622
                  srli         s5, s7, 17
                  c.add        s0, s4
                  addi         s9, a3, -768
                  addi         t3, a5, 881
                  srli         t3, s6, 10
                  sll          s2, s0, zero
                  c.and        a3, a0
                  xor          a0, s1, a1
                  rem          ra, a2, s2
                  add          s9, sp, gp
                  slli         t5, gp, 1
                  xor          gp, ra, s3
                  c.addi16sp   sp, -16
                  addi         t6, t6, -962
                  add          s11, s1, t2
                  srli         s8, s9, 6
                  c.nop
                  addi         t6, tp, -1644
                  xori         gp, t4, 1297
                  c.slli       a6, 9
                  slli         a5, t3, 1
                  c.add        a7, a3
                  nop
                  mulhu        a5, t2, t0
                  c.and        a3, s1
                  add          a0, s6, t2
                  c.nop
                  sll          s8, a3, s4
                  slli         s9, sp, 14
                  c.addi16sp   sp, -16
                  sub          t3, s8, s6
                  mulh         s1, s11, s2
                  sra          a0, s4, a2
                  c.add        a0, a2
                  c.li         a7, -1
                  auipc        s8, 55677
                  slli         s1, t1, 22
                  ori          t3, s2, 968
                  c.srli       a0, 3
                  xor          t6, t3, s11
                  srl          s8, ra, s8
                  c.srai       a5, 21
                  sltiu        s7, a3, 1448
                  auipc        s1, 849350
                  srl          s5, s5, zero
                  addi         s0, tp, 1423
                  or           t2, a3, ra
                  c.nop
                  add          s8, zero, a6
                  slli         a7, ra, 26
                  remu         a5, zero, s2
                  c.addi16sp   sp, 160
                  andi         tp, a0, -959
                  xori         a5, a3, -1477
                  addi         a7, t2, -861
                  c.add        ra, s3
                  sll          s5, a4, a6
                  ori          s11, t5, -1668
                  mulhsu       s5, tp, s1
                  lui          a6, 568914
                  c.sub        a2, s0
                  ori          s4, zero, -1199
                  rem          s2, t4, tp
                  c.li         t1, -1
                  add          a7, a6, a0
                  c.lui        a3, 2
                  div          sp, s9, s3
                  c.mv         sp, a4
                  srli         a0, s2, 18
                  srli         s7, tp, 6
                  c.xor        s1, s0
                  ori          s11, t2, -1583
                  ori          a5, a5, 617
                  lui          a0, 688285
                  c.mv         sp, s9
                  c.mv         s2, s9
                  sub          s9, zero, a2
                  c.nop
                  div          s11, zero, s0
                  srli         s11, t5, 10
                  andi         s8, t2, 559
                  c.li         s11, 27
                  c.nop
                  mulhsu       s7, t6, a2
                  mulhu        s1, t4, a0
                  c.addi16sp   sp, -16
                  sll          t1, s7, a1
                  c.addi4spn   a5, sp, 336
                  srl          s4, s1, t1
                  srl          s2, s5, gp
                  slti         tp, a5, 19
                  add          t0, a6, s9
                  add          a0, t3, t6
                  xor          zero, sp, s9
                  sltu         t3, a7, zero
                  xori         t6, a7, 1061
                  remu         a5, zero, s5
                  divu         s7, s8, zero
                  c.mv         s3, gp
                  sltiu        a0, t5, -710
                  mul          s1, s6, s3
                  c.addi       s1, -1
                  c.add        tp, s8
                  c.lui        s7, 23
                  slli         s0, ra, 11
                  sll          s10, a0, s9
                  addi         t0, a0, -1382
                  mulhsu       s4, t2, s4
                  mulhu        s5, s2, zero
                  srl          sp, s10, t2
                  c.add        t2, a5
                  srl          t4, sp, s7
                  c.srai       a5, 2
                  rem          t3, t3, t6
                  slt          s8, s2, t3
                  rem          t5, a6, ra
                  auipc        a0, 81006
                  auipc        s1, 871218
                  xori         t2, a7, 1997
                  mulhsu       a3, t6, zero
                  c.addi       sp, -1
                  auipc        t5, 388013
                  rem          zero, t1, t6
                  rem          zero, t0, tp
                  c.addi4spn   a2, sp, 976
                  ori          ra, s1, -694
                  sltu         a7, a5, a5
                  c.sub        s0, a1
                  add          s8, a5, tp
                  ori          s5, s1, -845
                  c.addi       a2, 18
                  mulhsu       s7, a4, t0
                  slti         s10, s9, -1568
                  c.sub        s0, a5
                  srl          s11, gp, s7
                  mul          s11, s0, s8
                  c.addi       t1, 17
                  sltu         t5, s5, t4
                  c.slli       a6, 11
                  c.addi4spn   a2, sp, 288
                  c.or         a2, a2
                  c.mv         s0, a4
                  c.andi       s1, -1
                  slt          a2, zero, s1
                  c.and        a2, a2
                  rem          t4, a2, sp
                  xor          a5, a2, t2
                  c.and        a0, a5
                  and          t4, s8, a5
                  c.mv         s5, s8
                  c.addi16sp   sp, 96
                  sltu         s0, t3, s4
                  mulhu        ra, t2, s11
                  sltu         a6, a6, t0
                  div          ra, a3, t5
                  or           s9, t0, a0
                  rem          s3, ra, t3
                  mul          a5, a6, a2
                  c.srli       s1, 5
                  sll          t5, t6, tp
                  div          t1, t2, t4
                  slt          t5, t3, t1
                  mul          t1, t1, sp
                  c.addi       s1, -1
                  sub          s0, s7, t5
                  divu         s1, s4, t0
                  andi         a5, a7, -1551
                  srai         s1, s6, 12
                  xor          a2, a0, a6
                  auipc        a0, 430790
                  slt          s10, a6, a5
                  add          zero, s11, a7
                  c.nop
                  ori          gp, s9, 1996
                  c.add        sp, t4
                  nop
                  sltu         s1, s2, s5
                  sltiu        s5, s10, 1475
                  and          t0, s4, a6
                  nop
                  nop
                  remu         s11, sp, a1
                  c.slli       a0, 10
                  slti         t1, s2, -1490
                  c.add        t5, t5
                  mul          s8, a5, a6
                  c.lui        s8, 7
                  mulh         t6, s4, s2
                  c.addi16sp   sp, 64
                  c.addi4spn   s0, sp, 336
                  c.addi16sp   sp, 384
                  c.mv         s1, t4
                  slti         t2, t3, 677
                  div          t0, s4, s9
                  add          a2, t2, s7
                  slli         s8, tp, 30
                  xori         s1, a3, -141
                  sll          a0, s2, a4
                  xor          tp, s2, s10
                  slti         a3, t4, 697
                  c.srli       s0, 13
                  mulhu        t3, a3, s11
                  slti         a5, a1, 438
                  sub          s7, s4, s10
                  mulhu        zero, tp, s9
                  sltu         a7, sp, gp
                  c.sub        a0, s1
                  rem          sp, a3, a5
                  mulhu        s7, s5, a2
                  c.li         s10, 21
                  divu         t6, a6, t0
                  c.mv         s1, s0
                  rem          t4, s11, ra
                  c.nop
                  sll          s11, s9, t5
                  lui          gp, 878754
                  nop
                  divu         s2, a4, t1
                  srai         s8, a3, 28
                  mulhu        gp, s4, t1
                  nop
                  sra          zero, a2, s9
                  c.add        a6, ra
                  c.lui        s8, 13
                  remu         a2, s4, a5
                  ori          s2, a0, -1934
                  c.li         s1, 15
                  lui          s9, 766476
                  remu         s7, s11, a3
                  mulhsu       s0, t1, t3
                  mul          a3, s2, a2
                  addi         a6, tp, 338
                  c.andi       s1, -1
                  sll          sp, a6, zero
                  srl          s9, a0, a5
                  divu         gp, t1, sp
                  sll          s4, t4, s2
                  c.add        t1, a4
                  c.addi4spn   a0, sp, 800
                  mul          gp, a4, t0
                  sltu         a0, s3, t3
                  slli         s5, a6, 31
                  mulhu        a2, gp, s9
                  mulh         s7, a0, s3
                  c.addi4spn   s0, sp, 528
                  mulhu        s10, t6, t4
                  c.add        a2, s5
                  slt          s11, sp, s7
                  sra          s10, t6, ra
                  c.srli       a3, 20
                  mulh         ra, s10, ra
                  xor          t5, a5, s2
                  c.mv         s8, sp
                  andi         t3, a3, 1659
                  remu         s3, s3, sp
                  mul          ra, t4, zero
                  c.srai       a3, 28
                  addi         a5, s5, 1352
                  ori          s5, ra, 1675
                  srl          s3, t5, ra
                  sub          tp, gp, s11
                  sltiu        a3, a3, -1880
                  remu         sp, t4, a2
                  rem          a3, s1, sp
                  c.li         s0, 25
                  c.sub        s0, s1
                  mul          s11, a7, s0
                  and          t4, s1, s4
                  srl          s11, a5, s3
                  c.srai       s1, 8
                  div          s4, a0, tp
                  c.add        t1, s4
                  sub          t1, t1, s1
                  mulhu        t5, a4, s3
                  slti         s2, a1, -1567
                  c.and        a5, s1
                  nop
                  c.andi       s1, 8
                  mulh         s3, s10, a5
                  c.li         s7, 2
                  addi         t1, a1, 1172
                  div          s5, zero, a7
                  c.slli       t3, 9
                  slti         t5, s0, 1258
                  c.srai       a2, 19
                  xori         s1, t0, -1218
                  slti         a5, s2, 1889
                  c.addi       t4, -1
                  slt          sp, t0, t2
                  c.lui        s2, 9
                  c.addi       t1, -1
                  c.addi4spn   s0, sp, 448
                  c.addi16sp   sp, -16
                  sltiu        s0, t0, 1082
                  slt          t5, a7, a2
                  xor          t0, s2, s10
                  and          s3, gp, t1
                  sltu         gp, t5, s5
                  c.li         s5, -1
                  c.and        s0, s0
                  sltiu        ra, t3, 1061
                  c.sub        a2, a1
                  divu         zero, a7, t1
                  xor          ra, s8, s3
                  c.add        gp, s11
                  c.addi16sp   sp, -16
                  mulhsu       t4, s1, tp
                  remu         t3, s1, t6
                  sra          s4, s2, s2
                  slti         t0, s7, -1092
                  and          t0, s4, a0
                  divu         t4, a6, s11
                  slti         s2, t5, -1956
                  c.addi4spn   s1, sp, 96
                  or           tp, a1, s11
                  sltiu        gp, a5, -987
                  rem          a3, a2, a1
                  c.and        s0, a1
                  xori         a2, s8, -512
                  slt          tp, zero, s8
                  auipc        s8, 601050
                  c.slli       s5, 9
                  c.add        s7, s1
                  c.xor        a0, a5
                  sll          gp, tp, s3
                  srai         s9, s2, 19
                  nop
                  or           t0, sp, t2
                  and          s0, gp, gp
                  srli         s7, s3, 6
                  sll          t1, t2, a7
                  slli         t1, a3, 10
                  divu         s9, a1, zero
                  sltiu        sp, s11, 986
                  xori         s2, a1, -1187
                  c.addi16sp   sp, -16
                  div          s4, t6, s1
                  xori         s4, sp, 262
                  sub          s7, t2, a6
                  srl          ra, tp, s8
                  xori         s5, s10, 318
                  c.or         s0, a3
                  mul          ra, s4, s5
                  remu         t5, a6, t2
                  slli         t6, s8, 13
                  srl          s0, s8, a0
                  and          t2, s3, s5
                  sra          s9, a7, zero
                  c.srli       s1, 26
                  nop
                  slli         a7, s5, 22
                  auipc        s10, 923448
                  c.addi16sp   sp, -16
                  mulhu        s2, t2, gp
                  c.addi       tp, -1
                  c.addi       sp, 19
                  slt          s8, sp, tp
                  mul          s3, a6, tp
                  srli         s10, s11, 3
                  and          s7, a0, a6
                  div          s3, t6, s2
                  c.xor        a5, a1
                  add          t1, s11, ra
                  c.nop
                  c.slli       s11, 19
                  xor          a6, t1, a7
                  c.addi4spn   a5, sp, 64
                  c.sub        a0, s1
                  slt          a3, t3, s7
                  srli         s11, s3, 17
                  slti         s8, a3, -782
                  c.or         a2, s0
                  c.addi       s5, -1
                  c.slli       a5, 31
                  srli         s0, t2, 26
                  nop
                  mulhu        a7, a7, a6
                  srl          t2, sp, t1
                  c.xor        a5, a3
                  c.addi4spn   a2, sp, 688
                  auipc        s4, 716681
                  slli         s3, s10, 25
                  c.li         t2, -1
                  mulh         t3, a0, t1
                  c.addi16sp   sp, -16
                  sltu         s9, t6, a1
                  add          s10, s3, a4
                  add          a5, t6, s10
                  remu         s4, s11, s10
                  c.add        ra, s1
                  and          t2, s10, a7
                  sltu         a5, a7, a5
                  addi         s10, s9, 89
                  c.nop
                  c.lui        s8, 15
                  or           t0, t0, s2
                  c.sub        s0, a5
                  sltu         a3, t3, s8
                  c.addi4spn   s1, sp, 352
                  ori          s1, tp, 1215
                  remu         t2, s2, s7
                  sra          a0, gp, s6
                  c.mv         t4, t2
                  mulh         a7, a0, s1
                  divu         s10, s8, sp
                  sub          a3, gp, a4
                  xor          ra, s8, s3
                  c.li         a6, 6
                  slt          t3, a1, s5
                  rem          tp, a4, s1
                  xori         s10, t6, -412
                  div          s9, s1, tp
                  and          t6, s9, a7
                  c.and        a0, s1
                  rem          s3, s5, t6
                  srai         t2, t2, 23
                  srl          t6, a1, t2
                  c.li         s7, -1
                  slti         tp, t1, -855
                  c.addi4spn   a2, sp, 112
                  nop
                  sltiu        a3, a7, -1365
                  mulh         sp, zero, a6
                  add          t2, a2, s3
                  c.and        s0, a4
                  c.andi       a3, -1
                  nop
                  mulhu        t2, tp, sp
                  srai         gp, s5, 22
                  c.and        s1, s0
                  sltiu        s7, s6, -1966
                  srl          t0, a4, s6
                  c.nop
                  c.or         a0, a1
                  c.lui        s2, 26
                  c.addi       t1, 20
                  srl          t5, zero, s1
                  c.andi       a2, 4
                  addi         s1, zero, 390
                  slli         t2, sp, 7
                  c.xor        a3, s0
                  c.addi       s3, 21
                  c.addi       s2, -1
                  c.addi4spn   a3, sp, 432
                  c.sub        a0, s0
                  mulhu        s11, t0, sp
                  ori          s3, a2, 798
                  c.mv         t4, a2
                  c.addi16sp   sp, -16
                  c.slli       t1, 27
                  mulhu        t4, a1, s11
                  add          a5, s4, s0
                  mulhu        s1, s1, a6
                  srli         a5, a0, 25
                  lui          sp, 181567
                  srai         ra, gp, 24
                  xori         s3, a1, 1495
                  mulhu        s11, t3, s1
                  rem          s8, a7, s10
                  xor          s9, tp, s11
                  slt          a7, a2, s7
                  c.and        s0, a5
                  sltiu        a3, t6, 1304
                  c.nop
                  mulhsu       ra, s0, a0
                  sra          a3, a5, sp
                  c.or         a2, s1
                  c.addi4spn   a3, sp, 368
                  and          ra, s8, t6
                  mulh         t6, t1, t6
                  c.lui        t3, 3
                  div          a2, s4, a2
                  c.add        a2, ra
                  c.addi4spn   a3, sp, 560
                  and          s1, a7, t1
                  andi         s1, t2, 325
                  div          s8, a0, t5
                  c.addi4spn   s1, sp, 128
                  mulhsu       a2, s6, s3
                  c.mv         sp, s9
                  ori          s10, t1, 1894
                  or           t4, tp, t1
                  sltu         sp, a0, t0
                  nop
                  c.lui        s4, 30
                  and          s5, a7, s9
                  c.or         a2, a1
                  sltiu        s1, s0, 1628
                  xor          s2, s9, s10
                  sll          t5, s10, sp
                  remu         t4, a3, gp
                  c.or         s0, a4
                  slli         a5, a2, 4
                  mulhsu       t5, s1, s1
                  c.andi       s0, 31
                  c.add        tp, s0
                  xori         sp, a2, -450
                  li           s0, 0xffffffff #start riscv_int_numeric_corner_stream_37
                  li           s11, 0x80000000
                  li           tp, 0x0
                  li           t3, 0x80000000
                  li           s1, 0x80000000
                  li           a5, 0xffffffff
                  li           s9, 0x80000000
                  li           t6, 0x0
                  li           s4, 0x0
                  li           s7, 0xde1a2485
                  remu         s11, s9, tp
                  rem          s9, s11, t6
                  rem          t6, s9, a5
                  mulh         s0, t3, s11
                  mul          t6, s7, s11
                  nop
                  mulh         s11, s1, s11
                  nop
                  sub          s0, s7, tp
                  sub          s11, s0, s9
                  add          s0, a5, s1
                  mulhu        t6, s1, t6
                  mulhsu       s7, t3, t6
                  rem          s4, tp, s11
                  mulhu        s0, tp, t3
                  divu         s1, t6, s11
                  addi         t6, s11, 1893
                  mulhsu       a5, t3, s7
                  mulhu        s11, s0, s4
                  sub          s0, s9, t6
                  lui          s1, 701666
                  auipc        s11, 177344
                  sub          s1, a5, s9
                  lui          s11, 949469
                  mulhsu       s9, a5, a5 #end riscv_int_numeric_corner_stream_37
                  andi         gp, s8, -1873
                  div          s3, a1, s9
                  slti         t4, a0, 1954
                  c.addi16sp   sp, 64
                  div          t4, s9, t5
                  c.sub        s0, s0
                  srl          tp, t6, s9
                  xor          a6, tp, t1
                  xor          s10, s1, a4
                  remu         sp, t6, s6
                  srl          t1, tp, s5
                  ori          s9, t6, 2003
                  sltiu        t2, s9, -163
                  c.and        s1, s0
                  nop
                  c.or         s0, s1
                  sub          s10, s2, zero
                  slti         t5, tp, 1404
                  c.xor        a0, a0
                  c.srai       s1, 24
                  sra          ra, t5, t6
                  lui          tp, 107182
                  srl          s8, s1, a7
                  divu         s1, s1, s8
                  c.or         s0, a1
                  c.sub        a5, a2
                  c.mv         s1, s3
                  divu         s8, s4, a5
                  mulhu        t5, s3, s11
                  slli         s10, s11, 16
                  mulhu        s5, s6, s10
                  sltu         a5, s10, a6
                  c.lui        t3, 15
                  c.add        t3, tp
                  andi         ra, s2, -246
                  addi         tp, sp, 761
                  srli         s5, ra, 29
                  c.andi       a0, -1
                  srai         t3, s3, 28
                  c.add        ra, s9
                  mulhsu       ra, t5, gp
                  c.li         gp, 29
                  c.or         a3, s0
                  srl          s11, gp, t2
                  c.srai       a5, 30
                  c.nop
                  c.addi16sp   sp, 416
                  or           t4, a3, gp
                  or           a0, s5, t2
                  and          t2, s7, sp
                  add          t1, s6, s9
                  sra          a3, t6, a5
                  andi         t2, t5, 1794
                  slli         s4, t5, 7
                  ori          s8, a2, 1837
                  mul          s2, s11, t5
                  c.and        s0, a3
                  and          ra, t1, t1
                  c.and        a0, a1
                  c.nop
                  c.li         s4, -1
                  slli         t4, t3, 9
                  nop
                  c.lui        t1, 24
                  sub          s9, t3, s3
                  c.nop
                  mul          t3, zero, sp
                  sltu         a5, s3, s10
                  sub          a2, s4, s4
                  c.li         s2, -1
                  c.lui        t4, 19
                  c.andi       a5, -1
                  c.addi16sp   sp, -16
                  slt          a5, t6, s9
                  or           s4, gp, s9
                  c.and        s1, a2
                  c.nop
                  lui          tp, 148026
                  divu         s7, t4, t2
                  mulhsu       a5, t6, s6
                  mulhu        s2, t6, t6
                  sltu         t4, t1, s1
                  mulhu        t5, gp, s11
                  slli         tp, a7, 16
                  sltiu        t5, a1, -898
                  sub          s2, t3, s9
                  slti         gp, a3, -326
                  c.li         s5, -1
                  mulhsu       sp, a2, a3
                  andi         t6, t5, -548
                  srl          s8, a4, a2
                  c.li         t2, -1
                  mulh         s10, s11, s4
                  lui          a3, 644750
                  c.add        s4, s0
                  c.srai       a0, 24
                  sll          s7, t6, t0
                  divu         s4, a7, t2
                  sll          t0, a1, t3
                  c.addi4spn   s0, sp, 688
                  srl          a6, s8, a6
                  c.addi16sp   sp, 144
                  or           t4, zero, t2
                  c.or         a2, a3
                  sll          a2, tp, gp
                  addi         s2, s10, -495
                  srl          a2, s6, s9
                  rem          zero, t5, t5
                  mulhu        sp, s3, a7
                  remu         s8, s6, a1
                  c.mv         s5, tp
                  sltu         t0, s5, t0
                  c.xor        a5, a5
                  rem          a5, s7, s4
                  sll          s5, s5, s7
                  c.nop
                  srai         sp, t5, 18
                  nop
                  c.and        s0, a2
                  c.xor        a3, s1
                  add          t5, a0, s9
                  rem          t5, s5, tp
                  c.addi       a5, -1
                  div          a2, t5, s11
                  lui          tp, 349807
                  divu         t3, t1, sp
                  lui          s4, 126367
                  sll          t5, zero, a6
                  ori          a6, a7, -626
                  c.add        t1, t6
                  srai         tp, t0, 17
                  xor          t0, t2, t5
                  srli         t6, zero, 9
                  c.nop
                  xor          s2, a7, a5
                  c.lui        s3, 6
                  or           t2, s9, s4
                  div          a3, s2, t3
                  c.addi       s7, -1
                  andi         t0, a0, 300
                  srli         a3, s5, 21
                  nop
                  add          s10, a7, s5
                  c.srli       a3, 20
                  slt          sp, t5, s6
                  c.andi       s1, 7
                  andi         s10, t3, -1952
                  c.xor        a3, a4
                  lui          t4, 454566
                  mulhu        s7, s8, a2
                  c.srai       a5, 5
                  ori          s8, t4, -208
                  mulhu        s4, s11, s6
                  c.addi4spn   a2, sp, 960
                  ori          tp, s3, 915
                  sltiu        ra, s3, -1940
                  srl          t6, s0, s8
                  c.addi4spn   a5, sp, 176
                  div          t3, a1, t5
                  nop
                  li           s1, 0xffffffff #start riscv_int_numeric_corner_stream_12
                  li           a7, 0xffffffff
                  li           t4, 0x80000000
                  li           t5, 0xffffffff
                  li           a6, 0x3eada90b
                  li           a3, 0x7f1e59b
                  li           ra, 0x0
                  li           s4, 0x0
                  li           t3, 0x80000000
                  li           a5, 0xffffffff
                  add          s4, s4, ra
                  mulhsu       t5, t5, t4
                  addi         t5, s1, -1394
                  mulhsu       s1, t5, t4
                  sub          s4, s4, t3
                  mul          t3, ra, t4
                  sub          a3, t3, s1
                  mul          t5, ra, a5
                  auipc        ra, 702991
                  add          a6, ra, a3
                  nop
                  auipc        s1, 301885
                  addi         a5, a5, -1672
                  mulh         a7, t5, t5
                  mulh         a3, a5, s1
                  remu         t5, t3, a5
                  lui          t3, 307045
                  mulhsu       ra, s1, a7
                  rem          a7, a6, t3
                  rem          t5, s4, t3
                  lui          s4, 535952
                  sub          s4, t4, s4
                  div          a7, t3, t5
                  addi         t5, t3, 211
                  divu         a7, a6, t3
                  mulhu        a5, t3, t4
                  mul          a7, t4, s4
                  rem          t3, t4, t5
                  add          a3, ra, s4 #end riscv_int_numeric_corner_stream_12
                  c.nop
                  c.sub        a2, s1
                  c.andi       a2, -1
                  srai         s5, s4, 22
                  ori          s4, zero, -1341
                  div          t1, s9, t2
                  c.li         a6, -1
                  c.slli       a2, 5
                  srl          sp, a4, a7
                  and          s5, s10, t2
                  c.or         s0, a1
                  rem          s10, s0, s11
                  c.addi16sp   sp, -16
                  xori         sp, sp, 1027
                  xor          t2, a1, a3
                  mulh         s8, t2, s2
                  div          s7, s5, s8
                  div          a2, a3, sp
                  c.sub        a0, s1
                  mulhu        t1, s0, t1
                  addi         t0, s8, -1793
                  sltiu        t5, a6, -1445
                  c.addi       a7, 1
                  remu         s4, s6, t1
                  c.and        a5, s1
                  xori         t2, s7, 1895
                  c.and        a0, a0
                  ori          zero, gp, 1702
                  mulhsu       a3, a7, t0
                  c.srli       a3, 12
                  c.nop
                  srli         zero, s10, 7
                  c.or         a5, a1
                  mulhu        s7, s9, s0
                  andi         tp, s10, 215
                  sltiu        s11, s2, -173
                  c.nop
                  c.addi16sp   sp, -16
                  sltu         s11, t5, t2
                  sll          a2, s11, s7
                  xori         t1, a5, -914
                  addi         t6, s6, 890
                  div          ra, tp, zero
                  remu         a3, s8, s0
                  srl          s4, a3, a6
                  sra          s10, t0, ra
                  c.addi4spn   a2, sp, 368
                  sra          t2, s8, t6
                  mul          s2, tp, a3
                  c.add        s0, s0
                  c.mv         t6, t1
                  slli         s8, s11, 16
                  srl          gp, sp, sp
                  nop
                  sll          t6, t0, s5
                  c.or         s1, a1
                  sltiu        s11, s3, -1064
                  c.addi4spn   a0, sp, 384
                  sll          s1, t3, sp
                  sltu         t5, s8, t6
                  c.andi       a3, -1
                  auipc        s0, 45851
                  andi         t2, gp, -312
                  divu         s9, a1, t5
                  slli         s5, a0, 15
                  c.mv         ra, tp
                  add          s3, t3, a5
                  c.srai       a5, 6
                  c.lui        s11, 1
                  c.lui        s7, 22
                  sll          t2, a0, a3
                  sltu         sp, ra, t2
                  auipc        a6, 968554
                  srli         s2, a7, 12
                  slti         s7, t2, 397
                  mulh         a6, a4, a3
                  sltiu        t6, s0, 1984
                  srl          s0, a7, s7
                  slt          a5, s9, s9
                  lui          s1, 506012
                  srai         t1, s11, 29
                  mulhsu       t3, tp, t1
                  xor          s1, t2, s9
                  mulhsu       sp, s2, s10
                  c.mv         s0, s1
                  srl          s1, sp, t5
                  auipc        t5, 909831
                  mulhu        s4, a6, a4
                  c.or         a3, a1
                  c.sub        a0, s1
                  c.srai       s1, 22
                  c.lui        s9, 27
                  c.andi       s1, 1
                  andi         a5, s11, 1314
                  auipc        t0, 112562
                  andi         ra, ra, -1700
                  c.slli       s4, 29
                  nop
                  sltiu        a7, a6, 1335
                  slti         a6, a6, -1323
                  mulh         t6, s7, sp
                  c.srai       a3, 13
                  c.addi       ra, 17
                  lui          t6, 854896
                  srli         s11, t1, 27
                  c.andi       s0, -1
                  c.srai       a2, 11
                  c.addi       s5, -1
                  sltiu        t6, a1, -1768
                  xori         s10, a6, -240
                  c.or         s1, a1
                  c.andi       a3, -1
                  nop
                  c.sub        a0, a3
                  lui          a6, 140061
                  c.nop
                  sltu         s1, ra, s3
                  slli         t1, t4, 27
                  div          a6, a2, a6
                  c.lui        s7, 26
                  c.addi4spn   s1, sp, 64
                  c.sub        s0, a0
                  c.and        a2, s1
                  c.andi       a2, -1
                  ori          t5, a1, -1616
                  sltu         ra, t6, a3
                  ori          gp, t5, -1211
                  c.xor        s0, a1
                  addi         a6, s11, -455
                  c.addi       s0, 8
                  andi         s4, a3, 1939
                  sltiu        t6, s2, -1639
                  slti         zero, s0, -1878
                  c.nop
                  mulhsu       zero, t3, t6
                  or           a3, s5, zero
                  or           s8, gp, a3
                  c.xor        a2, a1
                  sub          s3, a4, t0
                  c.li         s7, -1
                  xor          zero, a2, a3
                  c.and        s1, a1
                  lui          a7, 667948
                  c.addi16sp   sp, -16
                  ori          a3, t2, 180
                  slti         s10, a1, 319
                  xor          t3, s5, t1
                  or           gp, s9, zero
                  nop
                  nop
                  remu         gp, s2, s0
                  mulhsu       a7, a0, s0
                  xor          t6, s5, a6
                  c.andi       a3, 3
                  c.mv         s7, s8
                  sltu         s4, a7, s1
                  sra          s0, ra, s6
                  sltu         gp, t6, a4
                  auipc        a7, 632370
                  c.sub        s0, a1
                  c.mv         s10, s8
                  c.and        a0, a0
                  c.or         a2, a4
                  c.addi4spn   a3, sp, 608
                  mulhsu       s7, t4, zero
                  slti         s11, a1, -324
                  xori         gp, a4, 1587
                  addi         gp, s9, 1117
                  c.addi4spn   a2, sp, 832
                  xor          s9, t2, a3
                  c.srai       a2, 24
                  c.addi       sp, 16
                  c.lui        t4, 1
                  srli         t3, s10, 23
                  addi         s3, a7, 1009
                  c.lui        s10, 9
                  c.slli       s9, 29
                  c.srai       s1, 25
                  c.xor        s1, a0
                  and          s8, s10, a2
                  slti         s0, a5, 174
                  remu         s8, sp, a0
                  srli         a0, s3, 0
                  add          s2, a4, s7
                  c.sub        a3, a2
                  mulhsu       t1, t2, t5
                  and          t5, zero, t6
                  sll          s10, a7, t4
                  mulh         t4, s1, t6
                  ori          a3, s8, -525
                  xor          t0, s0, s5
                  c.lui        a2, 11
                  addi         s8, a7, -239
                  sll          s3, s6, a2
                  slt          s10, t4, s1
                  andi         s5, s4, -1597
                  c.mv         a7, a5
                  c.slli       s1, 30
                  mulh         s7, tp, a2
                  sltiu        s10, a0, -350
                  c.and        a5, s0
                  add          a0, t3, a4
                  or           s7, a3, s0
                  mul          s1, s8, s8
                  mulhu        s3, s1, t3
                  slti         s5, a5, -1335
                  slli         s0, tp, 19
                  srl          s11, ra, t5
                  rem          a6, s11, a1
                  c.addi4spn   s0, sp, 624
                  c.srli       a0, 24
                  c.slli       a5, 20
                  c.addi16sp   sp, -16
                  xor          a2, t2, a0
                  slti         t5, sp, -165
                  lui          a6, 1002404
                  c.and        a2, a5
                  c.addi4spn   a3, sp, 272
                  rem          a0, gp, s6
                  mulhu        t6, t1, tp
                  sltu         s11, t3, t0
                  sub          a5, a2, a1
                  srai         t0, tp, 9
                  c.addi16sp   sp, -16
                  srl          t5, s7, a0
                  add          s11, s2, s6
                  c.or         a2, a5
                  lui          a5, 500607
                  c.addi4spn   s0, sp, 784
                  c.nop
                  c.addi16sp   sp, -16
                  andi         s11, s8, -1031
                  c.xor        a2, a5
                  sub          s3, a7, zero
                  auipc        s4, 103054
                  xor          s10, ra, t1
                  remu         a6, t0, t3
                  sra          sp, t5, s1
                  sltiu        sp, sp, -790
                  sltu         s1, t0, a7
                  srl          s11, a0, s10
                  or           s2, t6, a7
                  lui          t2, 688313
                  c.slli       s3, 17
                  sltiu        a0, s2, 2013
                  c.slli       s8, 5
                  c.and        a0, a3
                  div          ra, s4, a0
                  sll          t6, a4, s10
                  c.slli       t0, 17
                  c.srai       a3, 23
                  lui          t0, 670145
                  sub          s11, zero, t1
                  nop
                  c.srli       a5, 15
                  mulh         t2, s4, a5
                  sltiu        a3, s11, 1285
                  sll          s2, s7, s10
                  c.addi4spn   a3, sp, 560
                  div          s11, sp, s8
                  slti         a5, s9, 1598
                  c.sub        a3, a0
                  auipc        t4, 875524
                  c.addi       s4, 27
                  sll          t3, s0, a3
                  and          s9, a2, a2
                  xor          t0, s6, ra
                  or           s2, ra, s11
                  or           t5, s5, t2
                  c.addi16sp   sp, -16
                  mulhsu       a5, zero, s1
                  mul          t3, s6, s0
                  c.srli       a5, 14
                  remu         tp, s6, s4
                  lui          a3, 63754
                  c.srai       s1, 21
                  mulhu        s11, s3, s11
                  slti         a6, t1, -380
                  ori          tp, sp, -2031
                  c.srai       s1, 28
                  c.and        a0, a1
                  c.addi       a2, 8
                  mulh         a7, s0, t6
                  c.and        s0, a1
                  divu         a5, s7, s10
                  c.li         a7, 1
                  sltiu        ra, a1, -632
                  mulhsu       s9, s9, s6
                  c.li         s0, 2
                  c.lui        s1, 1
                  c.srai       a5, 2
                  nop
                  ori          t5, a5, -835
                  ori          a0, t0, 1451
                  divu         s7, a7, t2
                  remu         a6, s9, a0
                  slt          s5, s9, t4
                  addi         s11, a0, 618
                  addi         t4, a5, -879
                  c.sub        a3, s1
                  mulhsu       s3, a0, s7
                  rem          t2, tp, t5
                  remu         s4, sp, sp
                  mulhsu       t5, s10, s5
                  srl          a7, t0, a5
                  c.nop
                  and          s7, a0, zero
                  lui          s5, 423214
                  c.lui        s11, 10
                  c.xor        a3, s0
                  xori         t0, s6, 1267
                  c.sub        a5, s0
                  c.or         a2, a4
                  add          t6, a5, s11
                  sltiu        s2, a4, 1736
                  c.addi16sp   sp, -16
                  addi         s9, s7, 561
                  c.mv         tp, s3
                  mul          s5, s11, a0
                  mulhsu       s3, tp, gp
                  andi         a5, s1, 1969
                  mulhsu       t1, a6, a1
                  div          t6, s2, s8
                  add          a7, sp, s9
                  c.add        s3, t5
                  xor          ra, t6, a3
                  slli         s0, a6, 18
                  auipc        t4, 262341
                  sub          gp, ra, s0
                  sltu         gp, s9, s7
                  xor          t6, a1, gp
                  c.addi16sp   sp, -16
                  srli         s4, t0, 24
                  and          s3, t5, t2
                  c.addi       s11, 2
                  divu         t4, t6, s0
                  c.andi       a0, 22
                  c.xor        a2, a2
                  xori         s4, a0, -1521
                  c.srli       a2, 31
                  c.addi16sp   sp, 368
                  c.xor        a5, a4
                  c.and        s0, a5
                  mul          a6, s5, t6
                  xor          t4, s2, s2
                  srli         t2, s10, 6
                  c.lui        s11, 17
                  sltiu        a7, t6, 1581
                  slli         gp, zero, 4
                  sltiu        a6, a3, -518
                  or           zero, s6, a3
                  nop
                  c.sub        a0, s0
                  c.addi4spn   a3, sp, 32
                  div          gp, sp, s2
                  c.addi4spn   s0, sp, 656
                  mulh         t1, s7, t4
                  remu         t4, t6, a4
                  xor          s3, gp, ra
                  addi         a0, s9, 956
                  c.sub        a5, a5
                  c.sub        s0, a5
                  c.andi       a0, 8
                  lui          t6, 833060
                  srl          t3, s4, a1
                  mulhsu       t4, t2, t1
                  c.srai       a2, 20
                  c.srli       a3, 22
                  mulhu        a2, ra, ra
                  srli         s8, a4, 1
                  srai         tp, gp, 25
                  srai         s0, s1, 18
                  c.srai       a5, 9
                  div          s4, a4, s5
                  mulh         a7, s1, s11
                  lui          a7, 660572
                  sub          ra, ra, gp
                  and          s7, a2, s8
                  divu         t2, a4, t5
                  c.addi16sp   sp, 416
                  slt          s5, t3, s0
                  c.lui        s1, 2
                  xori         s1, t0, -1545
                  and          t3, s4, t0
                  c.andi       s0, 19
                  c.li         sp, -1
                  sll          s11, s3, a2
                  or           s9, s3, a2
                  div          s11, s3, a4
                  slt          t3, a7, s0
                  c.srli       s0, 15
                  sub          a3, tp, s9
                  slt          t5, a1, sp
                  sll          s11, a7, s0
                  srai         s3, s5, 5
                  and          sp, zero, s1
                  sll          a2, a4, s0
                  ori          s8, t0, -74
                  addi         gp, tp, -697
                  c.and        a3, a2
                  srli         a2, a3, 13
                  c.nop
                  srl          t1, t1, t2
                  mulhsu       s7, a3, t0
                  div          s8, a2, s5
                  sltu         s1, s7, a5
                  c.li         s3, 3
                  remu         zero, a1, tp
                  mul          s11, a5, t1
                  c.lui        s7, 9
                  slli         s2, t2, 3
                  c.or         s1, a4
                  xori         t5, gp, 795
                  sltu         s1, ra, sp
                  mul          s8, s8, t2
                  mulh         s10, tp, a5
                  mul          s2, a4, s3
                  slti         a0, t6, -546
                  c.sub        a2, s1
                  slli         s1, t3, 3
                  slli         s0, t2, 2
                  c.lui        s3, 22
                  c.add        s10, tp
                  c.addi       s7, 3
                  and          s9, s11, s2
                  xor          t4, a0, gp
                  c.addi       s9, 21
                  and          s0, zero, t6
                  divu         t2, s4, zero
                  slti         a2, s7, 1724
                  c.slli       s11, 5
                  srl          s5, a6, t2
                  srl          t0, t4, a6
                  sltiu        a7, s9, -1999
                  srli         a6, ra, 0
                  andi         a3, t4, 759
                  c.addi16sp   sp, -16
                  mulhu        s10, s10, t3
                  mulhsu       s4, s10, a4
                  andi         gp, a2, -248
                  ori          tp, sp, 13
                  c.andi       a0, -1
                  c.andi       s1, -1
                  lui          zero, 423855
                  c.srli       a3, 5
                  div          s3, s7, s11
                  c.li         a0, 17
                  nop
                  mulhsu       s7, a7, s5
                  divu         t3, s6, t0
                  c.srai       a2, 4
                  auipc        s1, 839838
                  c.and        a5, a5
                  div          a5, t4, s0
                  nop
                  sltu         ra, s7, t3
                  nop
                  xor          a0, s11, s0
                  mulh         tp, a4, a1
                  c.li         s3, -1
                  add          s11, s5, a2
                  mul          s5, s8, a4
                  c.addi16sp   sp, -16
                  or           t1, s0, s7
                  c.mv         t2, s5
                  sltiu        ra, ra, 1850
                  c.mv         s8, t1
                  andi         s1, t1, 1443
                  add          tp, s10, a0
                  xor          s7, sp, zero
                  c.addi       t3, 5
                  srli         s7, s4, 18
                  sub          s4, s5, tp
                  slt          s0, a7, zero
                  nop
                  or           t3, tp, a2
                  srai         s9, s8, 21
                  srli         t3, a4, 10
                  mulhsu       s1, s1, sp
                  c.slli       s10, 30
                  or           s4, s11, a0
                  srli         s5, s11, 19
                  c.srli       a5, 1
                  sra          a7, s1, a7
                  ori          s5, s7, -391
                  ori          t2, s10, 578
                  c.nop
                  mulhu        s7, s5, t2
                  remu         a6, s8, s4
                  mulh         s8, s8, gp
                  c.mv         a5, s6
                  nop
                  c.add        ra, s10
                  c.addi4spn   s0, sp, 400
                  srl          s11, s9, a0
                  ori          t0, s6, 946
                  c.addi       t3, 12
                  sra          a2, t0, t4
                  ori          t6, ra, -282
                  c.andi       a2, -1
                  xor          t0, tp, s6
                  remu         t3, sp, s6
                  c.li         a2, 13
                  c.lui        s0, 25
                  andi         s9, t0, 968
                  sll          s1, s10, s1
                  srli         a7, s10, 29
                  sltu         s10, s11, a1
                  c.slli       t0, 7
                  sltu         s0, t1, s4
                  mulhsu       s9, s6, gp
                  ori          s11, a0, 416
                  c.or         a0, a5
                  sltu         tp, a4, t4
                  srl          a3, s6, t6
                  c.li         s2, 13
                  lui          a2, 236264
                  c.and        a5, a4
                  c.and        s0, a4
                  sltu         t5, s4, t1
                  slt          t2, t2, ra
                  c.sub        s0, a3
                  c.lui        a2, 11
                  nop
                  c.srai       s0, 3
                  c.xor        a2, a1
                  srli         s8, a2, 4
                  slt          t0, a0, t5
                  sub          s1, s0, t6
                  c.add        s3, s1
                  and          s4, s4, s7
                  mulhu        t6, a4, s2
                  nop
                  sub          zero, gp, a1
                  ori          t1, a4, 110
                  c.mv         s2, s7
                  add          a2, s10, s5
                  andi         a3, t4, -574
                  remu         gp, tp, s0
                  addi         sp, a6, 680
                  sltiu        t0, t1, 1688
                  divu         t5, t0, a0
                  or           t5, s5, s9
                  c.and        s0, a3
                  addi         t3, t3, 1788
                  c.or         s1, a2
                  nop
                  c.slli       s7, 10
                  ori          s2, a5, -184
                  slli         t5, t4, 11
                  and          a7, s10, s7
                  c.add        ra, a2
                  sltu         a5, s1, a4
                  c.srli       a3, 4
                  srli         t3, a6, 12
                  srai         s3, a7, 14
                  c.lui        t4, 27
                  sub          s1, s0, s2
                  slt          s3, s3, s5
                  c.nop
                  ori          s7, s6, -551
                  ori          t5, a7, -286
                  sltu         t6, s9, tp
                  or           t2, t4, a0
                  c.xor        a3, a3
                  rem          s11, a7, s0
                  or           s10, t3, tp
                  c.srli       s0, 5
                  c.andi       s1, -1
                  xor          t0, s1, s7
                  c.mv         a5, sp
                  c.srai       a3, 26
                  slti         ra, a7, 2019
                  srai         ra, s4, 16
                  and          a7, t3, s10
                  c.addi4spn   s0, sp, 304
                  sll          s11, s8, t5
                  mulhsu       tp, s5, s8
                  xor          t1, t5, sp
                  mulhsu       a7, t5, a4
                  c.and        a2, a3
                  ori          sp, zero, -824
                  srli         ra, a2, 13
                  c.and        a5, a1
                  rem          s5, s1, gp
                  c.addi       a5, -1
                  sra          a3, a4, s4
                  c.lui        a5, 7
                  ori          s8, tp, -520
                  mul          ra, s9, s11
                  c.sub        a0, s0
                  divu         t4, a7, s1
                  andi         s10, s7, -846
                  c.addi       a6, 7
                  andi         s4, gp, 1632
                  c.addi       t2, -1
                  slt          a6, ra, t1
                  c.li         sp, -1
                  sltiu        s7, a0, -1263
                  slti         t4, a5, 1003
                  xor          a3, s1, s4
                  c.andi       a2, 27
                  c.mv         s0, a7
                  srai         a2, s2, 28
                  div          ra, a2, t0
                  sll          s0, a1, gp
                  mulhu        s3, t2, a5
                  divu         a2, s3, s9
                  c.addi       s5, 9
                  c.srai       a0, 26
                  sltiu        a5, a5, 637
                  xor          s2, t2, sp
                  c.nop
                  auipc        t2, 609076
                  ori          zero, a6, 363
                  andi         s2, s11, 166
                  rem          t2, s6, zero
                  nop
                  mulhsu       t4, gp, t4
                  sra          a6, s6, s8
                  slti         gp, s6, 1090
                  mulh         gp, a7, s1
                  c.srli       s1, 13
                  sltiu        sp, ra, -45
                  and          s1, t3, t2
                  div          a7, a5, s5
                  slli         s11, s4, 24
                  c.srli       a0, 11
                  addi         s5, t3, 1551
                  c.or         a3, s0
                  c.addi4spn   s1, sp, 48
                  lui          a2, 623323
                  xori         t4, s0, 1347
                  srai         s9, a4, 22
                  c.addi       s7, -1
                  addi         t3, sp, -1077
                  c.srai       a3, 1
                  c.srai       s1, 11
                  sltu         a3, t4, s4
                  sra          zero, s4, tp
                  xori         s7, s6, 976
                  c.li         a5, 25
                  addi         sp, a2, -1589
                  sub          a0, t5, s11
                  c.sub        a5, a0
                  c.or         a0, a2
                  c.slli       s11, 28
                  srai         s9, gp, 24
                  mulh         s8, s3, t1
                  c.nop
                  srl          a5, s7, a1
                  slli         a2, a7, 4
                  srl          a6, t6, s4
                  c.nop
                  sll          s9, s11, s9
                  c.or         s1, a0
                  c.xor        a0, s0
                  xor          sp, t6, a0
                  c.or         a0, a1
                  srai         zero, s7, 2
                  c.li         a7, -1
                  srl          a0, sp, t0
                  srli         s11, a5, 27
                  c.srai       a3, 24
                  c.add        s10, s8
                  divu         s8, a0, a3
                  auipc        s9, 112122
                  auipc        s5, 1016108
                  or           gp, a3, ra
                  c.andi       a5, -1
                  c.srai       a5, 21
                  sll          s5, zero, tp
                  c.li         s5, 29
                  mul          tp, t0, t5
                  c.li         a7, 2
                  c.srli       s0, 19
                  rem          s7, s1, t6
                  c.and        a2, a0
                  c.addi4spn   a5, sp, 432
                  sltu         s9, s9, s3
                  c.and        a2, s1
                  addi         gp, s1, -1179
                  slt          t2, t2, s6
                  c.mv         s2, s2
                  divu         a7, sp, t1
                  or           t1, a1, s8
                  srl          t4, a2, t1
                  c.xor        s1, a2
                  ori          ra, a6, -246
                  lui          a5, 951558
                  xori         a2, s11, 1712
                  remu         s7, a3, t4
                  srli         s9, zero, 15
                  auipc        s4, 23065
                  c.li         s9, -1
                  sltu         s8, s7, a6
                  c.mv         t6, s0
                  c.srai       a3, 3
                  c.lui        t4, 4
                  c.srli       a2, 3
                  c.addi       s4, -1
                  mul          gp, s3, a1
                  mul          s4, a7, tp
                  slt          t4, s10, a2
                  srl          a7, s11, a3
                  add          s0, s5, a2
                  ori          s8, s2, -1377
                  c.sub        a0, a3
                  lui          s7, 322989
                  c.andi       a3, -1
                  divu         t0, a4, a5
                  c.sub        a2, a4
                  mulhu        a3, gp, a5
                  sltiu        t3, s2, 1873
                  c.or         s1, s1
                  c.slli       a6, 20
                  remu         s2, s3, a3
                  remu         ra, s6, s8
                  sub          t6, sp, t5
                  nop
                  auipc        t0, 876633
                  ori          a2, s7, -1015
                  c.nop
                  sll          t1, s9, sp
                  or           s9, s3, s2
                  add          t1, s9, t2
                  sltu         s3, a2, sp
                  divu         a3, tp, s4
                  slt          gp, s8, s6
                  c.li         ra, 6
                  remu         s3, a2, s4
                  slti         s5, a7, -421
                  sub          a7, a2, s4
                  divu         s8, s10, a4
                  remu         s9, t5, t3
                  mulhsu       tp, s3, a3
                  ori          s1, t3, -1252
                  slli         t6, s7, 19
                  div          a7, t1, a5
                  auipc        s4, 697171
                  xor          s3, a1, t1
                  addi         sp, s9, -1384
                  c.li         a7, 25
                  addi         t3, gp, 413
                  sll          t5, zero, a5
                  c.add        s3, a6
                  mulhu        s0, s7, a1
                  c.li         a6, 0
                  c.srli       s0, 15
                  c.addi16sp   sp, 240
                  c.addi16sp   sp, -16
                  c.lui        a2, 27
                  remu         s3, a2, s10
                  sltu         t3, gp, t4
                  c.addi4spn   a0, sp, 64
                  rem          t4, s5, a3
                  c.srli       a2, 1
                  addi         tp, tp, -1749
                  andi         s0, t1, 1941
                  slt          s8, a4, s11
                  remu         s0, s11, s10
                  divu         t2, t4, s6
                  c.srai       a3, 5
                  c.lui        a2, 9
                  c.li         s10, 11
                  c.or         s1, a3
                  sub          s3, sp, t5
                  c.sub        s0, a4
                  sub          s1, sp, a6
                  sltu         s4, t3, a4
                  mul          a5, s10, s10
                  and          a5, s9, s4
                  c.or         a3, a1
                  rem          t0, ra, a4
                  c.sub        a5, a2
                  c.lui        t5, 26
                  slti         t2, t6, 2039
                  c.nop
                  c.nop
                  lui          a5, 232648
                  addi         sp, s6, -1577
                  slli         s8, s6, 1
                  c.sub        a0, a4
                  c.and        a3, s0
                  c.and        a3, a3
                  slli         a2, a7, 23
                  div          a0, a3, gp
                  c.srai       a2, 11
                  c.add        s8, a3
                  c.addi16sp   sp, 240
                  c.addi       s7, 6
                  mulhu        tp, zero, t3
                  sll          t3, s4, s5
                  c.srai       a3, 16
                  remu         s2, t4, sp
                  divu         t6, s4, s0
                  srli         s10, s1, 28
                  srai         t6, t5, 2
                  sra          a3, s5, s4
                  c.mv         s0, a7
                  remu         s9, t2, s2
                  c.mv         a5, a3
                  srai         a7, gp, 29
                  sub          tp, a6, s5
                  sra          s9, zero, t6
                  c.nop
                  c.nop
                  c.addi       s1, -1
                  auipc        a0, 962088
                  srai         t1, s1, 4
                  sub          s2, t2, t6
                  srl          t1, a6, t6
                  c.slli       t3, 6
                  mulh         t6, a1, a6
                  andi         s7, a4, 620
                  remu         s10, a0, s9
                  c.addi       a3, 25
                  div          s2, t4, s6
                  rem          s5, a4, zero
                  div          s3, s8, s9
                  and          ra, s5, ra
                  sub          s7, t6, t0
                  c.mv         ra, s1
                  sub          t5, a7, s0
                  remu         tp, s2, t6
                  c.addi4spn   s0, sp, 816
                  c.li         t3, -1
                  auipc        a7, 490699
                  lui          t4, 309728
                  srai         t3, t6, 1
                  c.xor        s0, a4
                  sltiu        s2, a6, 1775
                  addi         s5, s9, 1402
                  mul          t5, a4, s5
                  andi         a2, tp, -988
                  slli         s3, t4, 6
                  xor          a6, t2, t2
                  xori         gp, ra, 210
                  sra          a3, t1, a6
                  lui          a2, 562037
                  sltu         a6, t3, s1
                  slti         s5, s2, -673
                  slli         s5, gp, 21
                  auipc        a3, 67576
                  c.slli       s1, 13
                  c.li         s1, -1
                  c.slli       tp, 16
                  add          s7, s4, s8
                  c.srli       s0, 22
                  c.and        a3, s1
                  mulh         t2, ra, a5
                  mulh         s0, a7, s0
                  xor          s9, t3, s10
                  srl          s10, s7, sp
                  slti         t4, a7, 1148
                  sra          s0, s10, a2
                  c.and        a2, a3
                  c.addi       gp, -1
                  c.add        t1, a6
                  mulhu        s2, a6, a3
                  sltiu        a3, a7, 1909
                  c.sub        s1, a1
                  mulhsu       zero, s9, a3
                  and          t3, a1, a1
                  xor          a3, t5, s0
                  mulh         s5, a4, s10
                  c.nop
                  sll          t3, s0, zero
                  c.srli       a5, 3
                  slli         a5, s10, 8
                  sll          a6, s0, t1
                  c.li         t5, -1
                  c.nop
                  mulhu        t6, a1, t4
                  c.sub        s0, a2
                  divu         a7, a6, s7
                  c.and        s0, a4
                  divu         s4, gp, s6
                  srl          s3, zero, s3
                  auipc        t2, 835950
                  auipc        a2, 482859
                  slli         s8, t1, 29
                  auipc        s2, 120156
                  andi         s10, s7, 586
                  c.andi       s1, -1
                  c.addi       s3, 8
                  mulhu        t3, s9, gp
                  c.li         ra, 10
                  sub          t5, a7, sp
                  mulhsu       a0, a2, tp
                  srai         t4, tp, 0
                  sub          s4, t5, a4
                  c.addi16sp   sp, 480
                  nop
                  xori         s0, s6, 1754
                  divu         s0, s11, t6
                  srli         gp, a5, 31
                  nop
                  mulhsu       s2, s11, t4
                  c.mv         s2, a4
                  srli         t4, zero, 19
                  divu         s2, s6, s6
                  c.xor        a0, s0
                  srl          a3, t4, s8
                  xor          s8, a4, gp
                  sltu         t1, a4, gp
                  c.sub        a3, a0
                  nop
                  sub          s11, s10, a4
                  or           t1, a4, s4
                  mulh         s1, s10, a7
                  c.add        t4, t1
                  xor          s3, t4, s7
                  c.lui        a7, 29
                  sltiu        t5, t0, 1417
                  c.and        a2, a4
                  remu         t4, s6, t4
                  mul          tp, a0, s4
                  slli         s5, gp, 25
                  c.srli       a0, 23
                  c.or         s1, s1
                  c.sub        s1, a2
                  srli         s2, ra, 16
                  slt          a5, a6, sp
                  sra          s10, a4, s3
                  remu         a6, t4, t2
                  c.sub        s1, a5
                  slli         t3, s6, 30
                  ori          t2, a7, -1080
                  sltu         a7, t0, t6
                  c.mv         gp, s10
                  sll          s5, a2, s8
                  divu         s7, t1, sp
                  mulhsu       t0, zero, s4
                  mul          a7, t2, s0
                  c.addi16sp   sp, 464
                  c.nop
                  nop
                  addi         a5, s10, -972
                  sub          s7, a5, t2
                  c.srai       s0, 21
                  c.mv         tp, s3
                  slt          s3, s4, s6
                  c.and        s1, a5
                  or           s7, a0, s4
                  mulhsu       ra, t2, s5
                  c.and        a3, s1
                  c.srli       a3, 7
                  c.addi       a7, -1
                  sltiu        gp, a6, -820
                  c.addi       s4, -1
                  c.and        s0, a3
                  andi         t6, gp, 5
                  c.addi16sp   sp, -16
                  rem          s2, s2, a6
                  sltu         s10, a2, s5
                  sra          a0, s0, t3
                  nop
                  ori          t2, t6, -888
                  c.slli       t1, 3
                  mulhsu       t4, s8, t4
                  divu         sp, t4, s5
                  c.srai       a2, 10
                  c.xor        a3, a1
                  and          gp, s10, t0
                  or           t2, s6, t6
                  add          t4, t3, a6
                  slti         s10, t6, 1397
                  c.add        ra, s5
                  andi         a6, t1, 286
                  divu         s1, a5, t4
                  c.mv         s9, a0
                  xor          t2, t5, s4
                  c.srai       a2, 4
                  slli         a3, t0, 24
                  c.srli       a0, 2
                  c.nop
                  c.nop
                  c.addi4spn   a2, sp, 80
                  c.lui        s9, 7
                  slti         gp, t1, -654
                  remu         a3, a0, gp
                  div          s10, a6, a1
                  slt          s7, t5, a3
                  c.addi       gp, 4
                  remu         t3, t1, s10
                  srl          gp, s5, t3
                  c.addi4spn   a0, sp, 576
                  c.addi16sp   sp, 80
                  sub          s8, t1, t3
                  div          ra, tp, s9
                  c.xor        a3, a4
                  div          s4, s4, a6
                  c.addi       a2, -1
                  slt          a7, s7, sp
                  slli         s2, s0, 6
                  sll          s2, s3, tp
                  sra          t2, s4, a5
                  c.li         a3, -1
                  slt          t3, a1, a4
                  div          s0, s3, s1
                  slli         s10, gp, 8
                  rem          sp, s11, t0
                  c.addi       a6, 2
                  c.or         a0, a4
                  c.sub        a3, a2
                  srl          t1, s0, a0
                  xori         tp, s0, 1211
                  or           t3, s5, s0
                  srli         s11, s8, 6
                  mulhu        sp, a0, s6
                  andi         s9, s5, 162
                  xori         tp, s4, -317
                  andi         a2, t6, 1686
                  srli         a3, s6, 14
                  c.addi4spn   a2, sp, 272
                  sll          a0, s9, gp
                  andi         zero, s6, -1995
                  and          s8, a3, s2
                  c.addi4spn   s0, sp, 912
                  xor          s11, s10, a6
                  xori         t0, s4, 714
                  mulh         s8, tp, t2
                  c.srai       a3, 3
                  c.srli       a0, 13
                  mul          s5, sp, a3
                  c.or         a2, a0
                  and          t6, t4, t5
                  c.srai       a2, 5
                  c.xor        a0, s1
                  srli         s1, s1, 15
                  slti         a3, t0, -284
                  xori         t2, tp, -1224
                  c.xor        s1, s1
                  xori         zero, t0, 1016
                  c.li         s0, -1
                  sltiu        t1, s5, 1949
                  mulh         s2, a7, t4
                  sra          zero, s11, t2
                  sltu         t3, a3, a2
                  auipc        s9, 649862
                  c.li         t4, -1
                  div          a6, tp, a0
                  and          sp, t6, s2
                  sll          s9, ra, a2
                  sub          s5, s3, t4
                  slt          s5, a2, a4
                  srai         t3, sp, 17
                  nop
                  xori         a3, s7, 162
                  slt          s1, a0, t0
                  c.li         s10, -1
                  srl          s11, t4, s2
                  add          s4, a1, t0
                  rem          a0, s5, sp
                  c.srai       a0, 22
                  c.addi       s7, 22
                  sltiu        s1, t0, 5
                  remu         s9, a7, s9
                  divu         t5, s4, gp
                  mul          a0, t0, sp
                  div          t0, s9, s11
                  andi         s8, s3, 604
                  addi         s7, a1, 1575
                  andi         t0, s3, 842
                  or           s2, a0, s3
                  andi         gp, a7, -857
                  divu         s0, a4, t6
                  addi         zero, zero, 232
                  mulhu        s0, a1, zero
                  sltiu        a0, a5, -1380
                  nop
                  slt          s11, tp, s6
                  sll          a6, t6, t0
                  c.addi4spn   s1, sp, 400
                  mulhsu       a5, s11, t4
                  c.and        a2, s1
                  c.li         a7, 17
                  c.xor        a3, s1
                  c.mv         t5, a2
                  c.andi       a5, -1
                  c.xor        a3, a5
                  rem          t0, a0, t2
                  mulh         t1, a4, s5
                  c.addi16sp   sp, 336
                  add          s4, sp, t2
                  srli         t1, ra, 30
                  ori          a2, s0, 355
                  c.srli       s0, 6
                  srai         s9, s4, 8
                  andi         t1, a6, 1392
                  c.add        s5, a5
                  c.addi4spn   a0, sp, 80
                  mulhsu       s1, ra, t6
                  divu         s7, ra, t4
                  sltu         t1, a4, s1
                  srli         a7, zero, 3
                  srl          gp, sp, a7
                  sub          zero, s2, s0
                  sltiu        a7, gp, -1090
                  c.andi       a3, -1
                  sub          s9, s6, s4
                  srai         t6, sp, 24
                  or           t5, t4, s8
                  slt          s8, a5, a0
                  c.srli       s0, 10
                  sll          a7, t6, a1
                  addi         a7, tp, -333
                  mulhu        s10, t4, a6
                  and          t2, a3, a1
                  divu         t3, a3, ra
                  c.mv         a7, tp
                  srli         t6, s0, 2
                  slli         s4, t4, 0
                  c.or         a2, a5
                  andi         zero, t5, -1638
                  sub          s9, s8, t5
                  c.slli       a5, 23
                  c.xor        a0, s0
                  or           gp, s8, t5
                  c.and        s1, a5
                  c.nop
                  c.and        a2, a0
                  c.and        a3, a4
                  andi         s11, s11, 2037
                  srli         s5, ra, 6
                  andi         s9, sp, -768
                  ori          a5, s9, 1093
                  c.nop
                  sltu         s0, t6, s3
                  mulhu        a5, t0, a7
                  c.add        t2, s4
                  rem          t6, s5, a5
                  sub          s5, s1, s3
                  or           t4, t1, a1
                  and          sp, t3, t4
                  c.slli       sp, 28
                  slt          a5, s0, a3
                  c.srli       a5, 14
                  c.srai       a0, 16
                  sll          a7, s3, s5
                  or           ra, a7, s10
                  c.addi4spn   a5, sp, 320
                  c.sub        a0, s1
                  c.or         a0, s1
                  c.mv         s4, s11
                  addi         s5, ra, 1334
                  c.and        a2, a2
                  sll          ra, a2, gp
                  slli         tp, s5, 14
                  srai         s9, tp, 31
                  c.andi       a5, 22
                  srai         a2, t4, 31
                  srli         s5, t1, 19
                  slti         ra, s11, 450
                  rem          s3, a1, t1
                  sltu         s0, a2, s3
                  c.xor        a3, a3
                  mul          s8, s8, zero
                  sltu         a3, gp, a1
                  or           t3, s10, s9
                  sltiu        ra, t6, 1780
                  srai         t6, a1, 23
                  c.xor        a3, a3
                  andi         a7, t4, -1368
                  c.addi       gp, -1
                  or           a3, tp, t4
                  c.xor        a0, s0
                  mulh         s9, t0, t1
                  nop
                  c.addi16sp   sp, -16
                  slt          s7, s11, s1
                  and          a2, zero, t5
                  mulhsu       t2, a5, s1
                  c.srli       a2, 8
                  slli         s5, ra, 30
                  remu         s2, t5, t3
                  mulhsu       t5, t3, zero
                  ori          a7, s11, 527
                  ori          gp, gp, -876
                  rem          a3, s1, s5
                  mul          gp, t1, a5
                  c.and        a2, a0
                  slti         s2, s1, -1878
                  c.and        a0, a0
                  c.slli       gp, 11
                  c.srai       a0, 2
                  mul          t0, a1, s1
                  sll          s1, a2, a1
                  remu         t4, zero, s5
                  remu         s9, gp, gp
                  sltu         s2, zero, a7
                  lui          tp, 947535
                  slti         s3, s6, 231
                  c.sub        s0, a0
                  c.addi       t3, -1
                  auipc        ra, 402589
                  mul          a5, a2, s10
                  c.mv         gp, s11
                  mulhu        t4, t6, tp
                  slti         t1, s11, 1345
                  srl          a3, a5, s7
                  ori          a7, gp, -1468
                  xori         s1, s10, 1703
                  mulhsu       t4, a4, s2
                  sub          tp, a1, a3
                  andi         t0, t1, -316
                  c.addi16sp   sp, -16
                  mul          s5, a7, ra
                  rem          s9, s4, s4
                  xor          t1, t5, s11
                  srl          s7, zero, a3
                  sll          t3, a2, s7
                  auipc        gp, 375150
                  c.slli       t0, 5
                  divu         t5, s9, s11
                  c.add        s4, a5
                  and          tp, s9, s1
                  c.mv         a6, s10
                  sra          ra, s6, s3
                  c.nop
                  c.lui        s10, 10
                  lui          a3, 479150
                  c.srai       a3, 5
                  mulh         s11, s11, t1
                  c.mv         t3, a5
                  xori         t4, s5, -1602
                  srai         t3, s2, 22
                  add          ra, a7, sp
                  nop
                  c.srli       s0, 21
                  add          s4, sp, a7
                  xor          t1, t2, s9
                  c.addi16sp   sp, -16
                  mulhsu       a2, t3, s3
                  lui          s9, 426242
                  srl          t3, a3, s11
                  slt          a2, t4, t0
                  c.mv         s4, s9
                  c.addi16sp   sp, -16
                  mulhsu       a3, s1, zero
                  slti         a7, tp, 1010
                  slt          tp, a0, gp
                  xori         zero, a6, 1897
                  xor          s7, zero, a7
                  c.nop
                  mul          gp, t2, s6
                  or           s7, a7, s9
                  c.addi       tp, -1
                  or           zero, s7, a5
                  c.add        t0, a4
                  c.slli       a0, 7
                  or           t6, s1, a6
                  c.slli       a0, 3
                  or           s2, t5, a6
                  lui          s7, 642376
                  c.li         a0, -1
                  c.addi       a2, -1
                  or           s1, a0, a6
                  ori          s2, t3, -65
                  c.xor        a0, a2
                  c.addi       s4, 14
                  slti         t3, s5, -1795
                  c.sub        s1, a5
                  mulhsu       zero, t0, s8
                  sub          s5, t0, a7
                  sltiu        a6, a0, 1583
                  c.srli       a0, 17
                  mulhsu       t6, tp, t4
                  or           s11, s3, gp
                  c.srai       s0, 14
                  add          t1, s2, s6
                  add          s4, t3, s8
                  sltiu        zero, zero, 1459
                  addi         a5, a7, -1738
                  c.xor        a5, a0
                  srai         s9, a2, 30
                  sltu         s4, s0, a3
                  mulh         s8, s3, t1
                  c.addi       a0, 1
                  and          s11, a7, s7
                  sll          t4, gp, ra
                  sub          s11, s9, s8
                  remu         t1, s9, s7
                  mul          s11, gp, t3
                  c.or         a0, a2
                  and          s0, t2, ra
                  c.or         a2, a2
                  mul          zero, t4, a3
                  mulh         a6, a3, s5
                  xori         s4, tp, 629
                  srl          s8, s11, t3
                  andi         s10, t0, 1841
                  c.xor        a5, a3
                  auipc        a5, 408353
                  mul          t2, s8, a2
                  xori         s10, t5, 665
                  divu         s11, s5, t5
                  c.srai       a2, 24
                  mul          s10, s4, t5
                  c.slli       s5, 16
                  srai         t6, s8, 8
                  c.nop
                  rem          s7, ra, t2
                  sltu         a6, t3, a3
                  c.srli       a5, 5
                  andi         ra, s5, 946
                  mulh         a7, ra, s9
                  or           t3, s3, s7
                  rem          s8, a5, gp
                  srai         t6, s6, 12
                  sltu         a6, zero, sp
                  c.srli       s1, 5
                  nop
                  c.srai       a5, 9
                  mulh         t6, ra, s5
                  c.andi       a2, -1
                  add          s9, s8, s1
                  c.addi4spn   a3, sp, 656
                  slli         t1, a0, 12
                  c.xor        a0, a5
                  ori          a3, sp, -767
                  div          gp, t6, t6
                  c.addi16sp   sp, 256
                  sll          s9, a7, s2
                  or           a5, gp, s8
                  divu         s9, ra, a0
                  mulh         tp, a0, t1
                  sll          s2, tp, tp
                  mul          s9, s2, a3
                  c.xor        s0, a3
                  xor          s4, t6, t2
                  xori         t4, s5, 1028
                  slli         s11, sp, 11
                  lui          t4, 930383
                  srl          a6, gp, s4
                  mul          zero, t3, t6
                  add          t1, s10, t0
                  mul          s10, a0, s4
                  c.mv         s4, t3
                  mulh         t2, a5, tp
                  andi         a2, a4, -1130
                  c.or         s1, a4
                  nop
                  c.sub        s0, a0
                  auipc        t1, 791930
                  slli         t3, a1, 19
                  andi         a3, t5, 829
                  li           a0, 0x0 #start riscv_int_numeric_corner_stream_8
                  li           s4, 0xffffffff
                  li           s5, 0x0
                  li           tp, 0xffffffff
                  li           t5, 0x0
                  li           s7, 0x80000000
                  li           t4, 0x0
                  li           s0, 0xffffffff
                  li           t0, 0xe2115d7d
                  li           s1, 0x80000000
                  sub          t5, t4, s7
                  divu         a0, t5, s1
                  mulh         tp, a0, t0
                  divu         s7, a0, s4
                  auipc        s0, 99336
                  add          s5, s5, s5
                  nop
                  mulhu        tp, t5, a0
                  mul          s0, s1, a0
                  mulh         a0, s7, t0
                  mulhsu       t4, s5, s4
                  auipc        tp, 588271
                  sub          tp, s5, a0
                  auipc        t0, 531584
                  mulhsu       s0, s4, s4
                  remu         s5, t4, t4
                  mul          s4, s4, a0
                  sub          t5, s5, a0
                  mulh         s0, t0, s5 #end riscv_int_numeric_corner_stream_8
                  slli         a0, s7, 1
                  or           s3, s5, a4
                  and          s10, t4, s1
                  xor          sp, s4, t1
                  add          s3, s10, s5
                  slli         t3, a2, 13
                  c.xor        a5, a4
                  add          t3, a2, t3
                  nop
                  c.addi       t3, -1
                  div          sp, a6, t4
                  c.srai       s0, 14
                  c.sub        s0, s1
                  c.nop
                  srli         t2, tp, 27
                  c.srli       a2, 25
                  c.addi       s7, 12
                  srai         a0, gp, 9
                  andi         zero, t1, 1798
                  c.add        a3, tp
                  srli         t6, s8, 25
                  mulh         s7, a6, s7
                  mulh         a7, s6, t5
                  c.srai       s1, 25
                  mulhsu       a6, a3, a5
                  slt          tp, s10, s7
                  and          a3, s1, s10
                  auipc        a5, 1008847
                  srai         a3, s1, 5
                  c.addi       sp, -1
                  mulh         t5, s7, s2
                  c.addi16sp   sp, -16
                  sra          sp, t1, s2
                  sll          zero, s9, t4
                  c.andi       a2, -1
                  ori          s10, s8, 1505
                  mulh         s10, a5, s10
                  sltu         t4, tp, s10
                  c.xor        a2, a3
                  sra          t6, s7, a5
                  slti         t0, s2, 960
                  nop
                  or           a2, a1, t2
                  ori          s4, s7, 331
                  c.andi       a5, -1
                  c.addi4spn   a2, sp, 736
                  xori         a6, t1, -1973
                  srai         s0, t0, 30
                  c.and        a5, a1
                  slt          s4, t1, tp
                  sltiu        s7, tp, 986
                  remu         s9, t1, zero
                  c.or         a0, a3
                  c.li         a5, -1
                  xor          s1, t5, a1
                  c.or         a0, a0
                  c.nop
                  div          s0, t4, s6
                  srli         s8, a4, 16
                  c.mv         a5, a3
                  c.lui        s0, 23
                  c.or         s1, a5
                  c.xor        s0, a5
                  add          s11, a4, gp
                  c.andi       a2, 6
                  add          gp, t6, t4
                  remu         s8, a7, s2
                  remu         a3, s7, s9
                  xor          s8, s3, a5
                  c.srai       a0, 16
                  srl          t1, s8, s11
                  c.li         a7, 25
                  sub          a3, t2, s10
                  andi         s4, s9, -1174
                  c.and        a5, s1
                  c.slli       s10, 12
                  srli         a0, ra, 3
                  slt          s7, a6, a4
                  andi         s9, s4, -801
                  c.slli       a3, 25
                  andi         s1, s4, 845
                  mulhu        t1, s10, a6
                  c.and        a3, a1
                  div          s10, t6, s5
                  or           s11, s9, s4
                  nop
                  c.li         t6, -1
                  c.or         a3, a4
                  c.srli       a2, 2
                  andi         s0, s3, -209
                  slt          gp, a2, t2
                  c.srai       a2, 30
                  c.mv         s0, t6
                  sltiu        gp, a3, -2008
                  nop
                  c.srai       s1, 22
                  c.add        s2, a2
                  andi         a0, s4, -808
                  and          a5, a2, s11
                  mulhu        s11, t4, ra
                  c.sub        a5, a3
                  c.li         s7, 20
                  srli         t0, s7, 12
                  c.xor        s0, a5
                  sub          t6, t2, s10
                  c.and        s0, a3
                  sltu         tp, gp, a0
                  nop
                  c.li         s4, 6
                  sltu         t4, t4, s11
                  c.addi16sp   sp, -16
                  ori          a2, t1, -143
                  ori          t3, a4, 415
                  slti         s4, t2, -1030
                  sra          s8, a3, s6
                  rem          t0, s10, s2
                  remu         a0, s11, s10
                  c.mv         t5, a0
                  c.and        a2, a1
                  xori         t0, tp, -612
                  auipc        s1, 915920
                  div          s1, s6, s1
                  c.addi4spn   a0, sp, 368
                  c.add        s3, t4
                  c.srli       a0, 19
                  sltiu        t1, ra, 396
                  c.sub        s1, s1
                  xori         s1, s10, 359
                  sll          t0, s6, s2
                  c.slli       a2, 20
                  add          s2, t1, a0
                  andi         a7, a5, 1233
                  sra          s7, s10, s6
                  c.addi       a0, -1
                  sra          s10, ra, t5
                  c.lui        a3, 31
                  c.or         a3, a4
                  auipc        s8, 691510
                  c.addi       s10, 26
                  slti         t4, ra, 208
                  c.addi       s9, 24
                  addi         a6, s11, -880
                  divu         s7, a3, s6
                  add          ra, t5, a2
                  c.li         t1, 9
                  ori          t5, a5, -1673
                  xor          t1, sp, t4
                  or           a6, a1, s8
                  slt          s4, a4, s5
                  addi         zero, ra, -868
                  c.addi       s11, 5
                  c.nop
                  srl          t0, t6, a5
                  slti         t6, t6, 701
                  c.addi       s0, 15
                  sltu         a3, t0, s11
                  c.add        a2, ra
                  divu         a2, s9, s10
                  sltu         s0, a1, a4
                  srl          s8, s7, a6
                  add          t3, ra, tp
                  remu         s11, t6, s4
                  mulhu        a0, a0, s8
                  andi         a2, a5, -879
                  c.mv         s0, a4
                  slli         s0, a3, 21
                  nop
                  srai         s2, s0, 6
                  auipc        a2, 1018626
                  mulhu        sp, t1, a1
                  div          t2, t2, a3
                  add          t4, a6, s9
                  xori         t6, t2, -1364
                  addi         s11, s9, 76
                  c.li         s0, -1
                  remu         s0, s6, a6
                  xor          t6, ra, s3
                  c.addi       t4, 18
                  sltu         a7, a2, a0
                  c.add        a0, a0
                  ori          s11, sp, -1352
                  xori         a5, t3, 1721
                  divu         s5, t3, s0
                  lui          a7, 289051
                  sltiu        t0, ra, 510
                  rem          s4, s0, a4
                  auipc        a6, 133937
                  c.addi16sp   sp, -16
                  c.sub        a0, a5
                  c.and        s1, a3
                  c.add        a7, a7
                  mulh         t5, t0, tp
                  mulh         t5, a4, sp
                  div          t0, s7, s8
                  xor          s10, s10, s0
                  mulh         zero, s1, s7
                  mulh         a7, t1, t0
                  addi         ra, a2, 780
                  c.li         t0, 7
                  c.slli       tp, 30
                  sltiu        t1, zero, 1016
                  mulh         s3, s11, a0
                  sltu         s10, s1, a2
                  nop
                  sub          s4, s3, s3
                  c.addi4spn   a2, sp, 208
                  mulh         t1, s0, tp
                  c.mv         s10, a7
                  add          gp, a2, s5
                  div          s1, s2, s10
                  rem          s8, t4, s8
                  divu         a7, s5, s11
                  remu         s7, a5, t1
                  slli         s1, a2, 0
                  slli         a7, s8, 2
                  div          t3, t0, t6
                  slti         t1, a1, 1291
                  sra          a5, a0, s4
                  c.mv         a6, s5
                  addi         t2, s10, -1650
                  mulhu        a6, a5, t1
                  srai         t4, s9, 26
                  sltiu        zero, s8, -1830
                  sll          tp, t6, a5
                  c.li         t0, -1
                  c.add        t5, a7
                  ori          s0, t6, 39
                  srl          t4, s5, a6
                  rem          gp, a5, a2
                  divu         a6, t5, s9
                  and          s11, t4, s5
                  lui          tp, 110717
                  lui          s5, 261130
                  c.addi4spn   a0, sp, 160
                  xori         s3, t5, 450
                  xori         s10, s0, 253
                  nop
                  sltu         t5, a4, a4
                  andi         a3, s10, 1699
                  addi         t3, a7, 981
                  c.andi       s0, 14
                  add          a5, s0, t2
                  c.or         a2, s0
                  mulh         sp, s8, s4
                  sub          s0, s9, s4
                  sltiu        t0, t1, 469
                  srli         s1, tp, 12
                  c.slli       s0, 1
                  c.nop
                  c.lui        a0, 18
                  sltu         s7, s7, a3
                  lui          t6, 565172
                  auipc        a0, 471643
                  c.srai       s1, 28
                  c.addi       t3, -1
                  and          t1, s2, t5
                  sll          gp, a1, t1
                  xor          t6, t2, s2
                  c.and        a3, s1
                  c.addi4spn   a0, sp, 800
                  c.xor        a3, s1
                  sll          t3, s8, s5
                  slti         sp, s7, 153
                  xori         s4, a4, 333
                  c.srli       s0, 11
                  srl          t6, tp, t6
                  c.addi16sp   sp, 480
                  c.addi16sp   sp, -16
                  remu         s1, s2, s8
                  c.addi       a5, 15
                  mulhsu       ra, s4, a3
                  nop
                  nop
                  c.slli       t6, 18
                  sra          s5, a3, s9
                  srai         s7, a7, 18
                  srai         t6, s3, 8
                  sub          sp, s8, s11
                  remu         s5, a3, t2
                  c.and        a2, a5
                  slt          a6, s8, tp
                  sra          t0, s7, s10
                  nop
                  add          a0, a2, s4
                  c.andi       s1, 29
                  sltu         s10, s8, t4
                  c.slli       t6, 2
                  sltiu        a7, t0, -80
                  c.nop
                  mulhsu       zero, a6, sp
                  c.xor        a5, a3
                  c.addi16sp   sp, 240
                  slli         s9, s8, 18
                  c.nop
                  srai         zero, a0, 4
                  nop
                  c.and        a2, a3
                  c.or         s1, a4
                  div          s11, s2, s0
                  c.sub        s0, a0
                  addi         t0, a3, -1521
                  auipc        t2, 964040
                  sra          s9, zero, t0
                  c.and        a3, s0
                  and          s11, gp, zero
                  rem          tp, s6, t2
                  lui          tp, 712486
                  sll          s3, s7, s7
                  ori          a2, s10, -886
                  c.srai       s0, 19
                  c.lui        s2, 30
                  c.lui        s7, 10
                  divu         tp, t5, tp
                  lui          ra, 106799
                  auipc        s3, 194388
                  srai         sp, sp, 3
                  c.li         t2, 29
                  c.slli       a5, 20
                  lui          t2, 387836
                  c.addi       t2, -1
                  sltiu        a6, s2, -1706
                  sll          a5, t4, t4
                  mulhsu       s2, s2, ra
                  c.addi4spn   a3, sp, 352
                  or           tp, a3, a1
                  c.mv         s5, a0
                  sltiu        a7, a0, 1906
                  c.slli       t2, 26
                  addi         s8, s1, 1494
                  addi         sp, t5, 336
                  xori         t3, s5, 783
                  srai         s10, t6, 30
                  c.addi       tp, 24
                  sll          t1, s9, t3
                  c.xor        a3, a1
                  srli         t4, t4, 16
                  xor          tp, t5, a5
                  sltiu        a2, s6, 1486
                  c.addi16sp   sp, 448
                  ori          a2, s5, 1644
                  add          s9, t2, s10
                  remu         s0, s3, sp
                  remu         s2, s4, s10
                  c.srai       s0, 13
                  sra          s3, s4, t1
                  c.nop
                  divu         a5, a0, a5
                  c.srai       s1, 25
                  rem          s0, t0, s2
                  c.xor        a3, a1
                  auipc        t1, 191560
                  div          s7, gp, t0
                  xor          t3, s0, a1
                  andi         s0, s11, 234
                  c.mv         s1, a6
                  c.srli       s0, 7
                  srli         a2, t4, 18
                  add          s7, s1, t1
                  c.addi4spn   a2, sp, 16
                  or           t0, t5, sp
                  c.add        tp, s10
                  srl          a0, s0, s0
                  divu         s1, t6, ra
                  sltiu        a0, zero, 70
                  slt          s1, t4, t3
                  slli         t3, s11, 28
                  and          s1, a3, a1
                  c.and        a3, a2
                  mul          s1, s11, s5
                  c.addi       a3, -1
                  slt          s4, gp, zero
                  srli         a2, t5, 1
                  sltiu        s8, t5, -887
                  sra          a3, s0, a0
                  c.nop
                  c.or         a3, s1
                  rem          s8, s8, t5
                  c.addi16sp   sp, 64
                  c.li         s2, 26
                  or           a0, s7, tp
                  c.sub        a2, a2
                  mul          s1, s11, zero
                  lui          s2, 95105
                  nop
                  ori          s8, a3, -416
                  c.li         t5, -1
                  c.nop
                  and          t6, s7, s6
                  lui          a3, 945977
                  c.or         s0, a1
                  sltu         s5, a1, s7
                  sra          t3, a5, t2
                  auipc        a0, 357724
                  sub          a2, s9, tp
                  c.add        s0, t2
                  div          t5, t4, t0
                  c.mv         s1, a6
                  add          zero, s7, t6
                  c.mv         a5, a1
                  c.srli       s1, 16
                  c.addi16sp   sp, -16
                  c.srai       a0, 17
                  lui          s9, 481340
                  c.andi       s1, 29
                  rem          a6, zero, s9
                  c.andi       s1, -1
                  sltu         a2, zero, a2
                  sll          sp, zero, t1
                  divu         tp, s10, t0
                  c.xor        a2, a0
                  sub          a5, sp, a3
                  c.addi       s7, -1
                  sltu         s4, tp, s2
                  slt          s0, gp, ra
                  c.lui        s1, 28
                  c.li         a7, -1
                  c.nop
                  c.nop
                  add          s9, t0, s4
                  c.nop
                  c.addi4spn   a5, sp, 144
                  srl          a0, a1, a7
                  sra          s2, s3, t0
                  c.srai       a0, 29
                  ori          t3, tp, 1221
                  addi         t1, a7, -1919
                  slt          a7, s6, a7
                  lui          t0, 409300
                  c.add        s3, t0
                  c.or         a3, s1
                  slti         t3, a5, 1642
                  ori          s11, tp, 1677
                  ori          zero, s11, 103
                  sra          t4, a1, t1
                  xori         s0, t5, -402
                  xori         sp, a0, -1745
                  divu         s8, t0, s5
                  slli         s1, s2, 18
                  slti         sp, a1, -1022
                  srli         gp, s11, 11
                  and          t2, a2, t5
                  andi         t1, t3, -197
                  slli         a2, t3, 29
                  c.slli       a5, 19
                  mul          a2, s1, s1
                  c.slli       a0, 12
                  c.lui        a0, 19
                  sra          sp, t5, t5
                  c.addi16sp   sp, 304
                  c.srli       s0, 28
                  c.mv         s1, s2
                  c.li         t4, -1
                  srl          a3, a2, s0
                  add          sp, a7, s5
                  xori         s11, s5, -435
                  c.and        a5, a3
                  c.nop
                  c.or         a3, s0
                  c.and        s0, s0
                  srai         a2, a7, 22
                  rem          a3, s0, s1
                  div          s8, t3, t3
                  c.add        gp, t6
                  c.addi16sp   sp, 112
                  c.xor        a5, a2
                  and          t0, a2, sp
                  c.or         s1, s1
                  and          gp, a1, t4
                  c.slli       a7, 24
                  c.srai       a2, 7
                  slt          t4, s7, ra
                  c.addi16sp   sp, 224
                  c.lui        a7, 30
                  sub          t2, s6, zero
                  xori         t3, a1, 400
                  c.addi       s7, 21
                  lui          zero, 173228
                  sll          s4, t1, s4
                  div          s9, gp, s2
                  sltu         s5, t6, s8
                  c.sub        a3, a1
                  and          s2, ra, t5
                  c.or         s1, a2
                  c.andi       a0, -1
                  div          t4, s10, s3
                  ori          t3, a4, 553
                  c.nop
                  slli         s0, t0, 2
                  c.sub        s0, s0
                  c.srli       a2, 14
                  srli         t2, s3, 23
                  srl          t0, t1, a3
                  c.srli       a3, 23
                  xor          a3, s2, gp
                  sub          t1, s4, a4
                  slt          t3, t0, t6
                  mulh         a0, a5, s3
                  sltu         t4, s1, s10
                  c.nop
                  mulhsu       a2, a6, s2
                  c.and        a3, a4
                  srli         t0, t6, 1
                  slti         gp, a3, 168
                  mulhsu       t2, a2, s6
                  sub          tp, a7, s3
                  slli         s1, a1, 0
                  c.mv         s5, s8
                  c.xor        a0, a1
                  and          t3, a7, a7
                  c.xor        s0, s0
                  mulhu        t1, s5, s3
                  slti         gp, a1, 1708
                  div          t5, t6, s9
                  c.sub        a3, a3
                  slti         t1, zero, 1182
                  mulh         s9, s2, a2
                  slli         a3, a1, 29
                  c.addi16sp   sp, 432
                  div          s0, t0, tp
                  andi         s0, a3, 152
                  add          s11, a4, t3
                  div          zero, t1, a2
                  and          ra, s11, s5
                  c.andi       a3, 10
                  xor          s8, s2, gp
                  slti         s9, a4, -1250
                  c.addi4spn   a2, sp, 784
                  c.or         s1, a2
                  c.xor        a3, a4
                  addi         s11, a7, 713
                  and          s9, s7, a0
                  c.nop
                  andi         t4, tp, -1835
                  remu         s7, a1, a4
                  div          t6, a1, s6
                  xori         s5, tp, 1903
                  sll          s10, s3, s0
                  mulh         s9, s8, gp
                  sltu         t2, a7, s7
                  c.addi4spn   a5, sp, 864
                  rem          s11, t6, t1
                  c.slli       tp, 20
                  c.sub        s0, a0
                  c.addi       s0, -1
                  slti         a2, s7, -1443
                  srl          tp, s5, t5
                  sra          t3, a2, s7
                  lui          s9, 499174
                  c.add        s5, s7
                  c.sub        s0, a4
                  lui          t5, 194388
                  srli         s11, a0, 13
                  c.addi4spn   a0, sp, 656
                  sll          t0, ra, s11
                  c.addi4spn   s0, sp, 400
                  srl          t1, s9, t6
                  srl          t1, a4, gp
                  lui          t2, 1005772
                  c.and        a0, a4
                  remu         s11, s7, s8
                  c.xor        s0, a0
                  mulh         s9, a6, a3
                  c.add        tp, a6
                  mulhsu       s9, gp, s5
                  auipc        a2, 368836
                  xori         s3, t2, -630
                  divu         s0, t5, a5
                  c.nop
                  c.xor        a0, a1
                  sll          t0, s7, a3
                  and          a5, ra, s7
                  c.and        a3, s1
                  c.sub        a2, a3
                  mulhsu       s3, a3, ra
                  divu         t4, t0, s10
                  c.andi       a3, 8
                  c.addi       sp, 16
                  sll          t0, tp, t4
                  slti         t3, s10, 1684
                  c.srai       a0, 18
                  xor          s11, t3, gp
                  sub          zero, t0, a6
                  c.andi       a5, -1
                  c.srli       s0, 31
                  addi         t5, a4, -1332
                  remu         t1, t0, s0
                  rem          t6, s0, s0
                  remu         s4, a1, a6
                  srl          a2, t1, s9
                  c.sub        a2, a3
                  c.slli       t5, 26
                  c.addi       sp, 21
                  sub          a6, a2, t6
                  mul          t1, sp, s11
                  div          s10, t2, a6
                  c.nop
                  sltu         t5, s2, s4
                  mulhsu       s3, t0, s10
                  srai         t3, s5, 17
                  add          s0, a0, t6
                  remu         a6, s4, t5
                  mul          t0, t4, sp
                  c.slli       a6, 6
                  mulhu        t6, a5, a2
                  c.or         a2, a4
                  remu         s1, a3, gp
                  mul          s4, s2, a1
                  lui          gp, 372409
                  c.nop
                  c.xor        a0, a3
                  divu         t3, ra, t3
                  mul          s11, ra, s2
                  xor          ra, a4, s10
                  ori          t1, a4, 1816
                  li           t2, 0xffffffff #start riscv_int_numeric_corner_stream_36
                  li           a7, 0xf50d57a5
                  li           a3, 0xd9e9c699
                  li           t1, 0x80000000
                  li           s8, 0x0
                  li           t0, 0x0
                  li           t6, 0x80000000
                  li           t5, 0xffffffff
                  li           a6, 0x7e0bfd85
                  li           s7, 0xffffffff
                  rem          s7, t0, t0
                  remu         a7, s7, t0
                  remu         t1, t2, a3
                  addi         s7, a3, -1922
                  mulhu        t0, t1, s8
                  mul          s7, s7, t5
                  sub          t2, t5, a7
                  auipc        t6, 374590
                  divu         t0, t0, a6
                  mul          a7, t1, s8
                  remu         t0, a6, t0
                  mulhsu       a3, a3, t1
                  divu         t0, a3, t2
                  addi         a6, s7, 1577
                  auipc        t6, 1010267
                  addi         s7, s8, 846
                  divu         t5, t2, t5
                  nop
                  add          a3, t6, t2
                  rem          t2, t6, a3
                  mul          t1, s7, t6 #end riscv_int_numeric_corner_stream_36
                  mulhsu       s7, t4, sp
                  andi         s11, a3, 1187
                  rem          sp, a5, a2
                  add          s5, a7, zero
                  lui          s4, 202792
                  c.andi       a0, 3
                  lui          s0, 485222
                  ori          t2, t1, -673
                  and          s8, s9, s10
                  srai         s0, s2, 1
                  c.andi       a3, -1
                  or           s4, s1, s5
                  ori          gp, s8, -1454
                  sltu         a7, t5, a1
                  ori          ra, t4, 889
                  andi         a6, a2, 1467
                  remu         ra, sp, a6
                  c.addi16sp   sp, -16
                  nop
                  slli         zero, t6, 20
                  c.addi16sp   sp, 80
                  rem          ra, zero, a3
                  div          s4, t4, a3
                  sra          s10, s10, ra
                  c.sub        s0, a0
                  c.slli       a2, 18
                  andi         s11, t6, 1729
                  c.andi       a0, 28
                  xor          a5, t1, s6
                  xor          s1, s11, s7
                  c.li         tp, 12
                  or           a0, ra, s10
                  or           s3, t4, tp
                  c.mv         s11, s5
                  sub          a5, a4, s5
                  mul          zero, gp, tp
                  divu         t1, t3, sp
                  xor          t6, s0, t6
                  sub          a7, a3, t1
                  c.addi16sp   sp, 112
                  slli         t5, s8, 6
                  xori         s11, gp, 242
                  andi         s9, s0, -1062
                  nop
                  slli         t2, a1, 14
                  c.xor        s1, a5
                  add          a6, s5, a7
                  xor          a7, s2, a2
                  c.slli       t3, 19
                  mul          t2, t4, a4
                  nop
                  or           s9, a3, a0
                  sll          s9, s11, a0
                  sltiu        t3, t3, 871
                  divu         a5, s9, s9
                  c.srai       a3, 13
                  rem          t0, a0, s10
                  xori         a0, s8, 354
                  or           a0, s7, s3
                  c.li         t0, 0
                  c.srli       s1, 25
                  mulh         a2, a4, t5
                  div          s3, t2, s3
                  lui          sp, 696387
                  div          s10, s10, a6
                  srl          s5, s10, a2
                  sra          s11, tp, a7
                  mulhu        t3, ra, t5
                  slt          s7, a6, gp
                  c.lui        s5, 22
                  divu         t0, ra, s4
                  mulhsu       a6, a3, t1
                  lui          a5, 349778
                  mulh         s10, s6, s6
                  auipc        s11, 109050
                  nop
                  and          sp, t3, a2
                  or           zero, s1, a2
                  add          a0, s5, s9
                  srli         ra, s3, 13
                  addi         s2, s3, 1983
                  c.slli       s9, 31
                  mulh         s11, t6, s4
                  sltu         s3, gp, s2
                  sltiu        a6, a5, 532
                  div          s0, a4, t0
                  remu         t3, a1, s5
                  sub          s4, s8, s1
                  addi         a2, s1, 679
                  slt          s9, t0, s1
                  auipc        s2, 1029099
                  srl          s0, gp, t0
                  nop
                  mulhsu       a2, s0, t6
                  andi         t6, tp, -311
                  c.addi4spn   s1, sp, 288
                  sra          a5, a2, t0
                  srai         gp, s1, 13
                  srai         t3, t4, 10
                  rem          s1, s1, s9
                  c.nop
                  and          a7, t5, a3
                  c.addi4spn   a2, sp, 720
                  c.or         s1, a1
                  c.addi4spn   a0, sp, 592
                  srli         a2, a1, 11
                  xori         a2, s2, -1606
                  add          t4, a0, a0
                  c.and        a5, a1
                  srai         tp, a4, 13
                  mul          s9, s0, a4
                  mulh         zero, s9, s6
                  or           a5, gp, t0
                  div          s9, tp, s5
                  c.srli       a3, 12
                  xori         gp, a1, -425
                  auipc        s0, 593930
                  and          gp, s10, sp
                  c.addi4spn   s0, sp, 656
                  c.addi4spn   s0, sp, 864
                  lui          t6, 589947
                  c.and        a5, a0
                  c.or         s1, a0
                  c.sub        a0, s0
                  srli         s7, s8, 5
                  srl          zero, s0, a4
                  c.nop
                  c.slli       a3, 14
                  mulhu        sp, a1, a0
                  c.mv         a3, s6
                  c.mv         s9, a4
                  c.lui        a3, 7
                  xor          a6, s2, a4
                  c.srli       a3, 14
                  slt          gp, s1, t6
                  c.addi       s11, 20
                  c.addi4spn   s1, sp, 352
                  auipc        s8, 561081
                  c.srli       s0, 3
                  xor          t1, s4, s0
                  c.slli       a2, 13
                  slti         t1, s2, 2020
                  xori         tp, sp, 977
                  c.srli       a2, 28
                  divu         s7, a7, tp
                  lui          t5, 488382
                  mulh         s2, a5, a6
                  or           t1, s6, a2
                  and          s0, sp, gp
                  c.lui        s7, 23
                  or           t0, a5, s3
                  and          s5, t5, s11
                  srai         s7, t3, 1
                  c.li         s2, 5
                  c.srai       a3, 26
                  c.lui        a3, 6
                  srl          s3, a2, a0
                  sltu         t2, s1, a4
                  c.slli       t0, 21
                  c.sub        a5, a5
                  c.addi       t3, -1
                  andi         t2, s10, 1408
                  mulh         s0, a5, t5
                  c.slli       t1, 22
                  slti         a2, a7, -1393
                  c.slli       t1, 26
                  xori         ra, t4, -1070
                  mulhu        zero, gp, a2
                  add          ra, zero, t0
                  slt          s7, s9, s8
                  slli         t1, sp, 18
                  srli         a7, s5, 17
                  srl          tp, s0, a1
                  ori          a0, a2, 1715
                  and          t3, s7, a3
                  sra          t3, s6, s9
                  c.xor        s0, a0
                  div          t5, a5, s8
                  c.srli       a5, 2
                  c.sub        s1, a5
                  mulh         t3, s3, gp
                  c.slli       s11, 21
                  sra          s4, tp, s10
                  c.nop
                  add          a3, s7, a1
                  srli         s10, a5, 9
                  sltiu        t3, gp, 1747
                  ori          s11, s6, -299
                  c.addi4spn   a2, sp, 320
                  c.srli       s0, 24
                  slt          a7, a2, a0
                  c.xor        a3, s0
                  c.addi4spn   a3, sp, 736
                  mul          t5, s11, t3
                  slt          ra, a0, s0
                  sll          t3, s4, t6
                  lui          s5, 941743
                  sub          s1, s3, a2
                  c.and        a5, a2
                  slt          a2, s9, s1
                  c.or         s0, a5
                  mul          a6, s8, s11
                  c.addi16sp   sp, 64
                  mulhsu       s8, s2, ra
                  srl          a3, a5, a3
                  mul          a6, t0, s1
                  c.or         a3, s0
                  c.addi16sp   sp, 464
                  c.andi       a0, 7
                  mulh         gp, t0, a0
                  auipc        a7, 982758
                  mulhsu       s5, a4, s5
                  sll          s5, a6, t6
                  slt          t6, s11, s0
                  c.lui        t2, 27
                  c.lui        a0, 10
                  srai         ra, ra, 23
                  c.andi       a2, -1
                  c.addi4spn   s1, sp, 720
                  mulhsu       a5, t2, s2
                  slli         ra, a6, 22
                  sll          sp, s1, a2
                  slti         sp, a3, -865
                  div          tp, t4, a7
                  slt          a2, s1, s4
                  c.mv         s1, gp
                  c.add        t3, s4
                  sll          a6, zero, tp
                  slt          s5, s0, s0
                  c.srli       s0, 5
                  lui          zero, 741008
                  sltiu        s8, a0, 94
                  slti         t5, t3, -1156
                  c.and        s0, a3
                  slli         s0, s4, 16
                  xor          t2, s2, zero
                  c.srai       a0, 26
                  c.li         a0, -1
                  divu         sp, t4, s10
                  div          a5, s3, a4
                  slli         s3, t5, 20
                  srl          s0, t5, a1
                  c.addi4spn   a3, sp, 64
                  slti         s8, t2, -875
                  lui          s11, 396312
                  mulh         s3, t4, t4
                  sltu         s8, ra, s9
                  divu         t1, s7, sp
                  c.mv         a7, t3
                  lui          t3, 352858
                  srl          a5, s1, t1
                  srl          a5, s10, ra
                  c.xor        s1, a1
                  xor          s9, s5, a7
                  mulhu        a3, a4, a3
                  auipc        a7, 345163
                  c.lui        t6, 25
                  c.lui        t6, 1
                  and          a2, s1, t5
                  c.slli       t0, 14
                  c.slli       sp, 1
                  and          t2, s6, gp
                  c.and        s0, a0
                  srli         s10, s5, 22
                  c.mv         t2, s3
                  c.and        a3, a4
                  sltu         t6, s9, a2
                  c.li         a5, 23
                  andi         s5, s6, 1280
                  remu         a0, s11, a7
                  srli         s1, a6, 15
                  c.addi4spn   s0, sp, 448
                  c.mv         s7, t0
                  rem          sp, a0, t3
                  sltu         s5, a6, s11
                  divu         t2, t0, t3
                  c.sub        a2, a3
                  remu         t0, s2, s6
                  or           s11, s1, s3
                  c.mv         t0, s11
                  xor          s8, zero, s4
                  c.and        a3, a2
                  sltu         s3, s6, t3
                  srl          s8, a3, gp
                  c.addi16sp   sp, -16
                  mulhu        ra, zero, s7
                  lui          t4, 978805
                  add          t2, a4, s6
                  sub          t6, a0, a2
                  andi         s3, t1, -271
                  or           s4, a2, t2
                  c.li         s4, 9
                  or           s11, s8, a1
                  srl          s1, zero, gp
                  slti         t3, zero, 1549
                  remu         s7, s11, sp
                  mul          t6, t1, zero
                  addi         a7, a6, -1910
                  c.addi16sp   sp, 144
                  c.addi4spn   a3, sp, 912
                  c.and        a2, a4
                  mulhu        t5, zero, s1
                  srli         s0, ra, 28
                  xor          a6, t6, s5
                  c.add        a7, t0
                  mulhsu       s5, s7, t1
                  and          s11, a0, a1
                  c.mv         s1, a2
                  nop
                  c.addi       tp, 1
                  ori          s9, t6, -1838
                  li           s9, 0x330f4ef #start riscv_int_numeric_corner_stream_24
                  li           a0, 0x0
                  li           s8, 0xa5e9117b
                  li           t4, 0x80000000
                  li           t1, 0x0
                  li           t6, 0xffffffff
                  li           s7, 0xda933e61
                  li           s10, 0x80000000
                  li           sp, 0xffffffff
                  li           tp, 0xffffffff
                  divu         t6, s7, t6
                  mulh         t4, sp, s7
                  nop
                  div          t6, tp, s8
                  mul          s7, t4, tp
                  addi         tp, t4, -1714
                  rem          s10, t6, sp
                  addi         s10, s7, -1383
                  lui          t4, 750967
                  remu         s10, tp, t4
                  addi         t6, t1, 334
                  mulh         t1, s8, s8
                  remu         t1, tp, s8
                  divu         a0, t6, t6
                  addi         s8, sp, -1005
                  add          t4, a0, t1
                  mulhu        s9, tp, a0
                  divu         s10, s7, t6
                  mulhu        tp, t1, t1
                  lui          t1, 977934
                  mul          a0, tp, a0
                  mulhsu       s10, s10, t4
                  addi         t6, sp, -1637
                  mulhsu       s9, a0, s8
                  mulh         t1, s10, s9
                  rem          s8, s9, a0 #end riscv_int_numeric_corner_stream_24
                  c.mv         t5, a7
                  slt          a0, t3, a5
                  c.nop
                  c.xor        a0, a0
                  xori         s7, t0, 740
                  rem          s3, ra, s5
                  addi         s8, s11, -512
                  srai         tp, s1, 13
                  mulh         s10, t5, s4
                  c.slli       s10, 21
                  rem          s2, a7, s10
                  auipc        ra, 90518
                  c.addi4spn   a5, sp, 208
                  c.add        s1, a2
                  mulh         t6, s1, t2
                  add          t3, a4, t4
                  c.slli       tp, 13
                  sltu         t6, t0, a0
                  or           s9, a6, a4
                  rem          a3, s4, s3
                  mulhsu       t2, a2, s6
                  sltu         zero, t1, s11
                  sltu         s5, a4, s4
                  li           t0, 0x80000000 #start riscv_int_numeric_corner_stream_18
                  li           s8, 0x80000000
                  li           s4, 0xffffffff
                  li           a2, 0x0
                  li           t4, 0x80000000
                  li           a5, 0x0
                  li           s9, 0xffffffff
                  li           s0, 0x0
                  li           ra, 0x5d67dcf4
                  li           s10, 0xffffffff
                  rem          s8, s8, s0
                  lui          t0, 132877
                  lui          s0, 533170
                  lui          s8, 838635
                  add          t0, s0, s9
                  auipc        s8, 1047566
                  divu         s8, s10, a2
                  mul          t4, s4, ra
                  addi         ra, s0, -1874
                  sub          s9, s10, s9
                  lui          t0, 701510
                  sub          s0, s8, a5
                  remu         t0, s10, s8
                  div          t4, ra, a2
                  mulhsu       s10, s8, ra #end riscv_int_numeric_corner_stream_18
                  rem          s8, s7, a0
                  div          s9, tp, s1
                  and          s10, s7, gp
                  slt          s5, t0, s11
                  div          s11, s4, s9
                  andi         s5, a6, 960
                  sll          a0, s11, s4
                  c.nop
                  nop
                  c.addi       t3, 21
                  slt          tp, s7, s8
                  auipc        tp, 241889
                  sll          t3, ra, t6
                  c.xor        s1, a0
                  and          ra, s7, gp
                  mul          s8, a5, t4
                  remu         s11, s4, a7
                  and          t0, s4, zero
                  mul          a3, a2, t6
                  addi         s9, a3, -1487
                  slli         s0, a5, 30
                  c.srli       s1, 17
                  c.sub        a3, s1
                  sub          ra, a5, s7
                  c.srai       s0, 26
                  rem          a7, gp, s9
                  c.lui        tp, 22
                  auipc        a3, 860186
                  srli         s1, s7, 29
                  c.or         s0, a2
                  div          tp, sp, a7
                  sltiu        s7, sp, 654
                  divu         a3, s3, a6
                  mul          t6, s8, a7
                  add          a2, t3, s9
                  mul          s0, a7, a6
                  c.nop
                  srli         t0, s5, 31
                  sub          a7, s7, a2
                  c.srai       s1, 1
                  c.xor        s1, a3
                  add          t1, a2, s5
                  c.mv         t4, s1
                  sra          s10, a0, s6
                  c.sub        a2, a4
                  c.add        a5, s10
                  mulhsu       gp, t2, a5
                  c.andi       s1, -1
                  remu         t6, s8, a1
                  c.srli       a3, 14
                  sub          t0, t0, s10
                  c.and        s0, a4
                  remu         a7, gp, a3
                  c.slli       s0, 16
                  sltiu        a7, s7, -516
                  c.andi       s1, -1
                  c.srli       s0, 18
                  c.xor        s1, a3
                  srai         s10, t3, 30
                  srai         zero, s10, 6
                  c.li         gp, -1
                  srai         t0, s3, 28
                  c.sub        s0, s1
                  mulhu        a6, s7, t2
                  srli         s5, a4, 31
                  c.li         a0, 15
                  mulhsu       t6, s4, t5
                  or           tp, a4, a6
                  xori         t4, a7, -1126
                  mulhsu       s5, a4, s1
                  c.andi       s0, 29
                  sub          a2, a3, a0
                  c.or         s1, a4
                  sra          s4, zero, s3
                  slti         s3, gp, 1932
                  c.addi4spn   s0, sp, 368
                  c.lui        s2, 19
                  divu         a6, s5, s2
                  auipc        a6, 790275
                  sltu         s2, s4, a0
                  divu         s3, t4, s5
                  c.lui        s9, 7
                  rem          s3, t0, t3
                  add          a2, s3, t0
                  sub          a2, s10, a6
                  and          t1, gp, s0
                  c.or         s1, a4
                  sra          a5, t5, a1
                  c.li         s9, -1
                  ori          s8, s4, -225
                  srl          s3, s5, a0
                  div          t4, a7, t4
                  c.add        a7, a7
                  slli         s4, a2, 28
                  c.slli       s4, 17
                  c.or         a3, s0
                  c.addi4spn   a0, sp, 640
                  slti         zero, a0, -629
                  mulh         sp, s3, s6
                  or           s7, t6, s11
                  slti         s2, t3, 303
                  sltiu        a0, s1, 1028
                  or           a5, a4, t5
                  c.nop
                  sltiu        t0, s0, 961
                  remu         t0, s3, s9
                  slti         s1, s11, 1731
                  mulh         tp, s1, t0
                  div          t4, a2, a2
                  c.srli       a2, 6
                  c.lui        s5, 12
                  div          t4, t1, s9
                  c.addi4spn   s0, sp, 64
                  c.xor        a5, a0
                  lui          s3, 377722
                  c.add        t5, s11
                  ori          t1, s1, 419
                  slt          t0, s11, s11
                  div          tp, a1, a0
                  sltu         sp, ra, t2
                  add          s7, a0, gp
                  srl          zero, a2, a7
                  c.andi       a5, 13
                  div          ra, t3, t5
                  c.lui        s1, 7
                  auipc        t5, 622329
                  slt          gp, a5, zero
                  sltu         a3, ra, a1
                  lui          tp, 529695
                  mulhsu       ra, zero, s4
                  add          sp, s4, tp
                  srl          s1, t5, s5
                  ori          a3, a0, -1601
                  sll          s4, t5, a6
                  c.addi4spn   a2, sp, 128
                  c.srli       a3, 28
                  srai         t1, a2, 17
                  add          s0, tp, s4
                  mulh         s1, a0, a7
                  remu         s3, a4, s3
                  div          t1, t6, s7
                  c.add        s5, t3
                  c.sub        s1, a1
                  nop
                  c.nop
                  ori          s7, a4, -1605
                  slli         s5, s0, 30
                  c.nop
                  slti         s5, s9, 1749
                  c.srai       a2, 17
                  c.and        s0, a4
                  c.and        a3, s1
                  c.sub        a0, a1
                  c.and        a3, s1
                  divu         t0, s0, t3
                  slti         s1, s6, -1420
                  xor          a7, tp, ra
                  c.addi4spn   s1, sp, 176
                  c.nop
                  c.sub        a2, a4
                  slti         s3, a0, 1501
                  slli         t2, a0, 23
                  nop
                  add          s7, t2, s11
                  c.or         a3, a3
                  sltu         sp, t6, t4
                  sra          s4, s1, t3
                  srli         s3, t6, 9
                  divu         t6, a4, s11
                  srli         t5, a3, 6
                  andi         t0, gp, 379
                  slti         gp, s0, 439
                  slti         s1, a0, 1767
                  slli         s1, a6, 7
                  mulhsu       s8, s9, s8
                  divu         s0, s1, s9
                  c.lui        s1, 6
                  addi         s1, a5, -771
                  lui          t2, 428664
                  c.add        ra, ra
                  addi         gp, s1, 106
                  c.nop
                  slli         gp, a6, 24
                  c.and        a5, a0
                  rem          s8, s3, a6
                  ori          t5, s2, -1663
                  remu         gp, s2, s10
                  mulhu        s4, t0, t0
                  auipc        s10, 812642
                  sltiu        t5, a1, -483
                  c.srai       s1, 6
                  c.addi4spn   a2, sp, 16
                  c.nop
                  srl          s4, t6, s1
                  c.xor        a0, a1
                  sltu         t1, a1, s5
                  srli         a5, s10, 23
                  c.or         a5, s0
                  slti         gp, t2, 2043
                  mulhsu       a0, a4, a2
                  c.and        a2, a5
                  srai         a0, a7, 31
                  mulh         s1, a3, ra
                  auipc        s11, 93371
                  mulhsu       gp, a0, t3
                  c.or         a5, s1
                  c.mv         s8, s9
                  lui          t6, 588918
                  sra          t0, s1, s9
                  and          t1, sp, a2
                  c.sub        a2, a3
                  c.srli       a0, 17
                  slti         tp, a3, -1002
                  or           t1, a3, a1
                  xori         t5, zero, -1730
                  sltu         tp, t3, s1
                  c.andi       a3, 9
                  c.or         a0, a3
                  or           a2, a5, a3
                  xori         t4, a1, -1957
                  rem          s0, a4, a5
                  addi         s7, a5, -777
                  c.and        a0, s0
                  addi         a6, t1, 1541
                  c.srai       a5, 16
                  slti         t4, a4, 1082
                  slli         a2, tp, 31
                  slti         ra, ra, -2006
                  rem          t1, tp, s4
                  slt          s11, s6, a4
                  auipc        t5, 710213
                  mulhsu       t4, s2, s7
                  mul          s0, t4, t6
                  sltiu        t0, a1, -1989
                  c.or         a0, a1
                  c.add        s0, t6
                  lui          s1, 339532
                  c.xor        a5, a2
                  xor          a6, zero, s2
                  add          a0, s2, a0
                  lui          sp, 515906
                  c.addi       s11, -1
                  sltiu        s10, s4, -204
                  mulh         s2, s11, t5
                  c.sub        s1, a3
                  c.or         s1, a5
                  xori         s10, t0, -1048
                  xori         s8, s4, 1426
                  mulhu        s2, s6, zero
                  c.add        a0, a6
                  slti         s10, zero, -811
                  c.or         a5, a4
                  nop
                  srli         s4, a3, 19
                  nop
                  c.mv         t0, a5
                  c.addi4spn   a2, sp, 288
                  srai         s9, a0, 15
                  c.addi       sp, -1
                  slt          gp, t2, s7
                  srai         t5, t0, 16
                  c.srli       a5, 6
                  c.xor        a2, a5
                  c.andi       s0, 30
                  xori         a3, t2, -194
                  xor          s8, s8, t0
                  c.addi4spn   a2, sp, 896
                  andi         t3, a0, 1677
                  sll          s2, ra, a7
                  srai         gp, s2, 3
                  divu         t4, t6, a3
                  c.srli       a0, 27
                  c.and        s1, a0
                  ori          t1, t2, 899
                  srli         a2, sp, 22
                  mulh         ra, a0, s6
                  srl          ra, s7, t2
                  sll          s10, a6, tp
                  slti         a0, s1, -947
                  sltu         s7, t4, sp
                  slli         sp, sp, 5
                  remu         sp, s1, ra
                  c.mv         t5, a0
                  sltiu        s3, s6, -1129
                  xor          gp, a5, t1
                  c.sub        s1, s0
                  c.li         t5, -1
                  srli         s4, s9, 26
                  add          a3, a5, t4
                  div          a2, s11, s11
                  c.add        tp, s6
                  lui          s3, 919969
                  sltu         gp, t6, a3
                  sub          a0, s10, a2
                  xor          t6, s10, s10
                  slt          a6, t4, s5
                  c.sub        a2, a3
                  nop
                  xor          t0, a0, s11
                  sll          a6, t0, tp
                  xor          tp, ra, a0
                  sll          t1, t0, t1
                  add          gp, t3, s0
                  div          s0, a4, t1
                  c.sub        s0, a2
                  c.sub        a3, s1
                  sll          t6, a4, s5
                  xori         zero, a5, 344
                  xor          a3, t0, s8
                  c.or         a0, a0
                  xori         s8, t1, -1924
                  mulh         t0, gp, a6
                  sltiu        a7, t1, -1539
                  xor          t1, t3, s11
                  add          t5, s9, tp
                  c.and        a0, a4
                  c.or         a3, a5
                  slli         t0, a4, 14
                  remu         a3, t2, t3
                  c.addi16sp   sp, 480
                  c.nop
                  sltiu        s9, sp, -411
                  mulhu        s9, tp, zero
                  srli         sp, t3, 22
                  slti         a3, s10, -1013
                  mulh         tp, t5, t2
                  or           zero, a3, s4
                  c.srai       s1, 16
                  add          s4, t0, zero
                  xor          ra, t3, a0
                  and          t4, sp, a7
                  xori         zero, sp, 62
                  xori         t6, t4, 12
                  c.li         s7, 17
                  c.andi       a0, -1
                  lui          t2, 969167
                  remu         gp, t5, a4
                  c.slli       s9, 5
                  c.xor        a0, a3
                  c.mv         ra, s7
                  c.srli       a0, 18
                  c.sub        a3, a2
                  xor          s2, s8, sp
                  sltu         s4, a5, ra
                  mulh         s11, s11, a4
                  mul          a6, a7, a6
                  c.nop
                  mul          a3, a5, s4
                  sra          a0, s7, t2
                  c.slli       s8, 8
                  c.add        s5, s11
                  lui          sp, 521085
                  sll          s10, s7, a4
                  and          t6, t2, a0
                  or           s7, zero, s3
                  c.addi       s5, 29
                  c.li         a2, -1
                  srai         t3, s8, 29
                  ori          s1, s3, 832
                  mul          s9, a4, a4
                  c.li         a3, -1
                  c.addi4spn   a2, sp, 112
                  auipc        t6, 467024
                  c.mv         t5, sp
                  c.addi4spn   a0, sp, 128
                  sra          s10, a0, t2
                  c.mv         a0, t2
                  div          a7, sp, t5
                  andi         t3, s7, 1702
                  slti         s1, a7, -991
                  srai         tp, gp, 10
                  mul          a0, a3, gp
                  c.or         a0, a5
                  sub          s5, s6, s3
                  lui          t3, 277629
                  mulhu        a6, sp, t5
                  sub          a2, a5, a6
                  nop
                  c.srli       s0, 15
                  and          s3, a6, s10
                  c.lui        s0, 9
                  c.xor        a3, a5
                  div          a2, a3, t4
                  srl          t6, t4, s7
                  ori          ra, a2, 1428
                  auipc        s5, 160476
                  and          ra, t5, s7
                  sub          t5, s10, s3
                  ori          tp, a7, -1233
                  xori         s11, s5, 154
                  nop
                  c.mv         t5, gp
                  auipc        t4, 816808
                  mulhu        t4, s9, t0
                  c.nop
                  slt          s8, a7, t2
                  mulhu        gp, s0, s1
                  c.lui        s8, 30
                  c.add        a0, a5
                  c.srli       a0, 27
                  c.andi       s1, -1
                  nop
                  c.slli       s1, 24
                  sra          tp, ra, s11
                  sra          t2, tp, ra
                  c.addi16sp   sp, 80
                  srl          gp, a4, s1
                  mul          a3, gp, s4
                  div          s1, t6, a7
                  div          t2, s8, a7
                  mulhsu       s11, s2, s5
                  c.srli       a3, 18
                  c.lui        s4, 10
                  lui          a6, 65485
                  xori         a3, t5, -1564
                  c.addi16sp   sp, 368
                  addi         t5, a2, 1052
                  srli         gp, t0, 3
                  xori         a0, t6, -729
                  c.andi       s1, 21
                  c.xor        a5, a5
                  nop
                  or           t2, gp, t0
                  c.nop
                  c.srli       a5, 24
                  rem          s7, s10, s4
                  mulh         t6, sp, a3
                  c.srai       a0, 13
                  c.addi       a0, 20
                  sltiu        t6, a1, -1164
                  c.srli       a0, 7
                  rem          zero, a5, t0
                  xori         s3, a5, 402
                  mul          s4, t4, s3
                  sra          t2, t2, s8
                  c.addi4spn   a0, sp, 32
                  c.nop
                  sra          s8, ra, ra
                  add          sp, gp, s5
                  slti         s0, tp, -628
                  div          a7, t2, a2
                  srai         s3, t2, 10
                  addi         s7, a4, -707
                  or           s2, s3, s10
                  srai         a3, s5, 29
                  c.srli       a2, 20
                  c.srai       s1, 31
                  nop
                  nop
                  c.mv         a7, s9
                  sll          s1, s3, s2
                  c.xor        a3, a3
                  xor          t0, a1, s10
                  c.mv         ra, a5
                  slt          s3, s3, s11
                  and          s2, t4, s10
                  slti         a5, s5, -1998
                  sub          t3, s9, t5
                  divu         a7, a0, tp
                  c.li         s7, -1
                  andi         s5, t6, -1091
                  c.srli       s0, 30
                  slti         s1, gp, -1297
                  mulhsu       s1, t4, t3
                  slti         ra, t3, -1665
                  mulhu        t3, a3, s9
                  c.mv         s3, s5
                  remu         t6, t1, s1
                  andi         s4, s2, 1821
                  nop
                  c.srli       a3, 20
                  c.mv         s8, s1
                  c.addi       a6, 9
                  c.srai       s1, 19
                  c.addi       s8, -1
                  c.addi16sp   sp, 336
                  xor          t5, t6, t5
                  remu         t5, s11, s7
                  c.addi4spn   a0, sp, 240
                  remu         s10, s8, tp
                  c.lui        s1, 12
                  c.nop
                  mulhsu       s8, t5, s2
                  slt          sp, a4, s5
                  c.add        a0, s9
                  slti         a2, gp, 646
                  srli         s0, a3, 10
                  c.or         a0, a5
                  or           a0, s6, ra
                  srai         t3, a7, 10
                  c.andi       s1, 16
                  c.xor        a5, s0
                  add          t1, t0, s9
                  sltiu        a7, a2, 297
                  xori         s3, zero, -1207
                  c.add        t5, s10
                  c.slli       a0, 29
                  c.lui        a6, 2
                  c.lui        s9, 25
                  xor          a3, zero, a0
                  ori          t6, s1, -273
                  slli         t5, gp, 22
                  sltiu        a2, s8, 197
                  addi         t2, a0, 1591
                  slti         zero, sp, 541
                  sltiu        s10, s0, -719
                  slli         s9, s11, 2
                  and          sp, t5, s11
                  c.slli       t3, 2
                  add          s2, s7, a5
                  slli         t0, gp, 17
                  xor          s9, s6, s2
                  c.nop
                  nop
                  c.andi       a0, -1
                  c.add        t6, s6
                  mulhsu       s3, sp, t1
                  add          ra, tp, t2
                  c.addi16sp   sp, -16
                  c.li         t2, -1
                  lui          sp, 21023
                  c.or         a3, a0
                  c.lui        t1, 29
                  mulh         sp, t6, t4
                  slli         s9, zero, 12
                  c.li         gp, 5
                  sra          s0, s7, s1
                  c.mv         t0, gp
                  add          a3, t3, s1
                  sll          a2, s5, ra
                  add          t2, ra, s7
                  divu         s5, t2, tp
                  slt          s7, a0, a7
                  srai         t1, t0, 31
                  divu         s9, ra, a0
                  xor          s3, s11, tp
                  or           a6, t1, s6
                  rem          t6, a0, ra
                  or           s8, s5, s11
                  ori          s9, s3, -1401
                  c.andi       a3, 7
                  mulhsu       s7, s4, s0
                  mulhsu       a3, t2, s2
                  c.addi       a0, -1
                  c.xor        a3, s0
                  or           t5, s4, zero
                  mulhsu       s4, t4, t1
                  c.addi       t5, -1
                  lui          t0, 211687
                  c.slli       s8, 9
                  c.andi       s0, 12
                  sltiu        gp, a4, 76
                  c.mv         s4, t6
                  andi         s8, a1, -1394
                  mul          t4, a0, a4
                  slt          s10, t4, a5
                  sra          a6, s6, gp
                  c.xor        s0, a3
                  c.mv         tp, ra
                  auipc        s9, 827492
                  c.addi4spn   a0, sp, 432
                  c.xor        a2, s0
                  c.nop
                  srli         s10, t0, 14
                  c.nop
                  c.addi       tp, -1
                  mulhsu       a3, s0, t5
                  slt          ra, a0, s9
                  c.slli       s9, 30
                  srl          ra, tp, t5
                  andi         gp, sp, -225
                  mulhsu       t5, a6, t5
                  c.addi16sp   sp, -16
                  c.slli       s11, 1
                  c.srai       a2, 23
                  c.li         a5, -1
                  divu         t3, s10, ra
                  mulhsu       sp, a4, a2
                  c.nop
                  srli         s9, t1, 11
                  c.srai       a2, 31
                  andi         a3, ra, 717
                  andi         a3, a1, 980
                  c.sub        a5, a2
                  mul          ra, t3, a0
                  slti         s2, s2, 1459
                  div          t6, s6, t3
                  srai         s0, s8, 5
                  c.addi16sp   sp, 352
                  mulhu        s0, s1, s9
                  c.sub        a2, a3
                  xor          s2, t4, s1
                  c.addi4spn   a3, sp, 224
                  c.and        s1, a2
                  c.mv         t6, s10
                  ori          s10, a5, 1588
                  add          s2, a6, tp
                  xor          t4, s1, s9
                  c.or         a2, a4
                  srli         a2, s10, 1
                  slt          t1, s11, t1
                  c.slli       a7, 6
                  c.xor        a5, a5
                  xor          zero, t1, s11
                  sltu         s3, s5, t0
                  slti         t1, s8, -881
                  slti         s3, a4, 1807
                  addi         s3, s6, -1398
                  mul          sp, a1, a0
                  c.lui        t6, 16
                  c.nop
                  srli         s10, a3, 0
                  xori         gp, t5, 1576
                  lui          a5, 272289
                  srai         a2, t5, 1
                  slli         t2, s5, 6
                  slti         a7, s0, 1081
                  xori         t0, zero, 1415
                  nop
                  c.slli       t1, 29
                  c.li         s8, -1
                  mulhsu       tp, t3, a0
                  and          t5, s3, s5
                  auipc        t5, 543288
                  c.srli       s1, 22
                  mulhu        ra, t4, s5
                  c.mv         a2, s0
                  nop
                  lui          s0, 506271
                  auipc        sp, 1031483
                  mulhsu       s5, s6, t6
                  xor          s5, a3, a2
                  mulh         s9, s0, a7
                  c.xor        s0, a5
                  sub          ra, s10, sp
                  c.slli       gp, 29
                  c.or         a5, s0
                  c.li         a3, -1
                  c.mv         s10, s7
                  c.li         gp, 9
                  mulh         a0, s10, a5
                  andi         zero, a3, 1272
                  andi         ra, ra, 38
                  sub          a5, s5, s1
                  xori         s7, gp, -1139
                  srli         a6, a4, 23
                  c.add        t4, s11
                  c.srai       a2, 14
                  lui          t5, 930186
                  remu         s7, t3, t2
                  sltu         t2, s4, s11
                  sll          t3, t6, s8
                  c.slli       s3, 5
                  srai         tp, s3, 2
                  or           a2, gp, s11
                  slt          a3, t0, s8
                  mulh         s9, s10, ra
                  remu         s11, a0, s11
                  div          t4, t2, s11
                  and          s1, ra, t4
                  mulhsu       a3, t1, t2
                  sra          gp, a0, s6
                  li           gp, 0x53d18c2d #start riscv_int_numeric_corner_stream_11
                  li           s0, 0x8a4b32d4
                  li           ra, 0xa1f73880
                  li           a6, 0xffffffff
                  li           a3, 0x98a4b1ac
                  li           sp, 0xffffffff
                  li           t3, 0xadfb5707
                  li           s11, 0x0
                  li           a7, 0x0
                  li           t5, 0x80000000
                  mul          sp, t3, s0
                  remu         a3, s11, a3
                  nop
                  mulhsu       a6, t3, s11
                  mul          sp, t3, gp
                  mulh         a3, s11, t3
                  nop
                  mulh         gp, gp, t5
                  mulh         s11, gp, sp
                  auipc        a7, 890469
                  div          s11, sp, a3
                  rem          ra, ra, s11
                  mulh         t5, sp, s11
                  addi         s11, gp, -887
                  mulhsu       a7, gp, gp
                  nop
                  addi         s0, s0, 1761
                  divu         a7, t5, a3
                  remu         s0, a7, a6
                  remu         s0, s0, gp
                  rem          sp, t3, sp
                  mulh         s0, a7, gp #end riscv_int_numeric_corner_stream_11
                  srl          s4, a7, t1
                  andi         a5, t4, -1997
                  divu         a2, s8, gp
                  nop
                  divu         s5, s8, s9
                  mulhsu       t1, s2, s6
                  sra          a0, a0, t3
                  c.xor        s0, a4
                  c.sub        s1, a5
                  div          t1, t5, a7
                  c.andi       s0, 30
                  c.nop
                  c.addi16sp   sp, 112
                  slli         s10, t1, 6
                  sll          s11, s8, s4
                  c.and        a3, a2
                  slt          s5, s7, s4
                  c.addi16sp   sp, 288
                  mul          a2, a3, s8
                  c.addi       t1, 10
                  lui          t6, 207394
                  lui          tp, 46337
                  slti         t5, s4, -1970
                  auipc        s4, 971255
                  add          a5, s0, sp
                  c.addi       a0, -1
                  or           a3, ra, s6
                  mulhu        t2, t4, s2
                  c.addi       s0, -1
                  c.andi       s1, -1
                  sra          s9, a6, t6
                  c.or         a0, a1
                  c.andi       s1, 30
                  rem          t3, t5, tp
                  ori          s8, ra, -952
                  nop
                  c.slli       s1, 15
                  slt          zero, t5, a0
                  slli         s10, s9, 30
                  c.mv         s4, a6
                  c.addi4spn   a2, sp, 720
                  srl          a3, a5, a7
                  srli         a5, a7, 9
                  srai         s0, s3, 1
                  c.andi       a0, -1
                  sub          s5, s3, a0
                  div          s8, zero, s8
                  rem          ra, s11, gp
                  xori         a2, sp, -1384
                  nop
                  andi         t3, a5, -1069
                  xori         s8, s4, 509
                  andi         t2, t4, -1622
                  sub          s8, s6, gp
                  c.and        a2, a2
                  ori          sp, t6, 1221
                  remu         t0, s1, a2
                  c.or         a3, s1
                  srl          s9, s10, t1
                  mulh         s4, tp, s8
                  c.xor        a0, s0
                  add          s2, a3, s8
                  sub          s4, s11, s2
                  mul          t2, a0, gp
                  sub          s2, a5, sp
                  remu         t5, t4, t6
                  rem          a6, s8, s11
                  xor          s7, s1, s3
                  c.addi4spn   a3, sp, 720
                  or           s7, t1, t2
                  c.sub        a5, a5
                  slt          sp, a6, s9
                  c.addi       t0, -1
                  c.addi       s11, -1
                  andi         t3, t3, 1333
                  sra          s5, s4, a7
                  c.sub        a5, a2
                  mulhsu       s3, s7, s4
                  c.add        a0, a5
                  c.srai       a3, 19
                  c.and        s0, a2
                  c.addi4spn   a2, sp, 176
                  divu         s2, a6, s6
                  c.andi       a3, 19
                  c.and        a2, a5
                  c.li         s1, 17
                  slli         s2, s1, 24
                  c.mv         a3, t0
                  c.and        s1, a3
                  c.xor        a3, a0
                  c.add        t2, t5
                  xor          a3, a7, t0
                  sll          t0, t3, s4
                  c.slli       t4, 21
                  c.lui        a2, 4
                  c.andi       a5, 5
                  c.add        sp, s2
                  c.li         s8, -1
                  rem          s5, s5, gp
                  c.srai       a5, 5
                  srli         s11, s10, 5
                  sll          t3, a1, t0
                  slli         s9, t1, 9
                  slti         s3, tp, -1665
                  c.li         s7, 18
                  c.addi       a0, -1
                  nop
                  c.addi       t5, -1
                  mulhu        s11, s0, s9
                  c.li         s8, -1
                  c.lui        s9, 17
                  mulhsu       a6, s6, s6
                  sltu         a6, t4, s6
                  c.nop
                  c.and        s0, s0
                  mulhu        sp, t6, sp
                  slti         a7, a3, 668
                  sra          a3, a1, s4
                  mul          t2, s9, tp
                  c.xor        a5, s1
                  c.slli       a6, 27
                  c.addi16sp   sp, -16
                  c.or         s0, a1
                  mulhsu       t3, t3, s1
                  xori         t0, s10, -709
                  c.xor        s1, a1
                  div          t6, s3, t4
                  sltu         a2, s1, s9
                  div          t5, zero, sp
                  c.srai       a5, 21
                  lui          s9, 42655
                  sub          a6, t6, a5
                  addi         a2, a2, 1161
                  sll          s4, s2, tp
                  srli         a7, t0, 15
                  xor          a2, s4, gp
                  mulhsu       a3, s0, s2
                  srai         s11, a5, 14
                  li           s7, 0xffffffff #start riscv_int_numeric_corner_stream_34
                  li           t1, 0x80000000
                  li           gp, 0x0
                  li           t6, 0x80000000
                  li           s9, 0x0
                  li           a7, 0x80000000
                  li           s2, 0xbc5ff231
                  li           s4, 0x80000000
                  li           a5, 0xffffffff
                  li           s3, 0x0
                  mul          s7, s4, s4
                  mulhu        s4, s4, gp
                  auipc        s2, 30189
                  div          s2, t1, gp
                  mulhsu       a5, a7, s7
                  divu         t1, s9, s4
                  add          a7, s7, a5
                  div          s2, a5, s9
                  auipc        s9, 256389
                  rem          s7, s2, s9
                  sub          t1, s9, t1
                  mulhu        gp, s9, s9
                  mulhsu       s3, s9, t6
                  mulhu        s3, gp, t1
                  remu         gp, s4, a7 #end riscv_int_numeric_corner_stream_34
                  andi         a6, s5, 1543
                  c.srli       a0, 21
                  c.and        a5, a1
                  ori          s1, t3, -151
                  mul          t5, a4, a0
                  div          t1, t5, s6
                  divu         t0, t0, a7
                  srli         s5, t6, 23
                  c.li         gp, -1
                  c.or         a3, s1
                  sub          s1, t3, t2
                  sra          t1, a7, sp
                  slt          s10, a4, s11
                  and          sp, a3, tp
                  c.or         a2, s0
                  addi         s7, s1, -1689
                  c.mv         t6, s9
                  mul          t0, s10, s11
                  c.xor        a0, a3
                  slli         t3, a7, 8
                  sra          a3, a0, ra
                  c.addi       s9, -1
                  c.and        a3, a2
                  c.li         gp, -1
                  c.add        s4, s1
                  srai         zero, a5, 5
                  c.nop
                  c.xor        a0, s0
                  slli         a7, s10, 5
                  c.and        s0, a5
                  c.addi16sp   sp, 64
                  and          t2, s6, s5
                  nop
                  ori          t0, s2, -767
                  auipc        t5, 212986
                  div          a7, s0, a2
                  srai         zero, a6, 5
                  c.addi16sp   sp, 208
                  lui          tp, 840307
                  slli         t3, a3, 17
                  c.and        s0, a1
                  mulhu        tp, a1, t6
                  or           t2, tp, s6
                  c.add        sp, tp
                  c.addi       a0, -1
                  c.xor        a5, a2
                  c.xor        a2, a0
                  c.addi       a5, -1
                  or           t4, a5, a2
                  c.srai       a0, 20
                  c.and        a2, a2
                  c.or         s1, a1
                  c.or         a5, s1
                  slti         a0, s9, 1347
                  c.xor        s1, a4
                  c.add        s10, t2
                  sra          sp, s9, sp
                  auipc        a3, 630981
                  c.xor        a0, a4
                  c.srli       a0, 18
                  c.xor        s0, s0
                  c.srli       a3, 15
                  mulhu        s7, gp, s5
                  c.srli       a2, 22
                  slti         s1, s8, 1425
                  slt          a0, zero, t1
                  slli         s11, s11, 19
                  div          tp, a2, s10
                  nop
                  sub          sp, t5, t4
                  c.nop
                  c.addi4spn   s1, sp, 32
                  nop
                  auipc        s8, 466474
                  c.or         s0, a4
                  addi         s8, tp, 1020
                  mulhsu       s0, t0, a1
                  c.addi       t3, -1
                  andi         zero, t3, 1824
                  mul          t5, tp, s3
                  sltu         t0, s9, a6
                  or           s11, s11, zero
                  div          s8, t4, a0
                  sll          t3, a0, t4
                  divu         tp, s3, t0
                  c.srli       a5, 2
                  srli         s10, t5, 21
                  auipc        ra, 882784
                  c.addi16sp   sp, -16
                  srai         zero, a1, 0
                  c.addi16sp   sp, -16
                  and          t6, s0, a2
                  sll          s10, a2, a6
                  add          s10, s9, gp
                  mulhsu       ra, gp, t4
                  mul          tp, s6, t4
                  addi         s2, a7, 1137
                  c.addi16sp   sp, 496
                  srai         s11, s1, 1
                  c.slli       a7, 2
                  c.sub        a5, a3
                  slt          s0, s8, s11
                  slti         ra, t2, 1792
                  nop
                  remu         s2, a6, a1
                  c.or         a0, a0
                  remu         s9, sp, s8
                  c.and        s1, s0
                  c.nop
                  c.xor        a0, a1
                  c.slli       t0, 14
                  divu         a3, t4, tp
                  mulh         sp, t5, t4
                  c.srli       a5, 5
                  srai         a6, gp, 3
                  c.xor        a0, a3
                  c.li         t3, 12
                  slt          s1, s10, s5
                  c.or         s0, a1
                  c.li         s5, -1
                  xor          t6, s2, zero
                  sltu         s1, a2, s5
                  sltiu        s11, a1, 1044
                  c.xor        a5, a4
                  mulhu        ra, t0, s4
                  slli         t6, s7, 18
                  mulh         s8, s7, a7
                  add          s8, t0, zero
                  xor          t6, t2, s8
                  and          a0, t0, a2
                  sltu         t1, t0, s1
                  andi         t2, s7, -889
                  slt          gp, s0, s1
                  c.and        a2, a4
                  divu         tp, ra, s3
                  mulh         s1, s0, ra
                  auipc        a6, 538244
                  srli         a7, gp, 4
                  srl          sp, a6, t0
                  mulhsu       t4, s2, a4
                  add          s5, a3, s7
                  mulhsu       s2, s9, a4
                  xor          sp, s11, t3
                  divu         s10, zero, t6
                  srai         ra, s9, 15
                  mulhsu       t5, s4, t6
                  and          s2, a5, a6
                  c.xor        a5, a0
                  c.or         a0, a5
                  srli         gp, s1, 30
                  c.or         s0, a1
                  mul          zero, tp, t6
                  xor          zero, ra, t0
                  c.and        a5, s0
                  c.nop
                  divu         a5, s6, s8
                  remu         zero, s4, ra
                  or           a2, s6, s3
                  mulhsu       s2, sp, s5
                  mulhu        t4, s11, ra
                  slti         t4, t4, 109
                  auipc        s4, 834391
                  addi         s0, s3, 1974
                  c.addi       s2, -1
                  remu         s2, s11, s0
                  c.slli       gp, 16
                  mulhu        tp, t6, s6
                  mulh         gp, s1, t2
                  sub          s3, a5, ra
                  srai         t5, a4, 18
                  addi         s7, t6, -454
                  sll          a7, t4, s11
                  c.lui        gp, 19
                  nop
                  srl          ra, tp, s0
                  c.nop
                  c.and        s1, a4
                  sub          s0, a2, t3
                  c.srli       s0, 23
                  addi         s5, t5, 1828
                  slli         s8, t3, 24
                  ori          s0, gp, 79
                  c.addi4spn   a0, sp, 480
                  c.srli       a5, 18
                  c.addi16sp   sp, 320
                  c.lui        gp, 3
                  c.nop
                  addi         t6, a2, -1691
                  slt          s5, t2, t5
                  slt          s9, a6, t0
                  add          s1, s10, a4
                  c.andi       s0, 9
                  c.andi       s0, -1
                  sltiu        s3, s0, -1027
                  addi         gp, a0, -1267
                  and          s4, s6, a5
                  div          zero, a5, ra
                  c.srli       s0, 24
                  lui          s3, 387382
                  c.nop
                  c.and        a5, a4
                  sltiu        t0, a1, -789
                  mulhu        t2, s2, zero
                  rem          a5, a5, t2
                  c.andi       a5, -1
                  c.mv         s7, s11
                  c.lui        ra, 12
                  srl          t1, t0, a4
                  xori         s8, t0, -433
                  sltiu        s9, s8, -529
                  and          a0, a4, t3
                  c.addi16sp   sp, 160
                  sll          t0, zero, s3
                  auipc        a5, 256600
                  xor          t6, a4, a6
                  xor          t3, t4, t5
                  remu         a6, s1, tp
                  mulhsu       t4, a5, s1
                  lui          tp, 606085
                  c.or         a0, s0
                  auipc        ra, 723628
                  sltu         s11, zero, gp
                  lui          tp, 802943
                  mulhsu       t5, a3, t5
                  divu         a0, t3, a7
                  nop
                  divu         s0, t0, t4
                  mulhsu       t6, gp, t2
                  c.addi       s9, 25
                  mulhsu       sp, s2, t2
                  divu         t0, s0, s6
                  and          t0, t1, t1
                  addi         t2, t1, -563
                  slt          zero, s9, a0
                  c.slli       s1, 25
                  sltu         a0, a7, s10
                  slt          s1, a3, s1
                  mulhu        s11, a5, t1
                  srai         s2, t1, 10
                  slli         t4, t4, 2
                  mul          tp, s4, t5
                  divu         s11, t4, t4
                  addi         t4, a6, -1740
                  rem          sp, s5, a4
                  c.lui        s5, 31
                  remu         a6, a6, s8
                  srli         t5, s7, 19
                  c.lui        s10, 10
                  slt          zero, s5, s1
                  c.and        s0, a4
                  add          s1, a3, s1
                  c.srli       a5, 9
                  c.srai       s1, 21
                  c.add        t1, t0
                  mulhu        gp, a0, t2
                  c.add        a2, s2
                  div          s1, s7, t2
                  c.andi       s1, 5
                  c.or         a5, a0
                  xor          a5, s5, a1
                  c.and        s1, a0
                  c.and        s1, s1
                  srli         a6, t2, 24
                  andi         t3, t6, -1783
                  sll          t5, t2, a7
                  srli         a6, gp, 22
                  add          s9, t0, a7
                  c.sub        a0, a5
                  srl          a2, s9, t0
                  c.sub        s0, a5
                  sltu         ra, t3, s6
                  xor          t6, t0, s9
                  mulhu        s8, s6, a4
                  and          a6, a1, a5
                  c.addi16sp   sp, -16
                  c.srai       a3, 3
                  srl          s5, zero, s8
                  c.addi       t2, 10
                  mulhsu       a0, t4, a5
                  c.addi16sp   sp, -16
                  c.mv         t2, s3
                  andi         a5, a1, -972
                  sra          s9, s6, a5
                  remu         s5, s3, ra
                  c.xor        a5, s0
                  divu         tp, t6, s8
                  c.mv         sp, a6
                  srai         t3, s4, 23
                  nop
                  sltu         t3, t1, s2
                  slt          s4, t2, s11
                  c.and        a2, a4
                  c.add        a0, s8
                  c.nop
                  slt          s5, s3, t1
                  c.srli       s0, 10
                  auipc        s3, 1030305
                  c.nop
                  slt          t0, t3, s4
                  rem          gp, s11, a4
                  c.srli       a5, 27
                  andi         t4, t5, -432
                  and          s0, a0, t3
                  mul          s11, s11, a7
                  srl          a7, gp, s4
                  srli         s5, s11, 27
                  addi         s10, a2, 491
                  addi         t6, s7, 1968
                  c.and        a3, a4
                  srai         s4, gp, 31
                  srl          a2, a0, s9
                  andi         s11, s4, 1106
                  sub          a2, a3, a4
                  c.li         s8, -1
                  c.srai       a2, 9
                  c.li         a2, 22
                  slti         a5, a4, 1565
                  rem          ra, s0, a7
                  mulhu        t0, a1, s5
                  c.andi       a3, -1
                  auipc        tp, 405342
                  c.or         a3, s1
                  slli         tp, a7, 6
                  lui          a2, 63355
                  divu         s8, a0, a0
                  c.addi       a2, 27
                  xor          s4, tp, zero
                  sll          s7, a0, a4
                  c.andi       a5, -1
                  srai         t1, t3, 28
                  mul          s5, s7, ra
                  add          ra, s2, t5
                  c.addi4spn   a5, sp, 272
                  remu         t0, t1, t1
                  c.mv         ra, a4
                  nop
                  xori         s2, t3, -1379
                  c.lui        tp, 4
                  auipc        s10, 46179
                  sra          s5, t3, s1
                  c.or         a2, a5
                  c.add        tp, t6
                  c.lui        t3, 15
                  c.sub        a2, a2
                  add          s0, a2, s4
                  mulhu        s11, a4, s5
                  srl          a7, sp, a2
                  c.mv         a7, s8
                  c.andi       a3, 16
                  c.sub        s0, s0
                  sltu         s2, a6, a3
                  c.addi4spn   s1, sp, 432
                  c.sub        s0, a0
                  c.srli       a5, 18
                  mulhsu       t3, a2, t2
                  sll          a6, s9, t4
                  c.nop
                  srli         a6, t1, 18
                  srai         t5, zero, 1
                  sltu         a6, t4, zero
                  sub          s5, s4, t3
                  c.slli       s9, 3
                  c.slli       gp, 9
                  lui          s1, 214210
                  slli         tp, s2, 9
                  srl          a5, s8, a7
                  lui          sp, 308766
                  mul          a3, a3, s8
                  auipc        a2, 889954
                  slli         s1, sp, 22
                  sra          s7, a3, a4
                  xor          s8, a1, gp
                  and          a2, t6, s2
                  c.li         ra, 24
                  mulhsu       a5, t6, t0
                  sub          s10, s9, tp
                  srai         s5, a7, 24
                  nop
                  mulhu        sp, a4, t2
                  c.andi       a5, 5
                  mul          zero, s6, t2
                  rem          a0, a3, s3
                  sra          t4, t5, a1
                  sra          t6, a0, s4
                  c.lui        t1, 9
                  c.srai       s1, 19
                  slti         ra, s6, 1122
                  sub          t6, s11, a5
                  mulh         t2, t5, t3
                  slli         a5, s8, 3
                  srl          a7, a2, s11
                  srl          gp, zero, t2
                  c.addi       s0, -1
                  divu         s3, s11, a4
                  c.add        ra, a2
                  remu         t4, a7, s2
                  mulhu        s5, t1, t2
                  c.li         a0, -1
                  auipc        s11, 540325
                  c.slli       gp, 13
                  c.lui        s8, 30
                  and          s3, t6, s11
                  mulhsu       s1, t6, t1
                  c.slli       t4, 4
                  mulh         zero, s2, s2
                  lui          s7, 73969
                  mul          a3, sp, t3
                  srl          s7, a6, zero
                  c.add        a2, ra
                  mulh         s0, a0, s0
                  c.addi4spn   a0, sp, 48
                  c.mv         s9, s4
                  srai         s4, a2, 31
                  nop
                  addi         t1, a1, 1924
                  mulhsu       t2, t1, t3
                  c.addi       t4, -1
                  c.addi       s4, -1
                  sll          a7, s8, t3
                  srai         a2, s10, 15
                  slli         s11, s10, 9
                  and          a0, a6, s9
                  c.addi4spn   a2, sp, 640
                  sll          a6, t3, sp
                  or           s0, t3, s6
                  or           zero, s10, a1
                  srl          tp, s2, t3
                  c.xor        a5, s0
                  c.mv         s8, s5
                  c.srai       a0, 5
                  ori          a7, gp, 1641
                  c.srai       a3, 15
                  c.slli       a2, 20
                  add          s8, s6, a7
                  xori         s7, t2, 1619
                  remu         s2, a2, gp
                  c.srli       a5, 22
                  nop
                  nop
                  c.mv         sp, a5
                  remu         a3, s7, t3
                  c.srai       a3, 4
                  c.or         a5, s1
                  ori          s11, ra, 410
                  add          a7, s9, a5
                  c.addi4spn   a3, sp, 864
                  mul          ra, s4, t4
                  slti         s5, tp, 2000
                  mul          a7, s11, s8
                  slti         s9, s1, -1406
                  c.addi       t5, 23
                  mulhsu       a3, t6, a3
                  srl          s2, s5, a3
                  c.srai       a0, 6
                  c.add        s3, a0
                  c.addi4spn   a5, sp, 880
                  remu         t1, a0, zero
                  auipc        s4, 997068
                  slti         zero, s8, -1076
                  addi         t2, t2, 1194
                  mul          t3, s1, ra
                  xor          a5, s0, gp
                  slti         sp, gp, 1486
                  srl          a6, sp, t3
                  c.srli       s1, 4
                  auipc        a3, 692132
                  c.addi       s7, -1
                  c.addi4spn   a0, sp, 624
                  lui          ra, 794234
                  c.slli       s7, 26
                  slti         t6, s8, 1959
                  srli         s2, t1, 24
                  or           s10, a1, zero
                  c.slli       t6, 2
                  rem          s1, s1, t4
                  c.lui        gp, 23
                  nop
                  sub          s1, a7, gp
                  xor          t2, sp, s1
                  or           tp, s8, s8
                  c.add        s5, s6
                  c.sub        a5, a3
                  c.add        t3, t2
                  remu         zero, tp, zero
                  and          t3, tp, zero
                  slli         t1, a0, 21
                  div          tp, a5, a5
                  xori         a0, t6, 2045
                  c.addi16sp   sp, -16
                  divu         s2, s7, tp
                  slti         t1, t3, 128
                  sub          gp, s0, ra
                  remu         a0, s4, a4
                  sub          a7, a6, t0
                  c.lui        s9, 22
                  slti         s5, s11, -1933
                  slt          s0, t0, t2
                  xor          sp, s0, s0
                  andi         a7, s4, 1503
                  divu         t6, a3, zero
                  remu         a5, s9, a7
                  srl          a7, s1, s9
                  andi         s11, s11, -700
                  c.add        s0, s0
                  xor          s3, a5, t6
                  c.mv         t1, s4
                  c.and        a2, s1
                  addi         t2, a2, 1491
                  srai         t0, t5, 31
                  add          a5, a6, a0
                  add          t6, s9, t5
                  nop
                  mul          ra, s1, s3
                  c.addi4spn   s0, sp, 208
                  c.mv         s9, s9
                  sra          s5, s4, ra
                  c.addi       a2, -1
                  c.lui        a6, 6
                  c.mv         a6, s4
                  lui          zero, 616438
                  mulhsu       ra, s3, t3
                  divu         t5, tp, gp
                  add          a7, s5, tp
                  xor          s11, t1, t6
                  srai         gp, sp, 4
                  mulhu        tp, a0, gp
                  slti         s8, a4, -267
                  mulhu        s7, s10, a4
                  c.slli       s3, 21
                  c.lui        s2, 11
                  add          s8, s0, a2
                  srli         tp, t4, 24
                  c.srli       a5, 8
                  sltiu        zero, s3, -1808
                  slt          s2, a5, a4
                  c.slli       s11, 23
                  mul          s9, s5, t2
                  ori          ra, t3, 604
                  c.addi16sp   sp, 288
                  c.li         t0, 5
                  c.mv         t3, s0
                  c.addi4spn   a5, sp, 992
                  xori         sp, a3, 855
                  mul          a3, t0, t3
                  c.srli       s0, 24
                  divu         s1, t1, s10
                  xor          s9, s4, gp
                  slt          ra, t4, zero
                  and          s11, s9, t0
                  divu         t0, a2, s5
                  mulh         s4, tp, a5
                  c.andi       s1, 0
                  c.xor        s0, s0
                  c.nop
                  sltiu        tp, s1, -1960
                  nop
                  c.mv         s8, a4
                  srli         a7, t5, 21
                  div          t5, s7, zero
                  xori         tp, s1, -742
                  slt          t3, a6, t3
                  c.xor        a5, a5
                  andi         t4, s7, 1133
                  c.lui        s1, 30
                  div          zero, ra, sp
                  c.sub        a2, a5
                  addi         s11, a7, -1591
                  xor          s0, s7, t6
                  slt          t3, a7, s8
                  c.and        a0, s0
                  ori          zero, s7, 445
                  add          s1, zero, s4
                  mulh         t0, a4, gp
                  c.slli       s5, 8
                  mul          zero, s7, t4
                  mulhu        s5, gp, s9
                  c.slli       s1, 31
                  or           s5, a6, a1
                  c.addi4spn   s0, sp, 304
                  srl          s3, s0, s7
                  lui          s1, 48374
                  mul          a5, a0, t2
                  c.and        a3, a1
                  c.add        a3, a6
                  slli         t1, gp, 21
                  slli         zero, s0, 16
                  c.sub        a2, a2
                  sltiu        t3, s2, 1306
                  andi         t2, t4, 1060
                  and          t1, ra, a0
                  sra          a5, a6, a2
                  c.and        a3, a5
                  c.li         ra, 24
                  sltiu        s11, s2, 150
                  c.and        s1, a3
                  sll          t3, s3, a6
                  c.srli       s0, 2
                  add          s9, a3, a6
                  c.srai       a3, 1
                  sra          tp, t0, s6
                  nop
                  c.or         s0, a5
                  slli         a2, s11, 31
                  mul          t4, s8, a6
                  sltiu        s5, s5, -1434
                  c.li         s1, 11
                  and          a3, s6, s7
                  mulh         zero, t2, s7
                  c.slli       s3, 11
                  andi         gp, t4, 1107
                  c.add        s9, t6
                  c.lui        t5, 7
                  c.sub        a0, a2
                  mulh         s8, sp, s0
                  remu         t6, a3, a2
                  srli         a0, s5, 24
                  sltu         s4, a1, t3
                  andi         a0, s9, -1159
                  or           t4, a6, s2
                  mulh         a2, a7, a6
                  xor          t4, s4, s4
                  addi         a3, s3, -193
                  xor          s9, a0, t4
                  slt          a3, zero, s5
                  srli         s4, zero, 30
                  auipc        t5, 284147
                  rem          sp, gp, a5
                  c.andi       a0, 30
                  slti         t3, gp, 717
                  c.srai       a5, 15
                  nop
                  slti         s11, s9, -895
                  andi         s1, s3, -1861
                  c.slli       a7, 2
                  c.addi       a7, -1
                  c.slli       s2, 6
                  xor          t6, s3, s7
                  c.addi4spn   a2, sp, 800
                  slli         t6, tp, 17
                  addi         tp, tp, -371
                  nop
                  remu         s9, t5, s10
                  mulh         s7, t1, s3
                  xori         a2, a7, 1602
                  and          a3, a3, s6
                  xori         t4, t0, 1636
                  and          t5, s10, t2
                  sra          s10, t3, a3
                  mulh         s1, s5, a5
                  c.mv         a6, s2
                  and          a6, s3, s5
                  add          t6, a7, s11
                  and          t3, a0, s8
                  divu         s3, a0, sp
                  mulhu        gp, s5, s1
                  sltu         s7, zero, zero
                  slti         t5, s9, -1930
                  nop
                  addi         s8, s1, -387
                  c.mv         t2, t6
                  nop
                  c.or         a2, a4
                  c.sub        a0, a4
                  mulhsu       a6, s2, a7
                  c.mv         s4, t5
                  nop
                  mulhsu       s10, t3, a0
                  auipc        tp, 986643
                  c.xor        a0, s1
                  nop
                  xor          s4, s6, s11
                  slti         s2, a0, 605
                  mulhsu       t4, s7, s5
                  c.slli       s11, 10
                  or           s1, s2, s5
                  add          s11, s5, a7
                  sll          s5, s0, t0
                  addi         s7, t5, -1508
                  rem          a7, a0, s10
                  c.nop
                  sltu         t2, s2, s3
                  mulhu        a0, s7, s2
                  div          tp, s0, t1
                  slli         t3, s0, 10
                  c.and        s1, a5
                  andi         a0, s8, -1020
                  ori          t1, s3, 472
                  c.lui        s9, 15
                  c.or         s1, a3
                  xor          s2, s5, s2
                  c.srli       s0, 8
                  sra          zero, t0, s1
                  c.xor        a3, a4
                  div          s7, s11, a1
                  mulh         t1, ra, gp
                  c.srli       a3, 21
                  slli         a6, a2, 26
                  xori         s4, s6, 1550
                  or           s4, s9, s0
                  c.andi       s1, 4
                  nop
                  mulhsu       s11, a4, t1
                  slli         zero, s3, 4
                  mulhsu       t5, s10, s0
                  c.slli       t4, 13
                  c.mv         t5, s11
                  c.mv         s5, sp
                  and          t3, zero, sp
                  srli         t6, a2, 25
                  mulh         gp, s9, t5
                  nop
                  c.nop
                  divu         s8, s0, s9
                  nop
                  rem          s9, t5, gp
                  c.mv         t4, t1
                  sub          s5, t3, t0
                  auipc        a3, 907420
                  c.add        s1, s5
                  ori          t6, s8, -1978
                  c.addi16sp   sp, 432
                  sltiu        s10, t4, 126
                  c.xor        s0, a5
                  or           ra, s3, a5
                  c.lui        s11, 22
                  c.xor        a0, s0
                  c.srai       a5, 15
                  sra          sp, t1, a4
                  c.add        tp, s3
                  c.slli       a3, 2
                  c.and        a2, a4
                  c.andi       a2, 9
                  c.and        s1, s1
                  lui          t1, 994174
                  c.addi       t1, -1
                  mul          a7, a1, s10
                  c.and        a3, a1
                  srli         t0, s6, 29
                  c.addi4spn   a0, sp, 528
                  c.addi16sp   sp, -16
                  c.addi       s4, 8
                  c.or         a2, a3
                  c.slli       a2, 18
                  c.xor        a2, a0
                  add          s7, a2, t0
                  sub          gp, t6, a7
                  divu         t4, sp, s0
                  sltu         t3, s11, a0
                  lui          ra, 494415
                  c.or         s0, a0
                  sll          s4, sp, s1
                  slt          gp, a0, sp
                  sll          a3, a1, a7
                  mulh         s5, a3, s3
                  andi         t6, t2, -789
                  c.srai       s0, 11
                  c.andi       a2, -1
                  xori         zero, t5, 1193
                  c.srli       s1, 15
                  xor          a0, sp, a5
                  mulh         a0, t5, a5
                  slti         a5, t5, 1554
                  c.and        s1, a5
                  and          a5, t2, s10
                  lui          tp, 396688
                  nop
                  sra          ra, a0, t5
                  ori          t2, s6, -619
                  c.or         a5, a3
                  mul          s11, s7, a5
                  sll          t2, s4, t5
                  slti         t1, t3, 369
                  slt          tp, s2, s11
                  sll          t4, a5, t6
                  auipc        tp, 866958
                  xor          a5, s2, t3
                  c.addi       a6, 17
                  divu         s2, s9, a1
                  sub          s4, t0, s9
                  c.srli       a2, 11
                  sltu         a2, s4, s11
                  add          gp, s5, t3
                  add          ra, t1, a2
                  c.slli       gp, 6
                  slti         sp, s1, 675
                  sll          a5, sp, t0
                  c.sub        s0, a2
                  c.add        s2, s8
                  slli         sp, gp, 2
                  lui          ra, 392552
                  srai         s11, a1, 9
                  slt          ra, s6, a1
                  remu         a3, s3, s0
                  c.srai       a5, 21
                  sltu         a7, ra, a4
                  and          a0, s4, a6
                  c.mv         s5, t3
                  or           t1, s8, s1
                  or           s5, ra, a1
                  c.lui        s8, 21
                  mulhu        t4, s9, sp
                  srli         t5, gp, 21
                  rem          t4, s7, tp
                  xor          s0, s3, tp
                  sub          sp, a1, t0
                  c.sub        a0, a2
                  remu         t4, s8, t3
                  mulhsu       t6, ra, s6
                  c.srli       a5, 7
                  auipc        s0, 413655
                  c.andi       a5, 18
                  srl          s4, s8, a3
                  c.srai       a0, 19
                  slli         a7, sp, 14
                  ori          ra, s10, 255
                  c.srli       s0, 27
                  mulhsu       t1, a7, s3
                  c.lui        s4, 26
                  remu         s7, s4, zero
                  add          s7, t2, t5
                  auipc        s0, 409067
                  mulhu        s4, t5, s4
                  sub          a3, s4, a4
                  sltu         zero, a3, s4
                  c.addi4spn   s1, sp, 32
                  mulhu        a2, t2, a4
                  srl          t0, a5, gp
                  c.andi       s1, 1
                  c.li         s2, 24
                  remu         s4, t1, a0
                  add          s7, t0, s10
                  c.nop
                  slli         zero, t5, 27
                  c.addi4spn   a5, sp, 400
                  c.addi4spn   a0, sp, 976
                  c.lui        s5, 10
                  c.addi16sp   sp, -16
                  c.xor        a5, a1
                  auipc        s5, 277065
                  sltiu        s11, a3, -1465
                  divu         t2, gp, ra
                  div          gp, t6, s5
                  rem          s0, t6, a2
                  mulhu        tp, a5, s10
                  c.slli       a3, 16
                  c.srli       a0, 10
                  srai         a6, t4, 31
                  c.addi4spn   s1, sp, 992
                  sra          s2, t3, a2
                  slt          a5, s7, s2
                  div          a5, s6, t2
                  c.xor        a0, a3
                  or           tp, a1, s5
                  c.addi16sp   sp, -16
                  slti         a2, t6, -1355
                  sltu         s7, s5, s5
                  srl          s4, t6, s10
                  and          t0, a4, s0
                  c.xor        a5, a2
                  c.addi4spn   a0, sp, 208
                  c.nop
                  c.add        gp, s10
                  sra          tp, a4, s8
                  mulhsu       t4, t2, s10
                  slt          s3, s6, a5
                  mulh         s1, t5, t3
                  sltiu        s11, t4, -1130
                  c.addi4spn   s0, sp, 704
                  c.srli       a3, 24
                  sra          s10, s3, s11
                  c.li         s8, 11
                  c.srai       a2, 5
                  slli         s2, t1, 28
                  nop
                  ori          t1, s0, -1998
                  c.nop
                  c.lui        a2, 29
                  ori          tp, ra, 464
                  c.addi       t4, -1
                  c.or         s0, a5
                  srl          a7, s1, zero
                  c.mv         s2, t2
                  c.addi4spn   a2, sp, 448
                  sll          t4, t3, a3
                  c.and        s0, a1
                  and          a5, t2, s0
                  xori         sp, tp, -691
                  xor          t6, a6, s4
                  srl          s8, zero, sp
                  and          sp, s0, t1
                  c.mv         ra, s10
                  c.addi4spn   s1, sp, 736
                  c.li         s11, -1
                  divu         t2, s8, s6
                  sra          s7, a1, a5
                  c.or         s0, a5
                  c.and        a0, a3
                  srai         s5, tp, 26
                  c.or         a3, s0
                  c.srai       s0, 11
                  sltu         t4, s2, s2
                  add          t6, t5, t5
                  or           a3, s5, a1
                  andi         t2, s0, 1368
                  c.and        a5, a4
                  remu         s9, a0, t4
                  xori         t4, t0, -1919
                  c.slli       s4, 27
                  lui          a6, 979256
                  c.addi4spn   a5, sp, 928
                  c.srli       s0, 15
                  mulhu        s0, s0, s3
                  xor          t3, ra, t2
                  c.addi4spn   s1, sp, 80
                  addi         s0, s4, -1185
                  sltu         t5, t3, a7
                  c.xor        a0, s0
                  c.or         s0, a4
                  slli         s3, a3, 5
                  sll          s7, zero, t6
                  or           ra, a7, s11
                  mulh         s2, s5, a2
                  or           a2, a3, t3
                  ori          s3, sp, -886
                  remu         a5, s7, a3
                  divu         t5, gp, s8
                  c.andi       a5, 31
                  c.li         s7, 2
                  add          t5, s6, ra
                  mulhu        s2, tp, t2
                  c.or         a3, a2
                  auipc        s8, 118213
                  mul          s0, s0, s10
                  sra          s10, zero, a0
                  c.srli       a2, 13
                  xor          t1, s3, ra
                  c.srli       a2, 7
                  c.srai       a0, 15
                  mulh         t3, s5, s1
                  mulhsu       t0, tp, a5
                  ori          a6, a0, -895
                  c.srli       a0, 18
                  c.or         a2, a3
                  remu         t3, a1, tp
                  c.addi4spn   a0, sp, 352
                  c.and        s1, a3
                  sltiu        s5, s1, -405
                  mul          s3, a3, a6
                  srli         sp, t0, 24
                  mulhu        s3, a4, s3
                  and          t0, s10, gp
                  c.srai       a5, 4
                  xori         t6, s3, 1232
                  srl          a0, a3, s1
                  c.srli       a3, 20
                  c.andi       s1, 1
                  c.lui        t1, 14
                  c.slli       tp, 8
                  ori          s0, ra, 1427
                  sra          s4, s8, t3
                  addi         s5, a1, -1715
                  slti         a6, tp, -1673
                  mulhsu       s9, t3, gp
                  nop
                  add          a0, zero, t6
                  slt          t3, gp, a1
                  xori         t3, t6, 1763
                  lui          a3, 625822
                  slli         t4, t5, 20
                  c.slli       s1, 30
                  c.nop
                  sub          s3, zero, s11
                  c.and        a5, a3
                  sra          a7, t6, s0
                  slti         s9, t2, -963
                  c.srli       a2, 14
                  slli         sp, sp, 25
                  lui          a6, 424113
                  mulhsu       s4, sp, t0
                  auipc        t3, 546603
                  mulhu        a0, s6, gp
                  c.addi16sp   sp, 144
                  srli         t2, t0, 25
                  c.and        a2, s1
                  andi         sp, ra, -100
                  c.mv         s8, sp
                  c.slli       t6, 26
                  or           s3, s2, s11
                  addi         sp, s6, 1385
                  srl          s4, s8, t0
                  sltiu        t5, sp, -1665
                  mul          a2, t0, t4
                  c.li         a6, 13
                  c.add        s10, s11
                  remu         s3, a6, a4
                  sltiu        t4, a4, -1944
                  mulhsu       t2, s8, a6
                  sll          tp, t2, t5
                  sltiu        zero, s2, -1437
                  auipc        zero, 694179
                  slli         t2, a5, 7
                  slt          s3, zero, s4
                  and          tp, t1, s0
                  c.li         a3, 10
                  c.addi       s3, 4
                  c.lui        a6, 2
                  c.xor        a3, a3
                  xor          t4, s6, a0
                  add          sp, s3, t3
                  c.addi16sp   sp, 272
                  c.nop
                  mul          s4, a1, t2
                  ori          t4, s3, -413
                  add          ra, a0, s9
                  c.li         s0, 26
                  xori         t3, a6, 325
                  c.add        a6, t5
                  slt          a3, s1, t6
                  addi         s3, t3, -271
                  sra          t4, s11, t4
                  add          t5, s9, a3
                  sub          tp, zero, a1
                  sra          a3, t2, t5
                  sra          s11, a7, s0
                  mulhsu       a3, t1, a1
                  div          s3, a3, s2
                  div          a0, t1, zero
                  c.nop
                  c.slli       s0, 18
                  andi         t4, a5, 398
                  c.and        s0, a1
                  remu         t2, s1, s7
                  mulh         s0, s1, a0
                  rem          tp, tp, gp
                  c.add        t1, s11
                  slti         s10, s1, -357
                  c.srai       s1, 29
                  nop
                  lui          s10, 913457
                  c.srai       s1, 4
                  c.addi4spn   a2, sp, 224
                  ori          s9, s7, -292
                  auipc        zero, 1024223
                  andi         s0, tp, 1301
                  mulhsu       a2, a7, a4
                  mulhsu       a6, t2, s9
                  c.sub        a0, a2
                  or           a5, gp, s5
                  lui          s8, 272386
                  c.addi4spn   s0, sp, 336
                  divu         s10, s4, t3
                  sltiu        ra, s6, -659
                  addi         t6, a7, -1740
                  c.nop
                  srai         ra, s5, 18
                  c.add        t4, a7
                  c.or         a5, a1
                  xor          a7, a1, a7
                  sltu         t4, t1, t5
                  c.srai       s1, 10
                  sltiu        a6, s1, -369
                  c.andi       a3, -1
                  c.slli       t1, 11
                  c.srai       a5, 31
                  c.sub        s0, a5
                  c.and        a0, a3
                  add          t5, s10, s9
                  c.mv         s4, t3
                  c.addi4spn   a0, sp, 816
                  c.sub        a5, s1
                  mulhsu       s4, t1, s7
                  and          s11, a7, a3
                  c.addi4spn   a5, sp, 560
                  sltu         s11, zero, a1
                  srai         t2, a6, 1
                  andi         t2, s3, 1820
                  c.addi16sp   sp, -16
                  c.addi       a0, -1
                  srai         s5, s9, 0
                  sltiu        a5, a2, -81
                  sltiu        s9, s10, 45
                  div          s11, sp, a7
                  auipc        a0, 458884
                  sub          ra, s5, a1
                  c.andi       s0, 21
                  xor          a3, ra, t1
                  remu         a2, t5, s1
                  c.or         a5, a5
                  srl          a7, zero, s8
                  c.sub        a2, a0
                  sra          a2, t6, s7
                  srai         a5, a2, 30
                  remu         s4, t2, s6
                  slli         a0, s7, 0
                  xor          t3, s3, s1
                  c.or         s1, a3
                  mulhsu       s1, s11, a1
                  slti         a3, t0, -1678
                  mulh         s7, s2, gp
                  c.lui        t0, 20
                  andi         s11, sp, 1421
                  c.xor        a0, s1
                  c.srai       s0, 17
                  c.srli       a2, 3
                  auipc        s0, 76254
                  srl          tp, gp, t3
                  sltiu        s10, a3, -698
                  c.mv         gp, a1
                  remu         a3, t1, s2
                  andi         s5, t5, 1641
                  c.srai       s0, 11
                  sltu         a2, s0, s0
                  c.addi4spn   a0, sp, 432
                  c.nop
                  add          s3, a1, s9
                  c.sub        a5, s1
                  mulhu        s10, s7, zero
                  c.srli       a2, 5
                  slti         s11, s5, -1658
                  sub          a7, t4, t6
                  c.srai       a0, 18
                  c.xor        s1, a5
                  c.addi       s9, -1
                  srli         a7, s11, 15
                  mulh         s8, s11, a5
                  c.addi4spn   s0, sp, 80
                  divu         a6, s7, t2
                  c.li         s9, -1
                  slli         zero, sp, 7
                  ori          s0, t3, -1848
                  or           s1, tp, s4
                  c.add        ra, s8
                  c.srli       s0, 4
                  andi         a2, ra, -283
                  xori         a5, t4, -1509
                  c.and        a2, a4
                  c.andi       a5, -1
                  xori         a0, a1, 440
                  xor          s3, a3, a7
                  c.slli       sp, 19
                  c.addi16sp   sp, -16
                  or           t3, t6, a0
                  c.nop
                  sltu         s3, s7, t2
                  slli         ra, a0, 30
                  c.or         a0, a4
                  ori          tp, a7, 1983
                  lui          s8, 608750
                  sub          t5, t3, s9
                  and          t0, sp, t5
                  srli         s8, t6, 16
                  mulh         t5, t5, t2
                  c.nop
                  mul          s9, a7, t5
                  sll          a6, s11, a6
                  sltiu        a2, a7, 223
                  c.slli       s1, 12
                  lui          sp, 494270
                  c.addi16sp   sp, 368
                  c.andi       a5, -1
                  srli         s11, t3, 7
                  slti         t0, s4, -2029
                  ori          a6, sp, -454
                  srl          s5, a4, s2
                  sll          a6, a6, a6
                  c.mv         a3, a4
                  lui          s10, 576264
                  c.xor        a5, a3
                  c.add        s4, a2
                  c.xor        s0, s0
                  auipc        a3, 865632
                  sra          a0, a4, t4
                  c.or         a5, s0
                  sub          t4, s0, s10
                  ori          a7, t3, -1152
                  lui          t2, 389143
                  c.li         s9, -1
                  c.mv         t3, sp
                  remu         zero, a5, s8
                  sub          a0, a1, a1
                  xor          s11, ra, a7
                  sltiu        a2, s0, -282
                  c.sub        a0, a5
                  c.addi4spn   a2, sp, 112
                  andi         s0, t3, -658
                  and          s10, tp, t3
                  srl          a2, a4, t0
                  c.lui        s5, 5
                  c.lui        s2, 6
                  ori          a7, a3, -1943
                  c.srli       s0, 17
                  or           t5, t2, s0
                  xori         t1, s10, 1842
                  sltu         sp, ra, t6
                  c.lui        s10, 22
                  div          s11, s2, a7
                  sra          a5, a1, a1
                  c.srli       s1, 21
                  mulhu        s1, s3, a4
                  srli         s10, a1, 30
                  slti         a5, a0, -1768
                  c.addi4spn   a5, sp, 144
                  c.lui        s3, 4
                  srai         s4, s9, 24
                  xor          t0, t6, s4
                  c.srai       a0, 23
                  slti         s2, sp, -1100
                  srli         s8, t5, 8
                  sll          sp, t4, sp
                  nop
                  c.addi       a6, 14
                  mulhsu       t0, s2, s10
                  mulh         t2, s2, s10
                  sll          t0, s9, s8
                  c.addi       t0, -1
                  div          s0, s9, s1
                  srl          s0, a5, t2
                  addi         t5, a1, 654
                  c.addi       a6, 22
                  c.srli       a3, 3
                  c.sub        a2, a0
                  c.xor        a5, a5
                  c.addi16sp   sp, -16
                  lui          t3, 499678
                  remu         t5, t6, t6
                  srai         a7, t0, 5
                  c.and        a3, a2
                  ori          s8, t1, 170
                  slli         s8, a4, 3
                  mulh         s2, s6, a0
                  c.srai       s1, 29
                  auipc        s2, 154433
                  or           t3, s10, a1
                  c.srai       a0, 7
                  andi         ra, s1, -1543
                  c.srai       a3, 24
                  nop
                  sltu         t3, s1, t4
                  slt          s9, s8, ra
                  srai         s8, s7, 15
                  and          s7, t5, s7
                  xori         a7, s11, 1025
                  div          t2, a2, t2
                  c.addi4spn   s0, sp, 912
                  nop
                  c.mv         t0, s4
                  sra          s7, s5, s10
                  mulhsu       tp, s7, s5
                  c.andi       a5, 20
                  slli         zero, s2, 3
                  srl          t6, a6, t3
                  auipc        a6, 672475
                  addi         s0, t2, -247
                  c.addi16sp   sp, 272
                  sub          s1, s2, ra
                  sub          s0, t2, s7
                  and          zero, s1, a2
                  c.nop
                  c.slli       gp, 31
                  srl          s5, s5, s6
                  c.add        s3, sp
                  ori          s0, gp, -1950
                  and          s2, a6, a6
                  andi         s3, zero, 390
                  div          a3, a3, zero
                  div          a0, s4, s10
                  c.addi4spn   s0, sp, 208
                  lui          s8, 45176
                  c.srli       a0, 9
                  c.add        gp, tp
                  div          t0, s6, a1
                  rem          ra, s4, a2
                  add          a0, t0, a6
                  slti         t5, t5, 643
                  and          s0, s9, s10
                  c.slli       s9, 21
                  c.addi16sp   sp, -16
                  xori         tp, t6, 284
                  c.sub        a2, a0
                  c.xor        a0, a2
                  addi         sp, t6, -631
                  c.xor        a2, a2
                  mulhsu       ra, zero, a1
                  c.xor        a0, a0
                  ori          t6, t6, -1292
                  c.srai       a5, 2
                  c.li         t1, -1
                  rem          t5, gp, s2
                  mulh         s11, s9, sp
                  c.xor        a5, s0
                  or           s1, s7, t0
                  lui          ra, 677976
                  or           a2, s1, tp
                  lui          s2, 318667
                  mul          ra, a4, a0
                  remu         a7, zero, s8
                  mulhsu       ra, a4, s6
                  c.or         a2, a2
                  c.lui        a5, 12
                  xor          sp, a1, s11
                  rem          t3, t5, t5
                  c.slli       s1, 8
                  c.or         a0, a0
                  c.and        a2, a0
                  c.srai       s1, 22
                  c.addi16sp   sp, 368
                  sub          s5, t3, ra
                  xor          zero, a1, s10
                  srli         sp, t6, 27
                  c.mv         s10, ra
                  sub          zero, s5, sp
                  c.xor        s0, s0
                  rem          s5, t4, a4
                  div          a2, s6, t4
                  c.addi16sp   sp, -16
                  c.addi16sp   sp, -16
                  c.nop
                  sltiu        tp, t6, 410
                  slti         t4, a7, -1462
                  sub          a5, s8, t5
                  auipc        s9, 181935
                  add          t4, t4, s9
                  rem          s3, s7, t6
                  slti         s10, sp, 5
                  lui          t0, 155058
                  lui          a3, 860835
                  c.add        s10, s8
                  srai         a2, zero, 2
                  nop
                  c.srai       a3, 20
                  c.addi       s9, -1
                  div          s0, s8, s11
                  mulhu        s5, s3, a4
                  c.addi4spn   s1, sp, 880
                  srl          a2, s3, s6
                  c.add        t1, a0
                  andi         a0, gp, -1833
                  lui          t5, 743789
                  or           s8, s10, t1
                  mul          t5, s3, sp
                  c.addi       a7, -1
                  xor          t5, tp, t1
                  c.mv         sp, ra
                  sra          t1, a4, a5
                  c.srli       s0, 20
                  c.srli       s0, 4
                  addi         t1, s3, 532
                  or           zero, a5, s7
                  c.slli       s4, 9
                  c.mv         t2, s6
                  addi         gp, s9, 1369
                  xori         a3, s0, -338
                  c.mv         s3, sp
                  srli         s5, a1, 18
                  c.lui        a7, 23
                  c.addi4spn   a3, sp, 944
                  auipc        s3, 332672
                  add          t1, a5, a6
                  mulhu        t0, a4, s7
                  mul          tp, s10, s2
                  c.lui        ra, 26
                  c.add        s8, s1
                  srli         s4, t6, 11
                  div          t4, gp, s6
                  slt          t1, t6, sp
                  or           s1, t5, ra
                  mulhsu       tp, a0, s7
                  mul          a2, s9, t5
                  nop
                  ori          a2, s5, -1093
                  rem          s4, a6, s10
                  c.srai       s1, 25
                  slt          ra, s5, s9
                  slli         ra, gp, 20
                  sltiu        t5, t1, -799
                  sltu         s2, t1, a4
                  and          t6, s7, s3
                  srai         a7, t1, 19
                  slt          s0, s8, zero
                  mul          s9, s1, zero
                  srli         tp, t1, 5
                  sltu         s9, a2, s6
                  c.or         s0, a4
                  sra          zero, s1, ra
                  sra          a3, s5, t6
                  sltiu        sp, t4, -585
                  or           zero, t6, a2
                  c.srli       a3, 7
                  c.addi4spn   a5, sp, 736
                  remu         a7, s3, a7
                  divu         s9, s0, t5
                  slt          t5, s2, s6
                  xori         s5, a1, -1871
                  sub          s10, a1, a2
                  sub          zero, s9, t0
                  c.nop
                  mul          s10, s11, t4
                  c.li         s0, 31
                  andi         t4, s8, -1001
                  ori          zero, t3, 440
                  c.nop
                  and          tp, s0, s3
                  mul          s4, zero, a7
                  sltu         s1, a4, s8
                  ori          s9, a5, 1178
                  add          gp, sp, a2
                  sll          t2, s5, gp
                  andi         a0, ra, 2044
                  slti         tp, s0, 348
                  srli         s0, t4, 19
                  or           s0, a2, s5
                  c.srli       s1, 26
                  srai         a0, a2, 26
                  nop
                  lui          a2, 557575
                  srli         a6, s4, 18
                  sub          t3, t6, a5
                  and          s5, t0, s6
                  slli         s0, a4, 18
                  xori         gp, a0, 879
                  srl          t4, s7, a1
                  srl          s0, a6, ra
                  c.addi       s8, 3
                  add          s11, a5, a2
                  xor          a5, s9, s3
                  remu         s11, s5, a6
                  c.srai       s0, 3
                  remu         a6, t2, s3
                  c.lui        ra, 9
                  xori         s8, tp, 620
                  sll          sp, t0, s4
                  c.slli       sp, 1
                  c.sub        a3, s1
                  slli         s0, s5, 7
                  srli         s9, s2, 2
                  lui          t3, 105823
                  remu         zero, a4, s0
                  c.li         s1, 16
                  mulh         t0, s7, t4
                  mul          t5, s9, tp
                  c.addi16sp   sp, -16
                  nop
                  slli         s10, t6, 4
                  c.addi       ra, -1
                  sltiu        s11, tp, -1066
                  c.slli       sp, 29
                  srli         t4, zero, 22
                  andi         a0, s10, 859
                  mulhu        zero, t1, sp
                  c.sub        s1, s0
                  c.slli       s5, 27
                  xor          s10, a0, sp
                  c.andi       a2, -1
                  lui          a7, 590034
                  slti         a7, t0, 1865
                  c.or         s0, a5
                  c.lui        t4, 30
                  c.addi       s10, -1
                  auipc        ra, 365075
                  rem          s1, a4, sp
                  auipc        s3, 407657
                  lui          s7, 180704
                  andi         a7, a3, 188
                  mulhsu       a2, a1, a6
                  c.srli       s0, 25
                  ori          s2, s10, -1691
                  srli         a6, s2, 1
                  lui          s4, 965348
                  divu         a3, a3, t4
                  c.srli       s0, 3
                  andi         s3, s2, -39
                  c.slli       s3, 26
                  c.sub        a2, a3
                  rem          s0, s10, s2
                  mul          a3, t3, s10
                  ori          s10, a4, -1598
                  slt          s1, t2, s10
                  divu         s10, zero, a3
                  andi         s11, a4, -1771
                  c.addi4spn   a5, sp, 416
                  c.xor        a2, s1
                  or           t4, s11, t1
                  mulhu        s7, s1, a5
                  mulh         a6, s11, s10
                  c.addi       s4, -1
                  srai         s0, s8, 29
                  c.mv         s7, t4
                  rem          t5, a3, s7
                  sltiu        s7, t2, -1475
                  rem          s4, s7, t4
                  c.slli       s8, 27
                  c.add        s8, t1
                  remu         s11, s0, s4
                  auipc        a7, 110780
                  c.addi       ra, -1
                  c.lui        a3, 18
                  srl          s9, s8, zero
                  mul          t1, s5, a2
                  andi         t4, a2, -1561
                  srli         t3, tp, 18
                  srli         s9, t3, 26
                  c.li         tp, -1
                  sra          a2, a2, s4
                  xor          t5, sp, a5
                  c.srli       a2, 27
                  sltu         t4, a0, s3
                  slli         tp, s7, 14
                  xori         s1, t3, 875
                  sra          s8, s6, t5
                  c.nop
                  slti         t2, s1, -1713
                  addi         t3, a4, 553
                  mulh         zero, ra, a0
                  sra          s3, s7, a2
                  add          a6, s1, s0
                  sltu         s10, t5, t1
                  c.xor        a3, s0
                  or           s4, t2, s3
                  c.addi4spn   a5, sp, 864
                  srl          t1, a1, gp
                  c.addi4spn   s0, sp, 320
                  xori         t4, ra, -1678
                  c.li         s11, -1
                  c.li         s10, 24
                  lui          t0, 403533
                  c.and        a3, s1
                  add          tp, zero, s9
                  andi         s10, s8, 560
                  ori          s1, s6, -1972
                  srli         tp, s2, 2
                  divu         t5, a1, s3
                  c.srai       a3, 2
                  sub          a0, t6, t5
                  c.andi       a2, -1
                  c.or         a0, a1
                  remu         s5, s11, a0
                  sltu         s11, ra, a5
                  sltiu        s1, s4, 488
                  slt          a5, t1, s3
                  mulhu        t3, a4, gp
                  c.srai       s0, 18
                  slli         t1, s10, 18
                  divu         t0, a0, s11
                  addi         sp, s8, -692
                  mulhu        t4, a7, t4
                  c.li         t0, 17
                  c.nop
                  c.or         a5, s0
                  mulhsu       a5, a2, s6
                  add          s8, tp, s1
                  xori         s1, t5, 12
                  div          t6, gp, t2
                  c.and        s1, a4
                  c.mv         s9, s1
                  c.addi       ra, -1
                  ori          t2, t5, 1352
                  addi         a2, a5, 881
                  c.addi       s9, -1
                  lui          s2, 955200
                  auipc        a6, 1021066
                  srai         t2, a6, 2
                  andi         s4, s9, -1002
                  c.sub        a5, a3
                  mul          s3, s8, sp
                  nop
                  c.and        a5, s0
                  addi         sp, a3, 1680
                  auipc        s4, 271176
                  c.nop
                  c.lui        s5, 23
                  c.li         tp, 31
                  c.li         t4, 20
                  sra          s4, s9, sp
                  lui          s7, 778925
                  and          s5, ra, s5
                  or           zero, a3, tp
                  addi         zero, s1, -1504
                  c.slli       t0, 28
                  auipc        s1, 655586
                  add          s2, t1, s8
                  mulhsu       ra, s7, a1
                  sltu         t5, a7, a4
                  c.nop
                  sltiu        zero, ra, 493
                  slti         a2, s11, -142
                  srl          a6, s9, s8
                  c.sub        s0, a0
                  c.addi16sp   sp, -16
                  srai         a0, a0, 28
                  c.slli       t0, 6
                  sub          t6, a1, zero
                  rem          a2, t6, a2
                  srai         s4, s3, 20
                  c.andi       a5, -1
                  lui          s4, 138051
                  andi         t5, sp, 2017
                  srai         a3, s0, 26
                  c.sub        a2, s1
                  lui          s2, 740440
                  sub          s0, t4, a0
                  c.nop
                  add          a3, a7, ra
                  c.add        s8, s4
                  lui          s11, 586965
                  xor          sp, s3, t1
                  sll          t5, s11, s4
                  c.srai       s1, 10
                  c.and        s0, a3
                  xor          s9, t0, s1
                  add          s8, gp, a5
                  c.addi       s7, -1
                  slti         s2, t1, 574
                  auipc        t5, 1047700
                  sltiu        t5, s1, -1773
                  sra          a5, s3, s8
                  divu         gp, s10, t1
                  andi         s0, s3, 228
                  divu         a7, s10, t0
                  c.addi4spn   a2, sp, 528
                  sltu         tp, a5, tp
                  c.addi       a3, -1
                  mul          t5, s6, tp
                  slli         t1, a1, 4
                  c.or         s0, s1
                  xor          s3, a5, t4
                  divu         zero, a0, t3
                  divu         s11, a2, s8
                  c.add        a5, s8
                  sltiu        t1, ra, -974
                  andi         s7, t1, -1153
                  slti         s0, a6, -1446
                  srai         s1, t3, 21
                  lui          s11, 972821
                  c.lui        s2, 31
                  c.andi       a3, 12
                  sub          sp, a6, gp
                  auipc        tp, 219270
                  srl          tp, s11, s2
                  c.or         a0, a2
                  addi         s9, t6, -1830
                  srli         s4, a7, 28
                  c.add        sp, a5
                  c.nop
                  mulh         a2, zero, s11
                  c.addi       t6, 29
                  c.li         s10, 8
                  slti         a6, s11, -1068
                  slti         s2, s9, -1526
                  xor          a7, s2, s0
                  c.addi16sp   sp, 16
                  add          t5, tp, s4
                  mulhu        sp, a5, gp
                  sub          s3, a4, s3
                  c.lui        a5, 27
                  mulhu        s8, t5, s10
                  c.add        a5, t5
                  c.addi16sp   sp, -16
                  slli         a3, zero, 20
                  c.xor        a0, s1
                  c.li         tp, 13
                  addi         s7, a0, -399
                  c.lui        s9, 4
                  sub          s4, a2, t4
                  c.addi4spn   a5, sp, 64
                  sra          a6, a6, sp
                  sub          t5, sp, t6
                  nop
                  c.and        s0, a1
                  c.sub        a2, a4
                  c.slli       s11, 29
                  c.andi       s1, -1
                  sltiu        gp, a6, -1248
                  c.li         s7, 15
                  sll          a2, t2, a3
                  mul          a7, a6, ra
                  sra          a5, t5, s11
                  and          a0, t6, a1
                  srli         s5, a4, 25
                  c.add        a3, a7
                  xori         a7, t0, -1605
                  c.slli       a5, 22
                  mulhsu       a2, s6, a1
                  c.or         a2, a2
                  mulhu        t6, s10, s1
                  c.mv         s7, t2
                  slli         t0, a7, 18
                  slti         t6, s2, -1984
                  auipc        a5, 953326
                  srli         s10, ra, 15
                  remu         s4, tp, s4
                  and          s3, t1, s8
                  lui          s8, 551180
                  c.addi16sp   sp, 16
                  mulhsu       t5, a6, t4
                  sub          s3, t5, t0
                  c.xor        a0, s1
                  slli         s2, s11, 16
                  c.addi4spn   a2, sp, 80
                  div          t0, t4, a3
                  c.slli       a5, 31
                  c.andi       a2, -1
                  slti         s8, s9, 98
                  sll          a0, s1, s10
                  mul          a2, s2, t3
                  srl          s7, ra, s4
                  addi         t5, s10, -222
                  ori          a0, a7, 460
                  sll          ra, a0, a4
                  srai         t6, s5, 7
                  xori         a5, s3, 1505
                  divu         a2, s2, a0
                  xor          ra, t2, s9
                  and          t5, a2, t2
                  li           s0, 0x80000000 #start riscv_int_numeric_corner_stream_9
                  li           s4, 0x0
                  li           s3, 0x0
                  li           a5, 0xffffffff
                  li           t5, 0x0
                  li           s2, 0x80000000
                  li           s10, 0xffffffff
                  li           t0, 0xffffffff
                  li           s11, 0x0
                  li           s1, 0x80000000
                  mulhu        s3, t0, s2
                  mul          s10, s2, t5
                  addi         s4, s1, 1060
                  nop
                  nop
                  lui          s10, 11967
                  addi         t5, s10, -803
                  mulhsu       s3, s11, s3
                  sub          s11, s4, s10
                  nop
                  mul          s0, s10, t5
                  remu         s1, s3, s3
                  add          s2, s3, s4
                  auipc        s1, 974524
                  mul          a5, s0, s0
                  mulhu        t0, s0, s1
                  mul          s4, s4, s2
                  sub          s2, a5, s1
                  addi         t5, s3, -1253
                  sub          s1, t0, t5
                  mulh         a5, s0, t0
                  mulh         t0, s10, s0
                  auipc        s3, 439030
                  nop
                  mul          s3, s0, t5
                  divu         s11, s2, s10
                  auipc        a5, 327327
                  sub          t5, s1, s3 #end riscv_int_numeric_corner_stream_9
                  div          zero, sp, t2
                  andi         s11, a6, 499
                  mulhsu       s4, a2, zero
                  sra          t3, t0, a2
                  nop
                  c.srai       a5, 5
                  ori          s3, t5, -981
                  andi         tp, t0, -1773
                  c.addi4spn   a5, sp, 608
                  mulhu        a7, sp, a6
                  c.andi       s0, -1
                  sra          s2, a7, s9
                  c.andi       a5, 10
                  sll          s3, tp, s6
                  nop
                  srli         t6, t4, 9
                  auipc        s2, 58656
                  ori          a6, t6, 1377
                  sltu         zero, s9, t3
                  c.addi4spn   a0, sp, 432
                  and          s1, s6, s4
                  xor          s11, a3, zero
                  c.addi4spn   a0, sp, 448
                  c.srli       s1, 26
                  c.srai       s1, 29
                  auipc        sp, 414352
                  slt          s7, s10, s6
                  mul          sp, s8, s7
                  c.andi       s0, -1
                  c.xor        a3, a5
                  addi         t3, s2, -1003
                  xor          a7, s5, a5
                  mulh         gp, a1, s10
                  lui          s2, 121429
                  c.addi4spn   a3, sp, 560
                  c.slli       gp, 25
                  mulhsu       s9, s5, ra
                  c.addi4spn   s0, sp, 992
                  c.addi4spn   a0, sp, 928
                  c.addi4spn   a5, sp, 208
                  c.nop
                  mul          s1, a0, s11
                  c.addi16sp   sp, -16
                  ori          s1, s4, -1664
                  rem          a2, a3, t5
                  mulh         s10, s2, t4
                  mulhsu       a3, a0, t3
                  remu         s9, a6, s2
                  xori         ra, a1, -1864
                  sra          s7, s10, t5
                  mulhsu       t3, s1, s5
                  c.addi       t4, 12
                  c.li         t3, 15
                  c.nop
                  srai         gp, a5, 21
                  auipc        a0, 42644
                  sltiu        t3, ra, 1582
                  sltu         t4, a6, a2
                  sub          s3, t0, s3
                  add          t2, t1, s4
                  andi         a6, gp, -2044
                  c.li         s3, 22
                  ori          s0, gp, 1082
                  c.xor        a2, s0
                  sra          a7, sp, a1
                  mulhu        s10, t0, s10
                  xori         t2, a0, 1519
                  addi         s8, a7, -2015
                  add          s4, s3, s2
                  mulhu        sp, t5, s5
                  srli         zero, zero, 7
                  nop
                  slt          s3, t5, tp
                  c.and        s1, s0
                  c.and        s0, a3
                  lui          zero, 508227
                  c.nop
                  mul          a7, a5, s1
                  srl          s0, a0, s11
                  mulhsu       t6, a4, a5
                  auipc        s0, 825373
                  ori          zero, a2, 542
                  sltiu        t6, a2, 639
                  sra          s8, gp, a1
                  c.nop
                  andi         t4, t6, -1876
                  c.add        s10, s6
                  c.li         t0, 26
                  mulhu        s2, s9, zero
                  nop
                  c.lui        s3, 4
                  mulhu        a3, s9, t6
                  c.nop
                  mulh         s11, s1, s0
                  mul          t4, t1, s6
                  c.and        a0, s0
                  add          s4, a2, s10
                  c.and        s1, a3
                  sra          s5, gp, zero
                  c.addi       t3, -1
                  add          s0, s8, t0
                  mulhu        sp, a2, s1
                  c.addi4spn   a0, sp, 688
                  mulh         a2, tp, s7
                  c.andi       a5, -1
                  xor          sp, a5, s4
                  sra          s0, s2, a0
                  c.and        a2, s0
                  c.and        a2, a2
                  slt          t6, gp, s3
                  c.lui        s1, 20
                  div          gp, s7, t6
                  c.addi4spn   s0, sp, 320
                  divu         s2, a7, a5
                  srai         gp, a6, 7
                  mulhu        ra, s10, sp
                  ori          t1, s8, 1727
                  slti         tp, s1, -211
                  c.xor        a0, a0
                  mulhu        sp, s11, t6
                  sra          t3, gp, a0
                  xori         a3, s7, -261
                  c.addi16sp   sp, 432
                  mulh         s8, sp, t2
                  xori         a5, t0, -544
                  xori         tp, t5, 720
                  c.srli       a0, 14
                  c.addi4spn   s0, sp, 576
                  div          gp, ra, s7
                  sra          s5, a3, a7
                  c.srli       a2, 3
                  sltiu        zero, a5, -1455
                  c.xor        a5, s1
                  andi         zero, s4, -1945
                  addi         s5, t2, 1912
                  c.and        a5, a3
                  andi         t5, a1, -473
                  c.sub        a2, s0
                  srli         zero, ra, 2
                  srl          sp, t4, s1
                  mulh         t4, s0, a4
                  sltiu        s5, s0, 1534
                  c.mv         s3, t1
                  srai         gp, t2, 6
                  andi         ra, a7, -1658
                  c.nop
                  c.andi       s1, -1
                  mulh         t0, tp, a3
                  mulhsu       s8, a3, t2
                  auipc        s1, 6809
                  add          a6, t2, a0
                  div          tp, s6, s5
                  andi         tp, s11, -973
                  slti         s11, s3, 1142
                  srli         s5, gp, 22
                  sra          s1, t3, t6
                  c.addi4spn   a3, sp, 640
                  c.nop
                  sltu         a5, t2, s5
                  remu         tp, t4, a1
                  mul          s4, t0, t4
                  mulhsu       sp, s2, s10
                  and          s8, s1, s3
                  xor          tp, s9, a4
                  remu         t0, a1, s4
                  c.srai       a5, 13
                  c.or         s1, a4
                  mulhu        t6, s4, s11
                  auipc        s1, 699446
                  c.andi       a3, -1
                  c.mv         t3, s0
                  c.lui        s3, 29
                  c.addi16sp   sp, -16
                  c.and        s0, a1
                  c.addi4spn   a5, sp, 480
                  lui          t4, 466730
                  c.xor        a5, a2
                  divu         t2, s8, a1
                  c.slli       s3, 26
                  slt          s8, zero, s2
                  c.add        t3, a5
                  c.addi4spn   s0, sp, 864
                  c.sub        s1, a2
                  and          t0, ra, a6
                  slli         s1, ra, 9
                  c.li         t2, 15
                  srl          ra, s10, t2
                  c.and        a5, a2
                  rem          s9, a6, t2
                  c.slli       a7, 9
                  c.li         t4, -1
                  slti         s2, a4, -997
                  mulh         tp, s1, zero
                  mulhsu       s11, sp, a3
                  c.addi16sp   sp, -16
                  c.srli       a5, 26
                  addi         t0, a4, 760
                  or           s5, t2, t1
                  and          t5, t3, ra
                  mul          a0, s3, s8
                  srli         a5, a3, 26
                  add          s2, s8, a5
                  c.andi       a3, -1
                  xor          s4, gp, a0
                  mulh         t5, t6, a7
                  nop
                  slt          s10, a5, a2
                  srai         t3, s8, 4
                  xor          s1, a3, s5
                  c.srai       a0, 18
                  div          a2, t2, s0
                  c.nop
                  sltu         tp, t2, a3
                  lui          s4, 286701
                  divu         t1, a0, gp
                  slti         t1, ra, -1224
                  addi         t3, a0, 1904
                  c.andi       a2, -1
                  c.nop
                  sll          a2, s7, t2
                  mulh         a6, zero, s0
                  c.or         s0, a4
                  c.sub        a2, a4
                  c.sub        a0, a1
                  div          a2, t2, s8
                  xor          a6, a1, ra
                  lui          a5, 858199
                  sub          a2, t6, tp
                  c.sub        a5, a3
                  rem          t4, gp, a0
                  mulhsu       s8, s11, t3
                  slti         s3, s8, 472
                  c.nop
                  sra          s4, tp, s4
                  sltu         s2, a7, s6
                  c.srai       a0, 15
                  sra          a5, t5, s6
                  mulhu        a2, s2, s3
                  c.srli       a3, 11
                  c.andi       a5, -1
                  nop
                  sltu         s11, a4, t6
                  c.slli       t6, 20
                  xori         s0, s10, 939
                  c.li         s7, 18
                  andi         s2, s1, -671
                  rem          s0, a7, zero
                  li           t1, 0x80000000 #start riscv_int_numeric_corner_stream_7
                  li           s1, 0x80000000
                  li           tp, 0x1684f929
                  li           s11, 0x0
                  li           s5, 0x80000000
                  li           s8, 0x0
                  li           s2, 0x0
                  li           a0, 0xffffffff
                  li           sp, 0xffffffff
                  li           a3, 0xde98eeb5
                  mulhu        s5, s11, tp
                  mulh         s8, s1, s1
                  divu         s1, s2, s1
                  sub          s5, s8, sp
                  add          s11, s11, t1
                  lui          sp, 54495
                  mulhsu       t1, sp, s8
                  div          sp, s5, a0
                  lui          s11, 694622
                  divu         tp, s1, s5
                  addi         a0, tp, -426
                  div          sp, s11, s8
                  auipc        a0, 644068
                  addi         s2, s8, -1180
                  rem          s1, a0, s1
                  remu         a3, s8, sp
                  mulh         sp, a3, s2
                  div          t1, s1, s11
                  nop
                  sub          sp, s1, a3 #end riscv_int_numeric_corner_stream_7
                  c.sub        s1, a0
                  and          t0, a7, t1
                  slli         t4, s11, 28
                  c.lui        s11, 31
                  c.lui        s11, 18
                  c.lui        s9, 28
                  sltu         a3, s2, s7
                  and          t1, zero, ra
                  c.addi       t5, 12
                  c.sub        s0, s1
                  divu         gp, tp, s3
                  add          s10, a0, s9
                  c.add        t0, a0
                  srl          s2, s8, ra
                  sra          a0, s1, s6
                  div          s11, a7, t3
                  c.srai       s1, 12
                  srli         s2, a0, 24
                  c.addi       t5, -1
                  c.srai       s0, 29
                  xor          s5, gp, s7
                  c.li         t2, 19
                  c.addi16sp   sp, 16
                  c.slli       s4, 14
                  or           t1, t0, a4
                  remu         tp, gp, tp
                  xor          a6, t3, t3
                  xor          t4, s6, s8
                  mulh         a3, a0, zero
                  and          a2, a7, a6
                  xori         ra, t3, 543
                  c.nop
                  divu         t1, s9, s9
                  slli         a3, s0, 20
                  srli         gp, s10, 29
                  sltiu        a0, s11, 1517
                  slt          t2, s9, t2
                  sub          s9, t1, t0
                  slti         t6, a7, 587
                  or           t0, s0, s7
                  sltu         zero, s5, s9
                  sltiu        s7, s7, -74
                  sll          s3, s8, s4
                  ori          s1, t3, -311
                  srli         tp, a4, 25
                  and          s9, s4, a0
                  c.and        s1, a2
                  c.and        a3, a1
                  add          t5, s4, t2
                  ori          ra, s3, 1035
                  rem          gp, a0, a7
                  or           s2, s6, a2
                  c.add        s4, a1
                  addi         tp, ra, 1985
                  c.li         s11, 12
                  c.and        a0, a2
                  rem          s9, s1, t5
                  auipc        sp, 774598
                  mulhu        s1, a5, s3
                  sltu         zero, s11, t0
                  srai         tp, s11, 11
                  mulhsu       s3, s10, t2
                  sltu         s10, t3, s0
                  c.nop
                  c.addi16sp   sp, -16
                  slt          s0, s4, t0
                  srai         s5, s7, 17
                  add          zero, s2, gp
                  div          t6, zero, t6
                  slli         t3, ra, 22
                  c.lui        t3, 7
                  srl          t0, a5, s2
                  c.and        a2, a2
                  mul          gp, gp, s10
                  xori         t3, t6, 927
                  sub          t5, zero, ra
                  mulh         s2, t3, s0
                  sub          s3, s10, t1
                  sra          t0, t0, t0
                  c.xor        a5, s1
                  add          s11, s6, a3
                  sll          a2, t2, sp
                  mul          a3, a3, t4
                  c.addi16sp   sp, -16
                  c.andi       s1, -1
                  c.nop
                  andi         t4, sp, -1577
                  and          a2, a1, t5
                  c.addi       a2, 9
                  mulhu        tp, a3, t5
                  ori          s5, a6, -1515
                  lui          s0, 88957
                  mulhsu       a2, s4, s0
                  andi         a2, zero, -1487
                  mul          tp, t0, a0
                  mulhu        gp, s3, a2
                  c.andi       s0, 19
                  c.slli       s10, 10
                  nop
                  lui          ra, 855853
                  ori          t3, t5, -127
                  c.addi16sp   sp, 240
                  sra          s2, s8, s9
                  c.and        a5, a3
                  c.lui        s8, 11
                  mulhu        s5, a6, t6
                  mulh         t5, s8, sp
                  c.add        a6, tp
                  c.or         a2, a2
                  c.sub        s0, a0
                  c.andi       a2, -1
                  srai         a3, t1, 27
                  srli         gp, t3, 22
                  auipc        a3, 981715
                  c.addi4spn   a0, sp, 480
                  and          gp, t1, a3
                  c.li         s10, 2
                  c.sub        a2, a2
                  remu         s8, t4, s0
                  c.xor        s1, a3
                  c.sub        s0, a0
                  or           t0, a3, ra
                  add          t5, t1, s9
                  c.andi       a3, 0
                  slli         s3, t4, 19
                  c.xor        s1, a1
                  srli         t3, s5, 12
                  mulhsu       t2, s10, s10
                  srai         s2, tp, 6
                  xori         s5, t6, -1996
                  rem          s9, a7, t5
                  andi         s3, a3, 1625
                  c.nop
                  xor          t4, s4, s4
                  andi         s5, ra, 293
                  mulhu        t6, s1, a1
                  c.srli       s0, 8
                  nop
                  slli         zero, a4, 30
                  lui          s9, 887665
                  c.addi       s4, -1
                  mulh         s0, sp, a5
                  c.addi4spn   a3, sp, 784
                  c.nop
                  c.addi       s1, -1
                  sub          t5, t5, a5
                  c.srai       a3, 10
                  c.sub        s1, a5
                  c.slli       s10, 24
                  sltu         t4, t1, a2
                  srai         a3, s6, 4
                  or           s5, s7, s11
                  srli         s9, t5, 21
                  divu         s10, s0, a0
                  divu         t5, t6, t3
                  remu         s10, t4, tp
                  remu         t2, a0, s8
                  c.and        s1, a4
                  c.xor        a5, a3
                  slti         s1, s9, 253
                  rem          t6, t4, t3
                  sltu         t0, a7, s11
                  and          zero, s0, s4
                  remu         sp, s11, zero
                  c.lui        gp, 26
                  auipc        a3, 843335
                  c.xor        a0, s0
                  c.srai       a5, 9
                  srai         gp, t3, 25
                  divu         a6, t4, s7
                  xor          t5, t6, a1
                  sll          gp, s5, s8
                  andi         sp, a7, -64
                  addi         t2, a6, 520
                  mulhu        a0, a5, t2
                  slt          s1, s7, s9
                  sra          t2, s7, s6
                  c.add        s0, s8
                  sub          a7, a7, zero
                  xor          ra, s10, ra
                  c.slli       s9, 15
                  remu         s5, s5, a0
                  rem          s5, s1, t2
                  c.addi       a6, -1
                  sra          t2, s6, t0
                  c.addi       ra, 26
                  srl          s5, s4, a2
                  c.li         t6, 24
                  srli         sp, s5, 6
                  xor          s10, s1, a4
                  sra          t1, zero, t5
                  sll          sp, s11, t4
                  c.mv         t2, s7
                  c.mv         t5, a4
                  c.addi4spn   s1, sp, 96
                  slti         s3, s4, 701
                  c.li         ra, -1
                  remu         s5, s4, s10
                  c.andi       a2, -1
                  c.slli       ra, 16
                  srl          t5, s5, s5
                  sltu         t4, a6, s2
                  rem          a3, s8, s9
                  nop
                  add          a2, a3, s1
                  or           gp, s1, t2
                  c.andi       a3, -1
                  mulhu        a6, t3, s10
                  c.mv         t0, s10
                  mul          t5, s7, t1
                  xori         a5, zero, -1287
                  c.addi16sp   sp, 320
                  addi         sp, s0, 1773
                  sltiu        s11, t6, -1818
                  mulhu        s4, a6, a1
                  andi         s1, s11, 1896
                  srai         s7, t1, 4
                  mulh         s2, a7, t2
                  lui          t3, 583507
                  sub          gp, s6, a4
                  add          a7, s2, s7
                  and          s8, gp, a2
                  xori         zero, a1, -197
                  slti         t3, tp, 133
                  divu         tp, s3, a1
                  and          a5, t0, t3
                  and          s2, a5, s7
                  mulhu        zero, a6, a2
                  c.srai       a5, 30
                  c.add        t4, t1
                  add          s10, s9, s10
                  sll          a0, gp, a5
                  c.srli       a5, 15
                  sra          zero, s8, s10
                  auipc        zero, 1020965
                  c.addi16sp   sp, 256
                  lui          a3, 926155
                  slli         s1, s0, 20
                  c.add        a7, s7
                  srai         t2, s0, 10
                  mulhu        s0, s4, zero
                  sra          a6, gp, s8
                  and          s3, a5, s0
                  sll          a0, s10, t5
                  c.srli       a5, 5
                  mulhsu       t5, s0, a0
                  c.andi       a0, 26
                  c.addi       tp, 5
                  addi         s1, t3, 961
                  and          s7, s3, t6
                  xori         t4, t6, 1372
                  lui          zero, 757649
                  and          t4, a3, s7
                  andi         t6, tp, 18
                  c.sub        a0, a3
                  c.srai       a5, 20
                  div          s2, s9, s8
                  mulhu        a3, s9, tp
                  c.lui        s11, 22
                  c.lui        s8, 18
                  mulhu        s5, t1, s4
                  srli         tp, t1, 4
                  sra          t0, t1, a1
                  xori         zero, s9, -1999
                  c.addi4spn   a5, sp, 544
                  c.sub        a0, s1
                  c.srli       a2, 29
                  sub          s7, s3, a0
                  lui          t3, 62608
                  mulhu        s8, a5, tp
                  c.addi4spn   a2, sp, 688
                  xor          s10, a1, s6
                  mul          a6, a5, s8
                  c.or         a2, a2
                  add          s3, s5, sp
                  mulh         s11, a0, a5
                  c.srli       s1, 23
                  c.sub        a2, a3
                  c.li         t2, -1
                  c.addi4spn   a5, sp, 976
                  mulhsu       t6, ra, a5
                  c.andi       s1, 9
                  srai         s4, a6, 29
                  c.andi       a3, 15
                  mulh         t3, a5, s8
                  srli         s11, a1, 12
                  srai         t2, a4, 1
                  c.lui        s7, 16
                  srli         s3, s6, 18
                  c.sub        s0, a5
                  sltu         s11, t2, s10
                  and          s3, t0, a0
                  slti         zero, gp, -1320
                  sra          s3, tp, a6
                  c.sub        s1, a2
                  remu         gp, s8, t5
                  andi         s11, tp, -397
                  srl          s0, t4, a2
                  mulh         a6, s9, a7
                  c.addi       a0, -1
                  c.nop
                  c.lui        t4, 5
                  c.mv         a3, t1
                  c.slli       t5, 27
                  add          a6, s8, t6
                  c.addi16sp   sp, 272
                  mulh         t1, s7, a0
                  slt          s5, t0, s7
                  xor          s9, ra, a4
                  nop
                  srl          s3, s8, a1
                  sltiu        a7, s8, 1961
                  add          s4, s1, t2
                  divu         s1, a5, s2
                  xori         s0, t6, 1285
                  c.srai       a3, 10
                  divu         s10, a2, s1
                  c.slli       s8, 31
                  c.or         s1, a4
                  c.li         s11, -1
                  c.li         a3, 5
                  xori         t1, s0, 1405
                  c.addi4spn   s0, sp, 144
                  or           gp, s2, a5
                  c.addi       gp, -1
                  mulh         t3, s9, s11
                  srli         a0, a0, 13
                  mul          a6, s7, t1
                  sra          s5, tp, s3
                  c.li         s11, 12
                  or           a0, gp, a4
                  c.nop
                  xor          s0, a5, t4
                  c.and        a2, a4
                  andi         zero, s3, 536
                  slt          a0, a3, gp
                  c.andi       a3, 16
                  sub          s2, a5, s8
                  mulhsu       s0, s3, s0
                  div          s2, t1, sp
                  c.li         t6, 20
                  c.li         t4, 28
                  c.li         a2, 3
                  auipc        gp, 844435
                  rem          zero, s6, s6
                  c.add        s9, a0
                  addi         a3, s7, -995
                  c.addi       s1, -1
                  c.sub        s1, s0
                  divu         sp, s6, s3
                  lui          gp, 378454
                  addi         t6, t1, 632
                  auipc        s7, 826379
                  mulhsu       t3, t0, s1
                  c.xor        s0, a0
                  c.addi4spn   a5, sp, 720
                  div          t5, s2, s6
                  c.srai       s0, 30
                  andi         s4, zero, 735
                  divu         t0, t1, t6
                  xori         s3, a4, -1944
                  c.srai       a3, 11
                  or           ra, t2, t4
                  sltiu        s4, a7, 1870
                  xor          s5, s0, t2
                  remu         a5, gp, a4
                  c.nop
                  nop
                  sll          zero, zero, t0
                  rem          t1, s5, sp
                  sra          gp, tp, a0
                  mulh         s10, s1, t4
                  srli         s10, s8, 11
                  c.addi       s4, 5
                  c.and        a2, a0
                  ori          ra, t0, 1953
                  srai         a3, gp, 15
                  c.nop
                  c.li         s8, 23
                  c.and        s0, a0
                  and          sp, s11, ra
                  div          gp, s4, s0
                  mulhsu       gp, t4, s6
                  c.nop
                  remu         s9, s5, tp
                  srai         a6, s8, 13
                  ori          a3, a7, 753
                  c.or         s1, a4
                  c.addi       a5, -1
                  add          s3, t3, tp
                  divu         tp, a4, tp
                  xor          gp, ra, a2
                  mulhsu       t5, s3, s6
                  c.add        t6, t5
                  c.xor        a2, s1
                  lui          s11, 976554
                  sll          t4, t3, ra
                  auipc        s8, 812056
                  mul          s8, t6, s2
                  mulhsu       s0, s2, s7
                  ori          t2, a7, 729
                  c.add        s4, t2
                  c.andi       a3, 31
                  nop
                  mul          s0, gp, zero
                  c.li         a6, 9
                  c.add        s0, s4
                  slli         s5, s3, 19
                  c.add        gp, t1
                  c.andi       s0, 15
                  c.xor        a3, a2
                  mulhsu       s7, s8, a5
                  auipc        zero, 1041035
                  mulhu        ra, t3, a1
                  c.and        s1, a2
                  c.lui        t3, 11
                  srli         t5, s11, 18
                  c.addi16sp   sp, 144
                  srai         s1, a4, 3
                  c.mv         a0, s0
                  mulhsu       s8, s8, a0
                  srl          a2, ra, a7
                  c.srai       a5, 18
                  div          gp, s6, s7
                  sltiu        s10, t0, -368
                  mul          t0, a3, s8
                  c.add        s7, s11
                  c.sub        a0, s0
                  sltiu        a0, t4, -1563
                  c.addi16sp   sp, -16
                  mul          tp, t1, a3
                  auipc        s10, 90371
                  c.xor        a0, a1
                  c.add        a2, t6
                  c.addi16sp   sp, -16
                  sltiu        t4, s7, 1025
                  c.mv         s9, t2
                  c.mv         t3, tp
                  sll          t5, a6, a6
                  mulhsu       a0, s4, tp
                  c.li         t4, -1
                  c.addi       t3, 28
                  xor          a0, t0, s5
                  srli         s7, s3, 28
                  c.addi16sp   sp, -16
                  addi         zero, a0, 1965
                  auipc        t2, 674971
                  mul          a0, s0, s9
                  mul          sp, s4, s11
                  c.sub        a5, s0
                  auipc        s1, 5104
                  xori         a5, zero, 1555
                  mulh         zero, a6, t1
                  c.slli       a0, 3
                  slt          t5, sp, a5
                  c.nop
                  rem          a5, s6, ra
                  rem          s7, a4, a6
                  auipc        t5, 451593
                  c.slli       a6, 7
                  divu         s0, s3, t3
                  lui          s8, 541063
                  srai         t2, s2, 9
                  sub          a0, s10, a2
                  srl          s10, s8, ra
                  xor          s3, tp, a4
                  add          s3, s0, a7
                  divu         a3, s2, s4
                  c.slli       ra, 29
                  c.srai       s1, 2
                  c.add        a3, tp
                  c.addi4spn   s0, sp, 80
                  and          t4, a0, s7
                  mul          a3, s5, a5
                  sltu         t0, a1, a2
                  c.and        s0, a1
                  add          s0, s0, zero
                  mulhu        s0, s1, a4
                  c.addi16sp   sp, 400
                  mul          s9, a0, a5
                  andi         sp, s6, 770
                  sub          s7, a5, s2
                  div          tp, s3, s7
                  sll          s3, a4, t1
                  c.andi       a2, 26
                  c.srli       s0, 9
                  addi         s3, t3, -1261
                  lui          sp, 538729
                  rem          s4, t0, t5
                  sra          t3, t3, s6
                  srai         a2, t6, 25
                  c.slli       gp, 26
                  sltu         t0, a5, s1
                  mulhsu       ra, s3, t5
                  auipc        gp, 365500
                  add          t2, a5, s8
                  lui          a0, 154420
                  srli         s1, s10, 1
                  div          s10, t3, sp
                  c.nop
                  sll          a5, s8, s1
                  add          t5, a7, s10
                  remu         s7, s9, t1
                  c.xor        s0, a1
                  srl          t4, t3, t3
                  xori         a3, a3, -1188
                  srl          s0, s3, a6
                  mulh         a3, t4, a1
                  c.addi16sp   sp, 160
                  c.addi16sp   sp, 96
                  c.slli       a7, 18
                  c.mv         s10, a0
                  addi         t3, s4, -1419
                  c.srli       a3, 13
                  sub          s11, s10, s1
                  sltu         s1, s6, zero
                  remu         s7, sp, a1
                  nop
                  add          s2, s0, s8
                  xori         t0, a7, -970
                  mulhsu       sp, s3, s5
                  nop
                  c.lui        s2, 23
                  xor          tp, t5, s2
                  sll          t3, t4, s9
                  c.addi4spn   a0, sp, 368
                  sub          ra, s3, s11
                  c.lui        t5, 16
                  xor          t3, s11, t1
                  sub          a3, s5, gp
                  srl          s0, a1, s1
                  c.srli       s1, 23
                  divu         zero, sp, a3
                  auipc        s0, 543321
                  slli         gp, s2, 29
                  srli         s2, t4, 10
                  remu         t3, t2, t4
                  c.add        a6, gp
                  or           s11, a5, s0
                  mulhsu       a5, s5, s6
                  c.addi16sp   sp, 48
                  sltu         zero, s8, a5
                  sltiu        gp, a2, -1147
                  c.addi4spn   s1, sp, 752
                  slli         t1, t1, 25
                  c.mv         s11, a0
                  c.and        a0, a0
                  c.slli       gp, 19
                  c.xor        a0, s1
                  mulhu        a3, t5, ra
                  div          t5, s0, tp
                  ori          t4, a6, 1977
                  c.srli       a5, 13
                  mul          t1, t4, a0
                  c.andi       a5, 12
                  sll          s10, s4, s10
                  c.lui        tp, 18
                  slli         t3, s2, 15
                  sltiu        zero, t0, -378
                  li           a0, 0xea985a1c #start riscv_int_numeric_corner_stream_28
                  li           s11, 0x0
                  li           s4, 0x62c8799
                  li           ra, 0x80000000
                  li           t4, 0xb761a551
                  li           a7, 0x13769112
                  li           a6, 0x80000000
                  li           gp, 0x0
                  li           t3, 0x0
                  li           s1, 0x607f4cd6
                  lui          t3, 95275
                  mulhu        s4, s1, gp
                  mul          gp, s4, a0
                  mulhu        s11, s11, s11
                  rem          t4, t4, t4
                  div          s4, s1, ra
                  mul          a6, a0, t4
                  mulh         s1, ra, s4
                  rem          ra, ra, s11
                  mulh         a0, s1, s4
                  lui          t3, 732493
                  add          t4, ra, s11
                  auipc        a6, 409627
                  auipc        s4, 717284
                  rem          s4, s1, s1
                  nop
                  remu         a0, gp, t4
                  mul          ra, t4, a6
                  mul          s1, ra, ra
                  mul          s1, t4, t4
                  lui          gp, 499899
                  remu         a7, t3, a0
                  mul          t4, s1, t4 #end riscv_int_numeric_corner_stream_28
                  c.xor        a3, a4
                  divu         t5, t2, a1
                  c.mv         a2, s9
                  srai         a2, t2, 18
                  srli         a0, s9, 20
                  srl          t0, a6, a4
                  c.add        t3, a5
                  sltu         s5, t5, a2
                  mulh         s9, s3, ra
                  remu         ra, gp, t1
                  srai         a7, s3, 23
                  c.sub        s0, s0
                  andi         t5, s5, -867
                  sltiu        ra, s9, 131
                  c.or         a5, a1
                  c.addi16sp   sp, -16
                  sra          t0, s11, t3
                  rem          a3, a5, gp
                  mulhu        tp, a3, a0
                  srli         s7, s7, 29
                  sltu         t4, s7, s2
                  slt          s11, a4, zero
                  c.addi       tp, 3
                  mulhsu       s0, a1, a7
                  c.sub        s1, s1
                  lui          s4, 185891
                  mul          t2, s11, s7
                  xor          a5, t5, s4
                  c.addi16sp   sp, 192
                  mulhu        s8, a7, t1
                  mul          s9, s7, a4
                  c.li         t2, 19
                  remu         s5, s6, a1
                  mulhsu       a5, s4, t3
                  slli         t3, t1, 0
                  c.srli       s1, 14
                  or           s9, sp, a0
                  xor          zero, s7, a1
                  sltu         a2, a3, s0
                  c.addi16sp   sp, -16
                  srli         a5, t4, 19
                  mul          s0, s10, sp
                  slti         t3, s9, 819
                  slt          s3, t3, a4
                  c.and        a3, a0
                  c.slli       s3, 7
                  remu         a3, s8, t0
                  lui          t6, 74005
                  mulhsu       t0, s7, tp
                  c.li         a3, -1
                  or           gp, t4, a3
                  add          t0, s1, a2
                  c.li         s1, -1
                  c.lui        s2, 6
                  xor          t1, s5, tp
                  c.addi16sp   sp, -16
                  c.li         t1, -1
                  add          a7, s1, ra
                  c.addi16sp   sp, -16
                  c.add        ra, gp
                  rem          t6, t4, a3
                  c.srli       s1, 11
                  c.lui        t4, 11
                  nop
                  slli         a5, a1, 8
                  c.mv         s2, gp
                  div          t3, a7, s1
                  or           s1, s3, t3
                  srl          sp, s4, s5
                  c.li         t2, 25
                  c.sub        a3, a4
                  remu         s4, ra, a0
                  c.lui        s1, 21
                  c.add        s10, a1
                  auipc        t0, 935369
                  mulhu        t5, s11, s10
                  mulhsu       t5, s10, t1
                  c.addi16sp   sp, 352
                  mulhsu       zero, t2, zero
                  lui          a0, 475607
                  srli         s2, a5, 6
                  div          zero, a6, s1
                  slli         s2, s5, 0
                  mulhu        zero, tp, s10
                  sltiu        a3, s2, 1193
                  divu         t1, gp, t5
                  c.xor        s0, a1
                  c.addi4spn   a3, sp, 560
                  srli         zero, s11, 12
                  nop
                  mulh         t1, a2, s0
                  srli         a2, s10, 9
                  c.sub        a0, a4
                  mulhu        ra, s1, a4
                  sll          s11, a5, t1
                  rem          s8, s6, t3
                  c.addi       t6, -1
                  c.li         s5, -1
                  c.addi4spn   a3, sp, 208
                  add          a2, s6, a2
                  c.nop
                  lui          s3, 233331
                  sltu         s7, a5, tp
                  c.add        ra, t6
                  rem          s5, tp, s2
                  c.addi16sp   sp, -16
                  c.li         sp, 19
                  c.andi       a0, 27
                  c.addi4spn   a5, sp, 736
                  addi         ra, s10, -1009
                  sltiu        a3, t3, 1192
                  srai         t2, t0, 19
                  c.lui        s4, 29
                  ori          a0, a2, -1375
                  rem          s5, s11, s11
                  c.addi4spn   a5, sp, 560
                  addi         zero, a4, -495
                  auipc        ra, 752485
                  c.lui        t1, 27
                  sll          t1, s6, s9
                  c.addi4spn   a3, sp, 672
                  xor          s11, zero, gp
                  c.addi4spn   a0, sp, 208
                  c.sub        a5, a0
                  xori         a6, tp, -48
                  srli         s0, s9, 24
                  remu         t2, t1, ra
                  lui          a5, 660232
                  c.and        a5, a5
                  xori         s8, a5, -779
                  divu         s2, sp, t1
                  srai         t2, s4, 28
                  and          tp, s10, s5
                  c.and        s0, a1
                  xor          t4, t4, s9
                  sra          t5, t4, s0
                  c.srai       s1, 12
                  ori          s5, t3, 1985
                  andi         s11, s8, -343
                  mulhsu       a5, s3, s6
                  add          t5, a0, t0
                  sub          s9, tp, s1
                  rem          tp, a2, a5
                  ori          s11, a3, 62
                  c.andi       s1, -1
                  c.sub        a2, a2
                  lui          t0, 1003950
                  c.nop
                  c.srai       s0, 30
                  srai         a3, sp, 0
                  add          s9, a0, a3
                  srai         sp, gp, 31
                  addi         tp, s3, 1832
                  divu         t1, s8, s10
                  mulhsu       s5, zero, s7
                  and          sp, t4, s9
                  c.and        a3, a4
                  c.addi16sp   sp, -16
                  slli         t2, ra, 22
                  addi         s4, t2, -1075
                  slti         t4, a1, 1363
                  c.li         t4, 29
                  add          t5, a6, s10
                  sltu         t3, t6, gp
                  div          s10, s9, s7
                  c.sub        s1, a5
                  c.or         s1, a1
                  c.xor        a2, a2
                  mulhu        zero, t6, t2
                  addi         a3, a4, 347
                  c.sub        a2, a1
                  c.xor        s1, a2
                  and          a0, s9, a4
                  div          t0, s5, s3
                  c.sub        s0, a4
                  c.addi16sp   sp, -16
                  c.lui        s7, 11
                  sra          a6, t5, s5
                  remu         s0, a0, tp
                  c.lui        a2, 8
                  sltu         zero, a6, ra
                  mul          s0, a6, a2
                  sltiu        s8, t4, 1742
                  srai         s8, s10, 13
                  c.srli       s0, 25
                  srli         a3, s5, 8
                  c.li         a2, -1
                  divu         s8, t4, s0
                  c.addi       t6, -1
                  c.srli       a5, 3
                  andi         gp, a6, -194
                  mulhu        gp, s0, s8
                  c.nop
                  c.li         a2, -1
                  c.or         s1, a3
                  slt          t2, zero, a6
                  c.addi       a6, 11
                  or           s5, t1, zero
                  c.slli       s11, 16
                  c.and        a5, a0
                  srai         s1, ra, 30
                  c.lui        t1, 17
                  nop
                  lui          a6, 249414
                  div          tp, s4, zero
                  c.li         s3, 2
                  c.addi4spn   s1, sp, 960
                  c.xor        a5, s1
                  slt          t2, t6, a2
                  slti         s7, s8, 186
                  xori         s9, t1, -1590
                  mul          sp, t5, zero
                  srli         a5, s10, 5
                  c.addi4spn   a3, sp, 416
                  slli         t4, s7, 10
                  c.addi16sp   sp, 368
                  sltu         t2, a4, s2
                  mulh         t6, a4, s10
                  c.li         s8, 31
                  lui          a2, 541250
                  div          s4, t6, t1
                  and          t3, s0, s0
                  andi         a3, t3, 984
                  mul          t0, a2, t6
                  nop
                  c.addi16sp   sp, -16
                  c.srli       a3, 16
                  slti         a5, s5, -329
                  andi         t1, s4, 168
                  srli         s10, s8, 11
                  c.xor        a3, a3
                  slti         s11, t3, 199
                  c.addi4spn   a5, sp, 304
                  c.and        s0, a1
                  c.andi       s1, -1
                  div          tp, a3, s9
                  sltu         a7, t3, a6
                  c.add        t0, a0
                  srli         tp, t1, 5
                  c.li         s1, -1
                  mulh         a2, ra, s3
                  and          t3, a0, a7
                  c.slli       a3, 2
                  addi         t5, tp, 290
                  nop
                  mul          a0, t1, t3
                  rem          s1, s7, gp
                  divu         ra, a3, ra
                  andi         zero, a4, -1937
                  c.srli       s1, 15
                  c.add        t2, t4
                  slli         t2, a5, 21
                  and          t3, a2, s1
                  mulhu        t2, t6, sp
                  mul          t3, a7, a2
                  slt          s5, ra, s0
                  rem          s8, s9, tp
                  mul          gp, t3, a5
                  auipc        s9, 925056
                  mul          t6, a5, s3
                  slt          t0, t1, zero
                  xor          s5, a6, s3
                  mulh         s4, a4, a0
                  c.srai       a3, 29
                  c.mv         s5, s9
                  lui          s11, 555277
                  c.mv         gp, a4
                  c.addi       t0, 5
                  c.sub        a0, s1
                  lui          tp, 640953
                  c.mv         sp, a2
                  srli         a3, t5, 29
                  c.sub        a0, a5
                  slli         t4, a5, 12
                  div          t3, a5, a4
                  andi         s0, t2, 228
                  c.or         a3, a3
                  nop
                  c.or         a3, a1
                  c.lui        t0, 28
                  c.srai       s1, 6
                  c.and        a0, a3
                  sub          sp, s2, s1
                  remu         t1, s6, s5
                  c.addi16sp   sp, 288
                  srl          a3, a3, a5
                  c.sub        s1, a2
                  c.addi16sp   sp, -16
                  c.sub        s1, a2
                  c.srai       s0, 1
                  sll          s11, s2, s10
                  c.and        a3, a0
                  mulh         s9, s0, a7
                  c.or         a2, a2
                  sub          s5, t5, s2
                  li           s2, 0x0 #start riscv_int_numeric_corner_stream_30
                  li           a6, 0xffffffff
                  li           s1, 0xffffffff
                  li           tp, 0x0
                  li           s7, 0x80000000
                  li           a0, 0xffffffff
                  li           s10, 0x0
                  li           gp, 0x80000000
                  li           t5, 0x0
                  li           t2, 0x74f9bc08
                  rem          a6, s10, tp
                  lui          t2, 675941
                  addi         gp, t2, 918
                  mulhsu       a6, s1, s10
                  sub          t2, s1, tp
                  addi         tp, t5, -400
                  nop
                  mul          gp, a0, t5
                  divu         gp, t5, tp
                  sub          a0, gp, a6
                  divu         s10, a6, a0
                  divu         a0, a0, tp
                  divu         t5, tp, a6
                  lui          s2, 149439
                  remu         s10, tp, s1
                  nop
                  auipc        tp, 1006194
                  mulhu        tp, tp, gp
                  divu         s7, t5, gp
                  mulhu        a0, t2, s7
                  mul          a0, a6, s10 #end riscv_int_numeric_corner_stream_30
                  c.and        a5, a5
                  mulhsu       a2, s8, tp
                  andi         a0, t5, -2006
                  c.srli       a2, 4
                  c.andi       a3, -1
                  c.xor        s0, a0
                  and          t0, t2, zero
                  c.slli       s10, 17
                  ori          t2, s1, -258
                  remu         t1, a5, ra
                  srai         s2, s10, 3
                  c.or         a2, a2
                  slti         s5, s4, 96
                  slli         a2, t0, 10
                  slt          a3, sp, t1
                  sltu         ra, t3, s1
                  slti         a2, s2, -2025
                  sra          t1, a7, s0
                  mulhsu       t5, t5, t1
                  sltu         t4, a2, a6
                  sub          a0, s1, a2
                  slli         t0, s9, 3
                  mul          tp, t2, s11
                  c.and        s0, a5
                  add          s2, tp, a1
                  ori          t4, t2, 916
                  sll          a6, t1, s6
                  c.srli       a2, 19
                  c.srai       s0, 8
                  ori          t1, s6, -223
                  slli         a6, sp, 5
                  srli         zero, t5, 21
                  srli         s5, tp, 4
                  addi         a2, s4, -14
                  la x11, test_done
                  jalr x0, x11, 0
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
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_2:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_3:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_4:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_5:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_6:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_7:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_8:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_9:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_10:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_11:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_12:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_13:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_14:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

mmode_intr_vector_15:
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x342 # MCAUSE
                  srli x9, x9, 0x1f
                  beqz x9, 1f
                  j mmode_intr_handler
                  1: la x11, test_done
                  jalr x0, x11, 0

.align           4
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
                  addi x22, x22, -4
                  sw  x14, (x22)
                  add x14, x22, zero
                  addi x14, x14, -128
                  sw  x1, 4(x14)
                  sw  x2, 8(x14)
                  sw  x3, 12(x14)
                  sw  x4, 16(x14)
                  sw  x5, 20(x14)
                  sw  x6, 24(x14)
                  sw  x7, 28(x14)
                  sw  x8, 32(x14)
                  sw  x9, 36(x14)
                  sw  x10, 40(x14)
                  sw  x11, 44(x14)
                  sw  x12, 48(x14)
                  sw  x13, 52(x14)
                  sw  x14, 56(x14)
                  sw  x15, 60(x14)
                  sw  x16, 64(x14)
                  sw  x17, 68(x14)
                  sw  x18, 72(x14)
                  sw  x19, 76(x14)
                  sw  x20, 80(x14)
                  sw  x21, 84(x14)
                  sw  x22, 88(x14)
                  sw  x23, 92(x14)
                  sw  x24, 96(x14)
                  sw  x25, 100(x14)
                  sw  x26, 104(x14)
                  sw  x27, 108(x14)
                  sw  x28, 112(x14)
                  sw  x29, 116(x14)
                  sw  x30, 120(x14)
                  sw  x31, 124(x14)
                  add x22, x14, zero
                  csrr x9, 0x341 # MEPC
                  csrr x9, 0x342 # MCAUSE
                  li x30, 0x3 # BREAKPOINT
                  beq x9, x30, ebreak_handler
                  li x30, 0x8 # ECALL_UMODE
                  beq x9, x30, ecall_handler
                  li x30, 0x9 # ECALL_SMODE
                  beq x9, x30, ecall_handler
                  li x30, 0xb # ECALL_MMODE
                  beq x9, x30, ecall_handler
                  li x30, 0x1
                  beq x9, x30, instr_fault_handler
                  li x30, 0x5
                  beq x9, x30, load_fault_handler
                  li x30, 0x7
                  beq x9, x30, store_fault_handler
                  li x30, 0xc
                  beq x9, x30, pt_fault_handler
                  li x30, 0xd
                  beq x9, x30, pt_fault_handler
                  li x30, 0xf
                  beq x9, x30, pt_fault_handler
                  li x30, 0x2 # ILLEGAL_INSTRUCTION
                  beq x9, x30, illegal_instr_handler
                  csrr x30, 0x343 # MTVAL
                  1: la x11, test_done
                  jalr x1, x11, 0

ecall_handler:    
                  la x9, _start
                  sw x0, 0(x9)
                  sw x1, 4(x9)
                  sw x2, 8(x9)
                  sw x3, 12(x9)
                  sw x4, 16(x9)
                  sw x5, 20(x9)
                  sw x6, 24(x9)
                  sw x7, 28(x9)
                  sw x8, 32(x9)
                  sw x9, 36(x9)
                  sw x10, 40(x9)
                  sw x11, 44(x9)
                  sw x12, 48(x9)
                  sw x13, 52(x9)
                  sw x14, 56(x9)
                  sw x15, 60(x9)
                  sw x16, 64(x9)
                  sw x17, 68(x9)
                  sw x18, 72(x9)
                  sw x19, 76(x9)
                  sw x20, 80(x9)
                  sw x21, 84(x9)
                  sw x22, 88(x9)
                  sw x23, 92(x9)
                  sw x24, 96(x9)
                  sw x25, 100(x9)
                  sw x26, 104(x9)
                  sw x27, 108(x9)
                  sw x28, 112(x9)
                  sw x29, 116(x9)
                  sw x30, 120(x9)
                  sw x31, 124(x9)
                  la x11, write_tohost
                  jalr x0, x11, 0

instr_fault_handler:
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret

load_fault_handler:
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret

store_fault_handler:
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret

ebreak_handler:   
                  csrr  x9, 0x341
                  addi  x9, x9, 4
                  csrw  0x341, x9
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret

illegal_instr_handler:
                  csrr  x9, 0x341
                  addi  x9, x9, 4
                  csrw  0x341, x9
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret

pt_fault_handler: 
                  nop

.align 2
mmode_intr_handler:
                  csrr  x9, 0x300 # MSTATUS;
                  csrr  x9, 0x304 # MIE;
                  csrr  x9, 0x344 # MIP;
                  csrrc x9, 0x344, x9 # MIP;
                  add x14, x22, zero
                  lw  x1, 4(x14)
                  lw  x2, 8(x14)
                  lw  x3, 12(x14)
                  lw  x4, 16(x14)
                  lw  x5, 20(x14)
                  lw  x6, 24(x14)
                  lw  x7, 28(x14)
                  lw  x8, 32(x14)
                  lw  x9, 36(x14)
                  lw  x10, 40(x14)
                  lw  x11, 44(x14)
                  lw  x12, 48(x14)
                  lw  x13, 52(x14)
                  lw  x14, 56(x14)
                  lw  x15, 60(x14)
                  lw  x16, 64(x14)
                  lw  x17, 68(x14)
                  lw  x18, 72(x14)
                  lw  x19, 76(x14)
                  lw  x20, 80(x14)
                  lw  x21, 84(x14)
                  lw  x22, 88(x14)
                  lw  x23, 92(x14)
                  lw  x24, 96(x14)
                  lw  x25, 100(x14)
                  lw  x26, 104(x14)
                  lw  x27, 108(x14)
                  lw  x28, 112(x14)
                  lw  x29, 116(x14)
                  lw  x30, 120(x14)
                  lw  x31, 124(x14)
                  addi x14, x14, 128
                  add x22, x14, zero
                  lw  x14, (x22)
                  addi x22, x22, 4
                  mret;

kernel_instr_end: nop
.section .kernel_stack,"aw",@progbits;
.align 2
kernel_stack_start:
.rept 3999
.4byte 0x0
.endr
kernel_stack_end:
.4byte 0x0
