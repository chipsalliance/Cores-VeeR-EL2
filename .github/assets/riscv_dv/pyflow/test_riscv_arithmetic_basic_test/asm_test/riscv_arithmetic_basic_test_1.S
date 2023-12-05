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
                  li x24, 0x40001104
                  csrw 0x301, x24
kernel_sp:        
                  la x30, kernel_stack_end

trap_vec_init:    
                  la x24, mtvec_handler
                  ori x24, x24, 1
                  csrw 0x305, x24 # MTVEC

mepc_setup:       
                  la x24, init
                  csrw 0x341, x24

init_machine_mode:
                  li x24, 0x1c00
                  csrw 0x300, x24 # MSTATUS
                  li x24, 0x0
                  csrw 0x304, x24 # MIE
                  mret
init:             
                  li x0, 0xfc7f95d1
                  li x1, 0x80000000
                  li x2, 0x0
                  li x3, 0xf5b5b89a
                  li x4, 0xf7918cab
                  li x5, 0xf839172f
                  li x6, 0x9
                  li x7, 0xb
                  li x8, 0x80000000
                  li x9, 0x3fbd44a9
                  li x10, 0x80000000
                  li x11, 0x6
                  li x12, 0x1
                  li x13, 0x0
                  li x14, 0x0
                  li x15, 0xb
                  li x16, 0x80000000
                  li x17, 0x0
                  li x18, 0x80000000
                  li x19, 0x99e45547
                  li x20, 0x80000000
                  li x21, 0x1
                  li x22, 0x0
                  li x23, 0x265c7bf1
                  li x24, 0x8
                  li x25, 0x97eb0431
                  li x26, 0xf23fb98e
                  li x28, 0x80000000
                  li x29, 0x0
                  li x31, 0xc
                  la x27, user_stack_end
main:             li         s6, 0x0 #start riscv_int_numeric_corner_stream_19
                  li         t3, 0x1
                  li         s10, 0x0
                  li         a4, 0x0
                  li         t4, 0x1
                  li         sp, 0x1
                  li         s9, 0xd63bd56
                  li         gp, 0x60cd8746
                  li         s4, 0x0
                  li         s1, 0x1
                  c.nop
                  c.add       a2, ra
                  c.lui       s7, 12
                  c.mv        a5, s0
                  mulhsu      zero, ra, a3
                  c.lui       a7, 4
                  rem         t2, tp, t6
                  sub         s5, a4, t0
                  mulhu       a3, a4, sp
                  c.add       s1, s4
                  sub         a1, s5, zero
                  c.add       ra, sp
                  mulhu       t1, a7, a5
                  addi        s5, s7, -1427
                  auipc       gp, 339567
                  div         s4, a4, s11
                  c.lui       s3, 12
                  nop
                  addi        t3, a1, -425 #end riscv_int_numeric_corner_stream_19
                  li         a3, 0x1 #start riscv_int_numeric_corner_stream_3
                  li         s5, 0x1c8f3f24
                  li         t4, 0x1
                  li         t0, 0x0
                  li         s9, 0x1
                  li         s1, 0x1
                  li         sp, 0x1
                  li         a1, 0x1
                  li         t3, 0x0
                  li         s4, 0x6c11a4cd
                  sub         a2, t5, a7
                  divu        t1, t5, s5
                  c.mv        a7, t4
                  c.mv        ra, s9
                  divu        t0, s2, s8
                  c.addi      t4, 10
                  div         s4, t5, a2
                  mulh        a4, s10, tp
                  mulhu       s3, ra, sp
                  addi        s3, s0, -988
                  addi        a5, a4, -2010
                  nop
                  c.addi16sp  sp, 48
                  c.mv        s1, tp
                  c.lui       s6, 29
                  c.add       a4, s0
                  addi        a6, a0, 1224 #end riscv_int_numeric_corner_stream_3
                  li         a4, 0x0 #start riscv_int_numeric_corner_stream_22
                  li         t4, 0x0
                  li         t3, 0x123dd690
                  li         s10, 0x0
                  li         s9, 0x65a3f0a3
                  li         s7, 0x75084d6a
                  li         a2, 0x0
                  li         a3, 0x0
                  li         t2, 0x66e2867c
                  li         s8, 0x1
                  lui         s5, 1044291
                  auipc       t3, 412720
                  mul         zero, a4, a2
                  c.addi      a5, 15
                  rem         zero, a6, s10
                  c.addi      t1, 6
                  mulhu       a7, a3, t4
                  nop
                  nop
                  auipc       s8, 422718
                  nop
                  mulhsu      t4, s0, a0
                  sub         s7, a0, s2
                  lui         s1, 1945
                  c.sub       a3, a5
                  div         s7, s4, tp
                  auipc       a7, 4458
                  addi        s7, t4, 38
                  c.addi      a1, -1
                  mulhsu      s2, a5, a6
                  c.nop
                  sub         zero, s11, t2 #end riscv_int_numeric_corner_stream_22
                  li         a2, 0x37d477 #start riscv_int_numeric_corner_stream_8
                  li         t4, 0x14536013
                  li         t3, 0x1
                  li         s7, 0x0
                  li         tp, 0x0
                  li         a3, 0x1
                  li         s5, 0x1
                  li         a4, 0x0
                  li         t0, 0x1
                  li         a5, 0x0
                  rem         a2, tp, a2
                  mulhu       s8, t6, t4
                  c.sub       a3, a3
                  add         t4, s8, t6
                  divu        s1, t1, s3
                  div         sp, tp, a3
                  nop
                  rem         a2, s8, a0
                  c.addi4spn  a4, sp, 832
                  c.li        tp, -1
                  mulhu       s4, a5, a0
                  nop
                  lui         ra, 868060
                  c.mv        a7, a2
                  c.add       ra, ra
                  sub         zero, s2, t6 #end riscv_int_numeric_corner_stream_8
                  li         t4, 0x7fe1d071 #start riscv_int_numeric_corner_stream_25
                  li         t3, 0x0
                  li         s10, 0x1
                  li         s8, 0x67dfb841
                  li         s9, 0x0
                  li         a0, 0x0
                  li         s2, 0x1
                  li         a5, 0x4248dea5
                  li         s3, 0x0
                  li         a7, 0x0
                  c.lui       a3, 6
                  divu        t3, gp, s11
                  mulhu       ra, t1, t3
                  c.add       a6, s11
                  c.add       sp, a7
                  c.lui       ra, 15
                  addi        a0, s8, -821
                  lui         t4, 455371
                  c.sub       a3, a3
                  c.sub       a0, a3
                  lui         a2, 896673
                  auipc       s0, 873181
                  add         a4, t1, ra
                  c.addi      ra, 13
                  mulh        zero, s6, t5
                  mul         s5, s3, s6
                  sub         s8, a5, a2
                  mul         t3, t4, a6
                  divu        a7, t6, t1
                  c.sub       a3, a3
                  li         s4, 0x0 #start riscv_int_numeric_corner_stream_9
                  li         s1, 0x0
                  li         t4, 0x1
                  li         t3, 0x0
                  li         a3, 0x20e3ee8
                  li         t1, 0x0
                  li         s8, 0x35e9a07b
                  li         a2, 0x1af8309e
                  li         s9, 0x0
                  li         s5, 0x1
                  auipc       tp, 998505
                  c.addi      a4, 1
                  c.nop
                  mulhu       t3, t1, s8
                  auipc       t2, 788962
                  c.addi16sp  sp, 128
                  add         zero, s0, a2
                  mulh        s9, s6, t2
                  c.addi4spn  a5, sp, 832
                  nop
                  addi        s9, a3, 1137
                  rem         s10, s8, a6
                  c.addi      a4, 16
                  c.lui       t4, 1
                  c.add       s1, tp
                  addi        sp, s11, 380
                  mulhu       s6, ra, s7
                  add         zero, zero, t0
                  mulhsu      s0, s3, t4 #end riscv_int_numeric_corner_stream_9
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_21
                  li         s9, 0x0
                  li         s1, 0x0
                  li         t3, 0x1
                  li         s10, 0x1
                  li         a0, 0x0
                  li         s8, 0x0
                  li         a6, 0x0
                  li         a1, 0x1
                  li         s2, 0x5b0d5887
                  c.add       t2, tp
                  c.nop
                  auipc       zero, 43049
                  lui         s1, 413670
                  c.addi16sp  sp, -16
                  mul         zero, s4, a1
                  c.nop
                  c.add       t2, a7
                  addi        a3, t1, 393
                  mulhsu      s8, gp, a2
                  divu        a4, s5, s2
                  add         t0, a0, t1
                  c.addi      ra, -1
                  rem         t1, a7, t2
                  divu        s8, a3, a0
                  auipc       a6, 392758
                  mul         s4, a2, a4
                  mulhsu      t2, s9, t5
                  c.add       s2, s0
                  sub         a1, s5, s6
                  c.addi16sp  sp, 336
                  c.li        t4, -1
                  c.nop
                  c.addi16sp  sp, -16
                  sub         a5, a7, t1
                  c.addi16sp  sp, -16
                  c.sub       a3, a3
                  mul         a7, a3, a4 #end riscv_int_numeric_corner_stream_21
                  li         t4, 0x6f02ff5a #start riscv_int_numeric_corner_stream_17
                  li         s7, 0x0
                  li         t3, 0x2407418a
                  li         s10, 0x3031957d
                  li         s1, 0x0
                  li         s0, 0x3c68c83f
                  li         a0, 0x0
                  li         s8, 0x7adb72c2
                  li         a1, 0x0
                  li         a4, 0x1
                  lui         gp, 170942
                  c.add       gp, gp
                  c.mv        ra, a1
                  c.add       t1, a0
                  mulhu       a6, s3, a0
                  c.nop
                  mulhu       s4, s8, s4
                  mulh        t0, s10, ra
                  rem         a6, s6, s10
                  c.addi16sp  sp, -16
                  c.li        ra, -1
                  rem         tp, s7, a5
                  addi        zero, a2, 1636
                  divu        s9, s5, t0
                  c.addi16sp  sp, -16
                  mulh        t4, s11, s9
                  c.sub       a3, a3
                  mul         a2, s7, t0
                  rem         t4, s0, s8
                  c.li        ra, 21
                  c.li        ra, 4
                  c.addi16sp  sp, -16
                  c.sub       a3, a3
                  div         s3, a1, gp
                  c.addi      a5, -1
                  c.addi4spn  a3, sp, 320
                  c.add       s7, s0
                  li         t4, 0x4fe94cd1 #start riscv_int_numeric_corner_stream_10
                  li         s9, 0x1
                  li         t3, 0x1
                  li         ra, 0x0
                  li         s8, 0x0
                  li         s0, 0x51119311
                  li         a0, 0x1
                  li         s4, 0x0
                  li         a6, 0x0
                  li         s3, 0x1
                  mul         s5, sp, a0
                  c.addi      s6, 2
                  lui         t1, 425085
                  sub         s4, a2, t3
                  div         s2, s5, s1
                  mulh        a3, s7, a2
                  mulhu       s4, s7, ra
                  mulhsu      tp, s2, t4
                  add         t4, gp, s3
                  mulhu       t4, s5, tp
                  c.addi      s6, -1
                  mulhsu      s2, a3, a0
                  add         zero, t3, t0
                  c.addi      s9, 6
                  c.mv        gp, s11
                  mulhu       s7, s1, s11
                  mul         ra, s3, a7
                  sub         zero, a2, t1
                  c.sub       a0, a3
                  c.lui       ra, 10
                  addi        a7, a6, -274
                  c.lui       t4, 11
                  c.addi4spn  a3, sp, 576
                  addi        s9, t1, -644
                  add         ra, tp, s2 #end riscv_int_numeric_corner_stream_10
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_2
                  li         t3, 0x0
                  li         a2, 0x2083332
                  li         s5, 0x1
                  li         a4, 0x0
                  li         s8, 0x1
                  li         gp, 0x1
                  li         tp, 0x4da989d9
                  li         a3, 0x1
                  li         a7, 0x1
                  nop
                  c.addi      s8, 7
                  c.mv        s3, s3
                  mulh        zero, s9, sp
                  c.addi      a7, 18
                  mul         zero, a5, t5
                  c.lui       s3, 24
                  mulh        a0, a2, s6
                  mulhsu      t3, t2, s5
                  c.addi      tp, 13
                  c.lui       ra, 11
                  divu        s2, a7, a5
                  divu        a0, t1, s10
                  add         a5, a1, s6
                  c.addi4spn  a0, sp, 832
                  c.li        sp, -1
                  add         s4, a3, sp
                  div         zero, a3, t5
                  mulh        s3, sp, s4
                  c.lui       s4, 27
                  lui         ra, 748049
                  mul         s2, s9, s5
                  addi        t2, t1, 1455
                  c.li        t2, -1
                  c.mv        a2, a5
                  c.add       t3, a3
                  c.addi      t1, -1
                  mul         s6, t2, a4
                  c.addi16sp  sp, -16
                  li         t4, 0x445f7f9 #start riscv_int_numeric_corner_stream_0
                  li         t3, 0x0
                  li         s10, 0x0
                  li         s8, 0x0
                  li         s2, 0x0
                  li         a4, 0x1
                  li         a0, 0x1
                  li         sp, 0x0
                  li         a1, 0x18cd3cad
                  li         s9, 0x58cc2b6a
                  auipc       s6, 699844
                  c.li        s2, 26
                  c.mv        sp, gp
                  nop
                  c.nop
                  c.mv        a7, a1
                  nop
                  addi        s10, a0, -840
                  c.sub       a4, a3
                  c.lui       s10, 15
                  mulhu       a1, sp, s6
                  mulh        a1, a4, t2
                  sub         s8, s8, zero
                  mul         a2, s11, s7
                  mulhu       s7, a6, s6
                  c.nop
                  lui         t1, 994979
                  mulh        s6, s3, t1
                  c.addi4spn  a3, sp, 608
                  c.addi      ra, 20
                  c.addi16sp  sp, -16
                  sub         t1, s8, s11
                  auipc       zero, 643033
                  add         ra, s6, tp
                  addi        t0, tp, -881 #end riscv_int_numeric_corner_stream_0
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_16
                  li         t3, 0x0
                  li         s10, 0x1
                  li         a1, 0x1
                  li         s9, 0x0
                  li         a0, 0x0
                  li         t2, 0x0
                  li         s8, 0x0
                  li         t0, 0x0
                  li         s7, 0x0
                  div         t1, t1, t3
                  c.addi      t1, -1
                  c.lui       ra, 16
                  div         tp, t6, t3
                  c.nop
                  c.addi      s2, 22
                  c.addi      s3, -1
                  c.sub       a5, a3
                  c.lui       s5, 21
                  c.lui       s9, 4
                  nop
                  c.mv        ra, s11
                  c.addi4spn  a3, sp, 832
                  c.li        t1, 30
                  div         a3, t2, s0
                  c.add       a5, a7
                  nop
                  c.mv        ra, tp
                  mulh        t4, a7, a3
                  sub         s6, zero, a5
                  mulh        sp, s4, a1
                  c.addi16sp  sp, -16
                  c.addi16sp  sp, 336
                  lui         zero, 828936
                  c.lui       s10, 10
                  nop
                  andi        a6, s8, -2000
                  c.or        a3, s0
                  c.and       a3, a3
                  c.and       a3, a3
                  c.addi      t2, 4
                  c.nop
                  sltiu       a6, s10, 1169
                  c.srai      a3, 15
                  addi        a3, t6, -155
                  and         s7, s8, a2
                  divu        a1, s7, s4
                  c.addi4spn  a3, sp, 384
                  lui         a0, 348794
                  c.addi4spn  a3, sp, 896
                  sltu        zero, t1, t1
                  andi        s2, s0, 1537
                  sll         tp, s4, sp
                  sltu        s9, a1, s1
                  auipc       zero, 377242
                  ori         a1, a0, -1749
                  or          zero, t6, a6
                  c.li        a4, 3
                  slli        s8, s4, 29
                  nop
                  c.or        a3, a3
                  c.andi      a3, 3
                  xori        sp, s10, -1231
                  and         s10, t2, a3
                  sltu        t1, s3, t3
                  xori        a3, zero, 1766
                  xor         a7, sp, ra
                  c.addi4spn  a3, sp, 640
                  c.or        a3, a3
                  c.xor       s1, a3
                  c.srli      a3, 13
                  sltiu       a4, s3, -358
                  srai        t4, t6, 1
                  div         s8, s10, s9
                  xori        zero, s4, -1725
                  c.nop
                  c.and       a5, a3
                  mulhsu      a3, s2, s3
                  sub         ra, a0, t1
                  c.and       a5, a3
                  slt         s5, s4, a1
                  c.srai      a3, 13
                  mulhsu      a1, a1, s8
                  rem         zero, s8, s8
                  c.andi      a3, 3
                  mulh        s1, s5, gp
                  divu        t4, a0, a6
                  slli        s8, s11, 24
                  divu        a5, ra, s9
                  mulh        zero, s9, t5
                  or          s6, s9, s6
                  c.mv        t4, a0
                  c.srli      a3, 19
                  auipc       ra, 277376
                  c.srli      a3, 25
                  c.sub       a3, a3
                  slli        t2, s6, 10
                  nop
                  xori        tp, s10, 1920
                  lui         s5, 1002459
                  c.or        a3, a3
                  c.srli      a3, 8
                  sub         gp, s10, s4
                  divu        s3, ra, gp
                  sub         a2, a0, t0
                  or          a5, a1, s6
                  xori        s2, s6, -52
                  c.andi      a3, -1
                  sll         ra, t0, s1
                  c.andi      a3, 5
                  sltiu       s9, s4, -540
                  c.sub       a1, a3
                  slt         t0, s7, s5
                  mulhu       s8, s7, a6
                  c.nop
                  slti        t0, zero, -1580
                  auipc       s0, 76054
                  add         gp, s5, ra
                  sltu        t3, s3, s10
                  c.and       a3, a3
                  c.addi4spn  s0, sp, 320
                  c.xor       a3, a3
                  c.srli      a1, 23
                  slti        s9, a5, -1421
                  and         s4, zero, a6
                  addi        a7, zero, 2013
                  sub         t1, s3, s9
                  sub         a1, zero, s0
                  c.mv        t3, s11
                  xor         s4, a4, t4
                  or          sp, a6, s4
                  c.or        a3, a3
                  lui         t0, 373917
                  c.and       a3, a3
                  c.addi4spn  a3, sp, 576
                  and         zero, s11, a0
                  auipc       t1, 820967
                  divu        s0, s5, a7
                  c.srai      a3, 6
                  c.nop
                  addi        a6, t1, 1312
                  div         t1, sp, t5
                  c.mv        a3, a4
                  lui         ra, 936092
                  c.mv        ra, a6
                  c.andi      a3, -1
                  c.nop
                  c.addi      t3, -1
                  c.addi16sp  sp, 160
                  mulhsu      tp, a7, t6
                  c.sub       a3, a3
                  mulhsu      a3, s0, s2
                  sltiu       s4, s7, 1860
                  srl         a0, ra, zero
                  c.or        a3, s1
                  c.addi      ra, 6
                  c.lui       t0, 25
                  rem         zero, sp, s3
                  srli        tp, sp, 21
                  mulhu       a2, zero, zero
                  addi        tp, s7, -1383
                  c.li        ra, 30
                  xor         s8, a3, a5
                  c.nop
                  c.srai      a3, 15
                  slli        a0, s9, 4
                  addi        s1, s7, -1389
                  c.andi      a3, 17
                  or          zero, s0, a3
                  srli        s5, sp, 4
                  c.add       a1, s4
                  c.srli      a3, 16
                  rem         a0, s5, t6
                  c.addi      ra, 26
                  c.li        ra, 15
                  nop
                  c.sub       a3, a3
                  lui         a6, 614823
                  mulh        a4, a4, t2
                  slt         s9, t3, s11
                  ori         s10, t5, -1900
                  c.add       gp, tp
                  c.addi16sp  sp, -16
                  c.addi      ra, 8
                  c.and       a2, a3
                  auipc       s3, 495028
                  mulhu       a4, s6, a7
                  addi        a7, zero, 1771
                  c.addi16sp  sp, 208
                  c.lui       s3, 24
                  rem         zero, s10, t3
                  add         zero, a3, a0
                  sltiu       a4, s8, 1957
                  mul         t2, s3, a1
                  slli        sp, a5, 13
                  c.and       a3, a3
                  slti        a1, s11, 1494
                  c.li        ra, 5
                  c.andi      a4, -1
                  ori         a3, s4, -619
                  sub         s7, s6, tp
                  mulhu       t1, a7, a3
                  nop
                  slti        s0, a1, 1389
                  sra         s5, t5, t0
                  c.addi      s1, 5
                  c.or        a3, a0
                  srl         zero, s6, sp
                  c.addi4spn  a3, sp, 192
                  c.li        a4, -1
                  sll         a6, s10, s4
                  lui         gp, 468341
                  add         a0, a6, zero
                  lui         tp, 700810
                  addi        s10, t1, -684
                  addi        t0, s2, -1213
                  srl         t2, s3, a4
                  c.srli      a3, 22
                  c.andi      a3, -1
                  nop
                  and         t3, s0, s3
                  sltiu       s7, tp, 2011
                  slti        tp, s1, -440
                  nop
                  xori        zero, s3, -1124
                  mul         tp, t0, s4
                  xor         zero, a3, t4
                  c.nop
                  c.xor       a3, a3
                  c.addi4spn  a3, sp, 96
                  sra         s6, a3, t0
                  sll         a6, t4, t2
                  c.srai      a3, 24
                  c.addi      s4, -1
                  c.addi4spn  a3, sp, 192
                  c.addi4spn  a3, sp, 64
                  sltu        t3, t4, zero
                  c.lui       s9, 17
                  c.nop
                  or          a1, a0, t6
                  xor         a6, s1, zero
                  mulh        s10, s0, a5
                  divu        zero, zero, t1
                  and         a7, s1, s7
                  c.addi16sp  sp, -16
                  sra         s1, tp, s2
                  xori        a3, t4, -1888
                  sltu        s4, ra, t2
                  c.sub       a3, a3
                  c.addi      ra, 27
                  add         s6, t6, gp
                  c.add       a3, t1
                  slt         t1, tp, a1
                  c.srli      a3, 7
                  c.li        ra, -1
                  div         s8, a2, s7
                  c.andi      a2, 26
                  srai        a4, a5, 24
                  c.srli      a3, 18
                  c.sub       a3, a4
                  c.andi      a3, -1
                  c.mv        s9, t4
                  sra         zero, a4, s3
                  sll         s0, a3, t2
                  mul         zero, ra, a6
                  lui         ra, 233915
                  sll         zero, s10, a3
                  slti        s0, s6, -21
                  mul         a1, s9, s4
                  sub         s7, gp, s1
                  auipc       s5, 1002872
                  c.and       a3, a3
                  mul         zero, t5, gp
                  sub         s7, a3, a3
                  sub         s5, s5, s8
                  sub         s0, s7, a1
                  lui         s10, 975489
                  mul         t4, s8, t1
                  slti        s9, t0, -1840
                  c.li        t1, -1
                  ori         s8, t4, -784
                  slli        a2, a4, 8
                  c.xor       a3, a3
                  andi        s7, t4, -107
                  c.sub       a1, a3
                  slt         t0, s7, a2
                  lui         zero, 58581
                  c.lui       s2, 10
                  mul         t0, s6, t3
                  add         a4, ra, s3
                  addi        s3, gp, 1119
                  or          a6, t5, ra
                  c.sub       a3, a4
                  c.li        ra, 10
                  c.and       a3, a3
                  andi        s8, s9, -1568
                  xor         a1, a2, a2
                  sltu        a2, t1, t2
                  mulhu       zero, sp, t4
                  srl         t1, t5, tp
                  add         a4, s3, t3
                  c.slli      ra, 18
                  c.mv        gp, gp
                  ori         s4, s10, 1444
                  rem         zero, s3, s3
                  mul         a7, a3, s6
                  c.addi16sp  sp, -16
                  c.mv        a6, ra
                  c.or        a3, a3
                  nop
                  mulhsu      a6, a5, a3
                  c.addi4spn  a3, sp, 640
                  div         a1, t5, a0
                  auipc       s8, 750692
                  slli        s6, a7, 2
                  srai        a7, sp, 20
                  srli        a5, s7, 21
                  sra         zero, gp, a7
                  c.mv        a1, ra
                  c.addi16sp  sp, -16
                  c.slli      s4, 19
                  and         s10, a4, s8
                  sltiu       s8, a4, 33
                  sltiu       t2, sp, -194
                  auipc       s6, 459473
                  sll         a6, ra, a7
                  c.xor       a3, s0
                  slli        a6, s2, 29
                  c.andi      a3, -1
                  slli        s2, sp, 24
                  srai        zero, sp, 25
                  sltiu       tp, s6, -1582
                  c.lui       a0, 10
                  xori        zero, a6, 22
                  xor         s6, a6, s11
                  mul         t1, s10, a7
                  sll         s9, a2, a3
                  c.xor       a4, a3
                  srai        gp, sp, 10
                  c.srli      a3, 8
                  mulh        a3, s1, s3
                  mul         s0, ra, s3
                  ori         s0, s1, 452
                  addi        a5, s4, -944
                  sltiu       zero, a4, -1626
                  rem         a2, tp, s2
                  mulhu       t0, s2, s9
                  ori         a1, tp, -1737
                  or          t4, a2, s8
                  c.srai      a3, 13
                  nop
                  c.addi4spn  a3, sp, 192
                  mulhu       s7, s10, sp
                  c.li        tp, 8
                  c.lui       gp, 14
                  c.lui       ra, 11
                  c.mv        a5, a0
                  and         tp, t4, a1
                  auipc       s9, 419839
                  sltiu       a7, t1, 1212
                  sll         t3, s7, tp
                  nop
                  add         s0, a3, t3
                  c.lui       t4, 24
                  c.slli      a6, 9
                  slli        t2, a3, 7
                  nop
                  mul         s9, t1, a0
                  sltu        s7, t3, a3
                  ori         tp, a2, 447
                  c.slli      s8, 23
                  sll         t4, a6, s7
                  c.addi4spn  a3, sp, 576
                  xor         gp, tp, t5
                  rem         t0, s7, s9
                  c.xor       a4, a3
                  lui         s2, 292974
                  or          s6, tp, s11
                  lui         s3, 496998
                  c.sub       a3, a1
                  c.addi16sp  sp, 496
                  nop
                  and         s7, s0, a7
                  xor         t2, a3, t1
                  c.sub       a3, a5
                  mul         s8, t6, tp
                  mul         s3, s1, t2
                  c.srai      a3, 6
                  c.mv        a6, t6
                  srai        a7, a7, 21
                  c.or        a3, a3
                  srli        ra, a4, 10
                  sltu        tp, s4, t1
                  c.addi16sp  sp, 464
                  c.slli      s6, 22
                  mulh        a5, s4, s4
                  c.addi      sp, 15
                  or          zero, s10, a6
                  sub         a7, t1, gp
                  rem         t0, s3, a0
                  nop
                  add         zero, a1, a4
                  c.lui       s2, 15
                  c.and       s1, a3
                  sltu        t3, t5, t1
                  srai        ra, a3, 3
                  auipc       s7, 900687
                  div         t1, t4, s11
                  addi        a1, ra, -1760
                  and         zero, s8, s9
                  sltu        sp, gp, a2
                  srli        zero, t3, 3
                  add         sp, s2, s10
                  mulh        tp, gp, s3
                  c.addi      s7, 21
                  c.addi      s9, -1
                  rem         s0, gp, zero
                  c.srli      s1, 11
                  mulhu       s5, a3, s6
                  xori        zero, a4, 516
                  xori        zero, t2, -959
                  c.mv        t1, tp
                  c.srai      a3, 26
                  xor         zero, a0, s6
                  sub         s5, a7, sp
                  c.andi      s0, 14
                  c.lui       s0, 5
                  c.slli      s8, 31
                  and         sp, s2, t1
                  c.li        s7, 22
                  c.addi4spn  a3, sp, 240
                  andi        t1, s0, -1225
                  andi        s9, s2, 1442
                  c.srli      a2, 16
                  c.and       a3, a3
                  c.xor       a3, s0
                  c.srai      a3, 22
                  and         s3, a5, s8
                  c.and       a3, a3
                  c.srai      a3, 23
                  sra         a6, a3, s5
                  ori         t4, t3, 753
                  srai        s3, s10, 30
                  sltiu       s8, s9, -450
                  c.andi      a3, 20
                  xori        t3, a3, -1148
                  srai        s1, zero, 19
                  srl         a5, s9, zero
                  mulhsu      s8, s7, a1
                  add         s1, a5, s6
                  nop
                  srli        s5, s2, 17
                  sub         t4, t0, t3
                  andi        s3, s11, 1882
                  sltiu       a3, a5, -1658
                  ori         t4, sp, 1908
                  mulhsu      t2, t6, s1
                  sub         s2, s5, a2
                  lui         s1, 119797
                  slli        t2, s8, 21
                  sra         gp, gp, s3
                  c.srli      s0, 5
                  c.addi16sp  sp, 368
                  srli        s0, a4, 17
                  mul         a4, a7, s10
                  c.and       a3, a3
                  rem         gp, s7, a1
                  c.addi16sp  sp, -16
                  and         gp, s9, zero
                  c.or        a3, a3
                  slli        zero, s1, 25
                  srli        s0, s8, 8
                  nop
                  c.sub       a3, a4
                  c.sub       a3, a3
                  c.add       ra, s4
                  sra         a4, s11, sp
                  c.xor       a3, a5
                  slt         gp, a3, s3
                  c.addi16sp  sp, 176
                  andi        s3, s8, 51
                  sra         s2, s2, s5
                  mulhsu      tp, zero, s2
                  c.addi4spn  s1, sp, 832
                  addi        sp, t0, -1447
                  srai        s0, a5, 15
                  c.add       s3, t2
                  sra         ra, zero, t5
                  mulhsu      t4, a1, s5
                  add         s9, s5, t1
                  c.srai      a3, 1
                  rem         zero, a7, a7
                  c.li        a2, 1
                  c.addi16sp  sp, -16
                  c.li        s4, 25
                  mul         a7, s10, t4
                  c.and       a3, s1
                  sltiu       s2, s2, 1806
                  divu        zero, s9, a6
                  c.addi      s5, 14
                  srli        s5, zero, 31
                  slt         s3, a2, sp
                  c.addi      tp, -1
                  mul         t2, s6, sp
                  sll         a7, a4, t2
                  mulh        s8, s10, s1
                  mul         zero, s9, a5
                  auipc       ra, 638824
                  sra         s3, t0, t2
                  mulhu       t3, s10, a3
                  sra         zero, t2, s10
                  c.srai      a2, 1
                  lui         a2, 373328
                  c.sub       a3, a1
                  sll         s1, zero, a5
                  c.addi      t3, 18
                  sltu        a1, gp, s11
                  srli        t1, s5, 1
                  addi        s8, s2, -993
                  auipc       s8, 461872
                  srl         tp, a2, t6
                  add         s4, s5, t0
                  c.srai      a3, 5
                  c.srai      a4, 4
                  slli        t3, a7, 8
                  c.lui       s1, 31
                  c.slli      t1, 23
                  c.or        a5, a0
                  c.xor       a3, a3
                  mulh        s5, t2, t1
                  c.xor       a3, a1
                  c.li        ra, 17
                  add         a7, s11, a4
                  or          gp, a6, ra
                  or          zero, t2, t4
                  lui         s10, 272668
                  mulh        ra, a4, s3
                  c.or        a3, a3
                  ori         zero, a5, -1169
                  divu        s8, s8, a0
                  c.srli      a3, 12
                  nop
                  c.add       gp, s5
                  slt         a0, t2, ra
                  xor         t3, a6, t0
                  c.addi4spn  a3, sp, 896
                  c.li        a2, -1
                  c.andi      a3, -1
                  andi        a5, sp, -107
                  c.srli      a0, 11
                  sll         s1, t4, a5
                  slt         s6, sp, s0
                  add         t2, sp, a5
                  addi        zero, s4, 841
                  c.srai      a3, 20
                  sltiu       a4, a6, 1806
                  c.slli      tp, 3
                  slti        zero, zero, -1841
                  rem         a2, s8, a3
                  ori         zero, ra, 1626
                  slt         a7, t0, a2
                  mulhsu      a7, a7, t4
                  c.sub       a3, a3
                  c.srai      a3, 4
                  c.addi      ra, -1
                  rem         t4, s6, t4
                  srl         a2, sp, a5
                  lui         tp, 686115
                  and         t0, a4, s5
                  srli        a6, a2, 21
                  div         s1, sp, zero
                  auipc       zero, 174240
                  or          s1, s8, s9
                  xor         a6, ra, t1
                  c.nop
                  xor         gp, t3, a4
                  c.li        s7, 21
                  mulhsu      s2, tp, t3
                  c.andi      a3, -1
                  sub         s10, a1, s11
                  c.or        a3, a3
                  c.andi      a3, 15
                  c.slli      a7, 8
                  ori         s8, s10, 643
                  sra         s5, s6, gp
                  add         t2, s9, s8
                  c.sub       a3, a3
                  xori        t0, s7, -61
                  c.add       a1, t2
                  and         zero, sp, t0
                  c.srai      a3, 22
                  rem         zero, t0, s1
                  c.xor       a3, a3
                  andi        a7, s2, -1205
                  divu        s10, s8, s8
                  c.lui       s5, 24
                  c.addi      gp, 21
                  sra         s0, a0, s3
                  mulhsu      a6, a1, a0
                  c.addi4spn  a3, sp, 80
                  or          s0, s2, t2
                  add         zero, s6, s8
                  sub         a1, s8, a5
                  srl         sp, ra, t2
                  c.srli      a1, 28
                  c.lui       a7, 17
                  slt         sp, t2, a3
                  c.andi      a3, -1
                  andi        zero, a1, -1628
                  xori        t4, t4, -562
                  mulhu       a4, a6, s2
                  c.addi4spn  a3, sp, 832
                  xor         t4, a7, s6
                  sltiu       a7, s8, 671
                  srl         zero, gp, zero
                  and         s2, a1, s2
                  sltiu       a0, tp, -1763
                  and         ra, gp, zero
                  xor         s9, s7, t0
                  c.li        s0, -1
                  c.srai      a3, 12
                  slt         s3, s4, a4
                  add         s1, a6, t0
                  divu        a7, s2, t2
                  sltiu       a6, s3, 898
                  c.lui       s7, 1
                  slli        a2, a2, 25
                  add         a0, s7, a0
                  divu        zero, s4, s3
                  c.xor       a3, a3
                  srai        ra, gp, 0
                  c.addi16sp  sp, 176
                  rem         s2, t2, s4
                  sra         ra, t2, a4
                  lui         gp, 809461
                  c.mv        a0, a5
                  nop
                  addi        s3, s10, -1700
                  c.addi4spn  a3, sp, 128
                  addi        t2, s0, 1190
                  mulh        t1, t3, a0
                  or          t3, a3, a2
                  xor         s4, sp, a5
                  srl         s5, tp, zero
                  c.addi16sp  sp, -16
                  nop
                  c.andi      s1, -1
                  slti        a1, t3, -1528
                  divu        t4, a6, a1
                  c.addi16sp  sp, -16
                  lui         a3, 528362
                  ori         a3, s0, 1152
                  c.addi      t3, -1
                  sub         s8, tp, s1
                  xori        s4, s9, -986
                  andi        zero, gp, -1545
                  c.sub       a3, a3
                  mulhu       t4, a2, t0
                  andi        a1, s6, 1053
                  c.slli      t4, 30
                  mulhu       t4, s0, t6
                  add         s3, t4, a2
                  divu        zero, a7, gp
                  sltu        sp, t1, s3
                  mulhu       sp, s2, a1
                  sltu        s7, t4, s7
                  addi        a2, gp, -1675
                  and         zero, zero, s0
                  or          s0, a3, s11
                  rem         a0, t6, s3
                  mulhsu      a6, s4, zero
                  lui         a6, 670981
                  c.sub       a3, a3
                  sub         a1, a2, s2
                  or          t2, s8, s6
                  c.addi16sp  sp, 96
                  c.addi16sp  sp, -16
                  c.and       a3, a1
                  c.mv        t2, s9
                  andi        t1, a1, 1786
                  auipc       t4, 596573
                  c.mv        t1, s0
                  div         t0, a7, sp
                  mulhsu      s3, zero, zero
                  andi        t0, a7, -481
                  mulhu       a0, gp, t3
                  add         s7, t2, t3
                  mul         s1, s10, a5
                  sll         s3, a1, t2
                  c.xor       a3, a3
                  slt         sp, t2, t4
                  lui         a0, 241601
                  xori        s4, s2, 202
                  c.addi4spn  a4, sp, 640
                  slt         s0, s3, ra
                  c.nop
                  lui         t2, 156800
                  lui         a6, 1279
                  c.addi      s0, -1
                  divu        t1, ra, s9
                  xori        t2, s9, 1788
                  addi        t4, a6, 206
                  srai        t3, a0, 16
                  c.srli      a3, 19
                  slt         zero, s0, a4
                  sll         a2, ra, zero
                  mul         a3, a5, t3
                  c.li        s10, -1
                  c.add       ra, s4
                  mul         s9, t3, s2
                  nop
                  c.li        s6, 28
                  ori         a2, s3, 530
                  c.addi4spn  a3, sp, 640
                  sra         s7, s5, s6
                  and         tp, t6, a1
                  c.nop
                  xor         s8, s4, a5
                  add         zero, s2, t1
                  lui         t2, 667587
                  srai        s4, s3, 11
                  c.mv        gp, t2
                  c.add       a3, s7
                  c.addi4spn  a3, sp, 96
                  c.or        a3, a2
                  or          s7, t2, a5
                  addi        a3, t2, -1827
                  xori        zero, s7, 820
                  sltu        s4, s2, s2
                  ori         s10, s10, 2021
                  c.add       a5, a5
                  ori         zero, a7, -374
                  c.srai      a3, 24
                  c.or        a3, a3
                  sltiu       a3, s4, -807
                  sra         s8, s5, a1
                  divu        s3, s9, tp
                  divu        t0, a7, s5
                  and         s8, s0, a2
                  andi        t1, s4, 1239
                  sltu        a0, t1, s3
                  mul         a4, s10, a6
                  c.xor       a3, a3
                  srli        t1, s7, 14
                  slti        t4, a7, 973
                  c.nop
                  slti        t3, t2, -1351
                  c.lui       s7, 16
                  sltiu       s5, t0, -22
                  c.andi      a3, 25
                  c.sub       a1, a3
                  c.slli      a5, 11
                  c.srli      a2, 23
                  c.srli      a3, 28
                  c.srai      a3, 23
                  lui         s8, 831829
                  ori         s8, s11, 323
                  andi        t1, t6, -1987
                  sub         s4, t2, s4
                  rem         t4, s2, s8
                  srl         t1, t3, tp
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_15
                  li         s10, 0x0
                  li         t3, 0x1
                  li         a4, 0x0
                  li         t2, 0x0
                  li         s9, 0x647de1b2
                  li         a6, 0x0
                  li         s8, 0x0
                  li         a7, 0x0
                  li         s4, 0x0
                  addi        a1, t3, -507
                  c.mv        t0, s1
                  c.lui       ra, 8
                  c.mv        s4, s10
                  c.addi16sp  sp, -16
                  mul         s8, s11, sp
                  mulhu       s9, a3, sp
                  c.addi      ra, -1
                  addi        tp, s10, 1994
                  nop
                  add         s6, a7, t1
                  div         s1, a4, s4
                  c.nop
                  c.addi16sp  sp, -16
                  mul         a0, t6, a3
                  rem         s7, s7, s11
                  auipc       t1, 953345
                  mulh        s6, t6, s6 #end riscv_int_numeric_corner_stream_15
                  sltu        gp, t3, a3
                  c.addi      s4, 19
                  div         a4, a1, s1
                  c.srai      a3, 22
                  ori         a7, a2, 1059
                  srai        s9, a6, 10
                  c.addi4spn  a3, sp, 80
                  mulh        s2, t3, s0
                  c.and       a3, a3
                  sub         a3, t5, s1
                  c.li        gp, 28
                  sll         s10, t6, a6
                  c.addi      gp, -1
                  slt         a0, s1, a6
                  slti        t1, s2, 1460
                  c.and       a3, a3
                  ori         t2, s8, -110
                  auipc       t3, 624599
                  c.li        a0, 13
                  c.sub       a3, a1
                  add         s0, s8, s10
                  ori         s6, a5, -667
                  c.srli      a3, 13
                  c.xor       a3, a3
                  c.add       a6, t4
                  c.slli      a5, 2
                  andi        t1, s10, 620
                  c.sub       a3, a3
                  c.xor       a3, a3
                  add         zero, a3, s11
                  and         t4, sp, t0
                  div         t0, tp, t2
                  c.andi      a3, -1
                  c.add       a3, a5
                  or          s5, s6, zero
                  c.srai      a3, 19
                  c.nop
                  c.or        a3, a5
                  and         t4, a2, s6
                  andi        zero, s9, -705
                  auipc       a6, 90294
                  c.addi      s7, 1
                  xor         a1, t6, t5
                  c.andi      a3, -1
                  c.andi      a3, -1
                  lui         s3, 11468
                  mul         s7, s7, a1
                  c.slli      t0, 25
                  mul         zero, s0, t2
                  c.andi      s0, 15
                  c.add       ra, s5
                  mulh        a3, s6, t2
                  srli        tp, a6, 15
                  sltiu       zero, a0, 1401
                  c.and       a3, a3
                  srl         t3, s9, a7
                  srai        s3, s1, 22
                  add         a4, a7, a7
                  c.andi      a3, 29
                  xor         zero, s2, s4
                  c.nop
                  nop
                  sltiu       t3, s4, -911
                  srl         s6, t1, a5
                  xor         s5, s8, a2
                  and         tp, s7, s3
                  c.mv        t0, a3
                  slt         t4, s6, s4
                  mul         t2, a2, a6
                  ori         t0, t1, -2026
                  sra         zero, tp, a6
                  addi        a7, t4, 1012
                  slli        zero, t3, 12
                  mulhsu      a0, a3, a1
                  c.addi4spn  a3, sp, 64
                  c.nop
                  srai        a4, s6, 2
                  mul         a7, a3, t3
                  mul         s3, sp, s5
                  sltiu       s5, sp, 1164
                  srli        s0, s1, 26
                  c.nop
                  addi        zero, zero, -1747
                  c.nop
                  slt         zero, s3, t4
                  and         s1, t6, t5
                  c.addi4spn  a3, sp, 384
                  c.addi16sp  sp, 240
                  sltiu       zero, s0, -1747
                  c.srai      a3, 20
                  mulh        zero, a5, s5
                  or          a4, s2, a0
                  c.xor       a3, a3
                  c.srli      s0, 14
                  mulh        s6, a0, a7
                  lui         t0, 943471
                  add         s5, a7, s10
                  mulhu       a3, a2, s3
                  sub         s1, a4, sp
                  srai        s1, s8, 18
                  sltiu       zero, tp, 1515
                  c.xor       a3, a3
                  sltu        s5, ra, s8
                  add         s3, s6, sp
                  lui         s5, 743628
                  c.addi4spn  a3, sp, 576
                  and         zero, s0, s1
                  mulh        sp, ra, s1
                  xor         s8, s6, s4
                  divu        s2, t5, gp
                  sub         ra, s5, a4
                  and         a6, tp, a4
                  c.or        s1, a3
                  slli        t4, t5, 10
                  add         s0, s6, t0
                  sub         s10, s10, s11
                  c.add       t1, t2
                  div         a2, s7, s10
                  srl         s7, tp, t0
                  c.slli      a3, 27
                  slti        a5, s8, 540
                  rem         a0, s2, a4
                  sltu        sp, a5, s6
                  c.mv        gp, a3
                  c.or        a3, a3
                  c.add       ra, t5
                  xori        s2, s9, 1022
                  c.addi4spn  s1, sp, 576
                  c.sub       a3, a3
                  sub         t4, s9, sp
                  c.li        s9, -1
                  mul         s3, gp, a4
                  slti        gp, t5, -623
                  sub         a3, tp, s7
                  srl         zero, t4, s4
                  or          t4, s4, s4
                  c.and       a5, a3
                  c.andi      s0, 12
                  add         a0, s6, t1
                  c.addi      s1, 16
                  lui         tp, 1047944
                  mulhsu      s7, a0, tp
                  srli        s10, a6, 4
                  mulhsu      a7, s3, a2
                  c.slli      t1, 24
                  c.li        sp, -1
                  c.nop
                  mulhsu      zero, t2, s3
                  or          s2, s6, a2
                  c.srai      a1, 9
                  add         s9, s9, s6
                  div         s4, t5, s11
                  nop
                  slt         a7, s5, ra
                  mulh        s4, gp, s5
                  c.srai      a3, 27
                  xori        a0, s3, -1279
                  slli        t3, a2, 20
                  sltiu       s8, a2, 1251
                  c.addi16sp  sp, -16
                  srl         ra, zero, s10
                  nop
                  andi        s8, t5, -249
                  c.sub       a3, a2
                  c.slli      t0, 12
                  c.addi      s10, 9
                  mulh        zero, a2, a0
                  c.xor       a3, a3
                  c.addi4spn  a2, sp, 864
                  lui         a5, 97270
                  sltiu       s3, t6, 1455
                  c.andi      a3, -1
                  srai        s5, s2, 16
                  c.srai      a3, 14
                  sltu        a6, s2, s8
                  slli        s0, tp, 14
                  c.and       a3, a3
                  nop
                  sltiu       ra, a6, 1764
                  c.and       a0, a3
                  c.srai      a3, 6
                  c.addi16sp  sp, 176
                  ori         a3, s11, -70
                  sll         zero, s9, s1
                  srl         gp, gp, s9
                  slli        a7, a6, 22
                  mulh        a3, t6, t5
                  slti        s9, tp, -38
                  c.li        sp, 14
                  srl         a7, t2, ra
                  slti        s5, t5, -1192
                  addi        zero, gp, 1624
                  c.slli      s8, 24
                  c.mv        s1, s9
                  c.addi16sp  sp, 80
                  c.and       a3, a3
                  srl         a6, s1, a4
                  mulhsu      ra, a4, t1
                  c.nop
                  addi        ra, s10, -1863
                  srai        a1, sp, 28
                  auipc       s7, 831118
                  c.lui       a3, 1
                  mulh        s4, tp, s3
                  mulhsu      a5, tp, s5
                  c.sub       a3, a4
                  andi        zero, s8, 1001
                  c.and       a3, a1
                  c.xor       a5, a3
                  c.addi4spn  a3, sp, 704
                  slt         s10, s2, s11
                  xor         s2, t5, a2
                  rem         ra, s4, s11
                  li         a0, 0x7077dbbb #start riscv_int_numeric_corner_stream_12
                  li         s8, 0x0
                  li         t4, 0x1
                  li         t3, 0x957a8ed
                  li         s4, 0x0
                  li         s10, 0x0
                  li         s9, 0x0
                  li         s0, 0x0
                  li         a5, 0x0
                  li         s3, 0x1
                  div         a2, s6, s7
                  add         s0, s3, s8
                  c.li        s9, 3
                  sub         sp, a2, s3
                  c.addi      ra, -1
                  rem         tp, t0, s1
                  c.sub       a0, a3
                  c.nop
                  c.nop
                  c.mv        ra, t6
                  c.mv        ra, s7
                  c.li        s9, -1
                  c.nop
                  c.nop
                  sub         s3, a3, t6
                  div         t1, s0, s4
                  add         a5, a4, t0
                  mulh        t1, t0, s1
                  mulhsu      s7, s10, a6
                  div         a6, gp, s9
                  c.add       s6, a2
                  mul         t1, a5, s10 #end riscv_int_numeric_corner_stream_12
                  sll         t4, s8, gp
                  sltiu       zero, t3, -1277
                  div         s7, zero, a0
                  add         t1, a7, a2
                  c.mv        s6, s5
                  slli        zero, s10, 26
                  sltu        s8, t3, t4
                  divu        sp, ra, a1
                  auipc       s0, 695893
                  add         zero, s0, ra
                  srl         a7, t2, s7
                  mulh        sp, t2, s9
                  c.addi16sp  sp, 448
                  mulhsu      sp, tp, sp
                  addi        a6, a5, 386
                  sra         t2, t6, a5
                  c.sub       a3, a3
                  mul         zero, s3, t1
                  c.li        a7, 25
                  sll         a6, a6, a3
                  c.li        ra, -1
                  c.sub       a3, a3
                  divu        t0, s1, t5
                  slti        gp, a1, 747
                  c.addi4spn  a3, sp, 320
                  slti        zero, s8, 1533
                  mulhsu      s9, a7, sp
                  slti        s3, tp, -6
                  mulhu       s4, s2, s9
                  c.nop
                  rem         a2, s0, t5
                  auipc       a1, 581267
                  c.addi4spn  a3, sp, 64
                  and         a0, a7, s3
                  divu        s9, s10, a5
                  c.xor       a3, a3
                  sub         s2, t2, t5
                  mulhsu      a6, a6, t0
                  slli        zero, a7, 28
                  divu        a5, s8, t1
                  c.andi      a3, 9
                  lui         t1, 58278
                  c.addi4spn  a3, sp, 368
                  c.srli      a3, 19
                  and         a2, s4, s11
                  c.nop
                  srai        zero, s1, 15
                  mulh        gp, s3, t2
                  rem         t3, a1, sp
                  c.addi      a1, -1
                  c.sub       a3, a0
                  sltiu       a2, sp, -1280
                  c.add       a0, t6
                  c.addi4spn  a5, sp, 64
                  c.and       a3, a1
                  sll         zero, s3, ra
                  c.nop
                  c.srai      a3, 13
                  c.addi4spn  a3, sp, 272
                  addi        zero, s6, 1884
                  c.addi      s2, 6
                  lui         s7, 862870
                  slt         a5, s7, a6
                  c.slli      ra, 21
                  c.li        s6, 15
                  mulhsu      tp, zero, t0
                  add         s6, s9, s7
                  c.nop
                  c.li        ra, -1
                  c.srai      a3, 5
                  addi        zero, a0, 1015
                  c.addi      s0, 13
                  sltiu       a0, s5, -1635
                  c.addi16sp  sp, 384
                  sll         a5, sp, s10
                  ori         sp, s10, 1527
                  c.lui       s9, 9
                  sll         s6, s5, a3
                  sltu        sp, a0, t4
                  nop
                  mulhsu      s2, t4, gp
                  nop
                  c.lui       gp, 29
                  nop
                  mulh        a0, a2, s8
                  sltu        zero, s8, t1
                  div         t0, tp, gp
                  c.and       a3, a3
                  c.addi4spn  a3, sp, 384
                  mul         gp, sp, a2
                  xor         a3, s3, s7
                  c.srai      a5, 24
                  c.nop
                  mulh        s0, a5, t6
                  mulh        s7, t0, s5
                  mulh        t4, a1, s9
                  auipc       s8, 807782
                  and         s4, sp, a5
                  c.sub       a3, a3
                  addi        a1, a7, 1277
                  and         zero, gp, zero
                  addi        ra, s11, 848
                  divu        sp, zero, a4
                  srl         s4, ra, t6
                  c.sub       a3, s1
                  mulhu       a6, a2, t6
                  and         s9, t5, s10
                  div         zero, s4, t6
                  xori        a2, s10, -611
                  sltu        sp, s6, a2
                  mulhu       gp, s5, a6
                  c.addi16sp  sp, -16
                  add         s4, a3, sp
                  div         s4, s11, ra
                  and         t1, a6, tp
                  c.nop
                  c.nop
                  or          t4, a6, s1
                  div         s6, a1, a3
                  c.addi      gp, -1
                  c.addi      t1, -1
                  slti        t1, t1, -58
                  li         a7, 0x1 #start riscv_int_numeric_corner_stream_4
                  li         t4, 0x0
                  li         t3, 0x0
                  li         a3, 0x1
                  li         s6, 0x119ea349
                  li         a2, 0x200af683
                  li         s0, 0x0
                  li         s9, 0x76ab1fa8
                  li         tp, 0x0
                  li         s4, 0x1
                  auipc       ra, 342991
                  nop
                  div         t4, a3, a4
                  mulh        a1, a2, sp
                  c.addi      t3, 10
                  c.addi4spn  a3, sp, 896
                  c.lui       ra, 3
                  mulhsu      s1, t2, t4
                  c.li        tp, 20
                  c.sub       a3, a3
                  sub         gp, t6, sp
                  sub         a5, a7, s4
                  c.addi      s0, -1
                  c.addi16sp  sp, -16
                  c.addi4spn  a3, sp, 960
                  c.mv        t1, s6
                  sub         s7, s9, s8
                  sub         gp, s1, t6
                  mulhu       s9, t1, t5
                  c.add       t4, a1
                  c.lui       ra, 5
                  div         t2, t2, a7 #end riscv_int_numeric_corner_stream_4
                  xori        s6, a1, -1566
                  c.and       a3, a3
                  add         t0, a3, s11
                  c.and       a3, a0
                  slt         sp, t5, t5
                  srai        a4, gp, 19
                  c.srai      a3, 5
                  c.or        a3, a1
                  add         t2, ra, zero
                  slti        zero, t4, -936
                  slli        s1, a0, 6
                  xor         t1, t2, s3
                  c.srli      a2, 25
                  lui         a5, 901881
                  xor         a6, a1, t6
                  and         sp, s6, a2
                  c.xor       a3, a3
                  sll         s2, t1, s1
                  xor         a3, t2, t3
                  c.mv        ra, s4
                  sub         a4, s7, a0
                  slt         a1, ra, s4
                  add         ra, zero, t1
                  c.mv        s2, s8
                  c.xor       a3, a3
                  c.srli      a3, 30
                  andi        sp, s6, -59
                  c.or        a3, a3
                  xor         a1, a0, s5
                  sltiu       s4, s1, -278
                  div         a5, a6, a0
                  slt         s7, a7, a7
                  mulhu       t3, s7, t5
                  ori         a7, t3, -172
                  div         a0, a6, a6
                  c.add       s9, tp
                  c.andi      a3, -1
                  c.xor       a3, a3
                  c.mv        a1, t1
                  and         a5, s2, a2
                  sltiu       s5, s11, -1372
                  slti        a1, s6, -1663
                  or          s1, tp, t1
                  mulh        s10, s3, s1
                  c.mv        s5, t4
                  c.addi16sp  sp, -16
                  c.add       s1, t0
                  xori        s10, s1, -1472
                  c.addi      a4, 10
                  ori         a4, a3, 84
                  xor         s10, a7, t1
                  srai        zero, t6, 6
                  srli        s7, t2, 27
                  c.nop
                  srli        t0, t0, 24
                  c.lui       s9, 14
                  xor         s0, a5, s0
                  div         t2, a5, s6
                  sub         gp, s1, s2
                  ori         zero, s3, 1276
                  srai        a1, a6, 4
                  srai        a6, s11, 26
                  srl         zero, s10, s0
                  c.and       a3, s0
                  rem         a6, tp, a5
                  sub         s1, s9, a6
                  c.srai      a3, 8
                  rem         s6, t4, a0
                  c.addi16sp  sp, 144
                  addi        zero, s9, -734
                  srai        t1, ra, 19
                  c.and       a1, a3
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_7
                  li         t3, 0x0
                  li         s10, 0x1
                  li         s9, 0x312e31b8
                  li         s8, 0x425c8f5b
                  li         s0, 0x6f04e18
                  li         s4, 0x77c0e0ad
                  li         t2, 0x4d04d219
                  li         a4, 0x31dc8466
                  li         s1, 0x1
                  add         t0, a5, t0
                  c.addi16sp  sp, -16
                  addi        t2, t1, -1230
                  c.nop
                  rem         t0, a4, t2
                  auipc       sp, 938754
                  sub         t0, t3, a1
                  c.li        s0, -1
                  c.mv        s7, a2
                  div         s7, s8, sp
                  auipc       zero, 415104
                  divu        a3, t2, t4
                  nop
                  sub         sp, t4, t4
                  addi        zero, a7, -770
                  c.li        a3, 25
                  c.lui       s4, 3
                  xori        t2, s7, -1413
                  xori        zero, zero, 1429
                  nop
                  or          a5, tp, s8
                  c.andi      a3, 14
                  c.srli      a3, 2
                  c.add       a2, tp
                  div         s7, s5, a7
                  mulhu       zero, a5, tp
                  slli        gp, a1, 12
                  mulhu       s3, s5, a3
                  xor         t2, t5, t2
                  srai        a1, ra, 23
                  c.srai      a3, 10
                  mulhu       t2, s4, s10
                  xori        a3, t2, -1765
                  addi        zero, t5, 430
                  c.or        a3, a0
                  c.addi4spn  a3, sp, 64
                  sub         sp, a5, s4
                  slt         t2, t6, a7
                  nop
                  c.and       a3, a3
                  lui         zero, 111695
                  rem         t3, s4, s7
                  rem         ra, s4, s9
                  c.srli      a3, 12
                  c.add       a1, s10
                  c.sub       a3, a1
                  c.andi      a5, -1
                  addi        a6, s1, 999
                  srli        t2, s5, 31
                  andi        s10, s9, 246
                  mulhu       zero, ra, sp
                  nop
                  andi        s1, s4, -2021
                  sltiu       a1, t0, -67
                  ori         s2, a7, 1797
                  mulh        s6, s2, t5
                  slli        zero, a4, 14
                  xori        s7, a1, 493
                  c.andi      a3, -1
                  c.or        a1, a3
                  mulhu       s1, ra, s8
                  c.addi      gp, -1
                  rem         s1, a1, s5
                  mulh        a0, s8, s11
                  srli        t1, t3, 16
                  add         a3, t4, a0
                  c.xor       a3, s1
                  c.slli      s6, 30
                  rem         s10, t1, s2
                  c.srai      a3, 6
                  xor         t2, a6, s2
                  mulhu       s5, tp, gp
                  c.xor       a3, a4
                  xori        a6, s3, -377
                  mulh        s4, a7, t0
                  c.lui       t2, 17
                  c.li        s4, 23
                  mulhsu      zero, t2, t5
                  addi        a7, a6, -1138
                  sra         a0, s8, a1
                  c.xor       s1, a3
                  c.sub       a3, a3
                  addi        a0, a5, -1895
                  auipc       a6, 1015562
                  mulhsu      s5, s0, a1
                  mulhsu      s8, t3, s8
                  srl         s9, a1, a5
                  xor         s6, a1, a5
                  slli        a1, s9, 18
                  slti        s2, t5, 591
                  c.addi16sp  sp, 96
                  srl         s6, a0, a1
                  mul         ra, t6, s6
                  andi        a6, a7, 896
                  mulh        t0, a4, t5
                  c.nop
                  sltu        a2, a3, a5
                  c.andi      a3, 14
                  nop
                  div         s4, s10, s6
                  slt         t0, t1, tp
                  c.slli      s6, 22
                  and         s2, t0, a5
                  add         s8, a7, s10
                  or          s10, gp, t6
                  and         ra, s8, s7
                  c.lui       ra, 31
                  lui         s4, 629829
                  c.andi      a3, 7
                  slt         a3, t5, zero
                  mulh        s7, gp, s1
                  c.add       a7, t3
                  c.sub       a3, a3
                  slt         tp, s10, a3
                  xori        zero, sp, 1733
                  sltu        s8, s5, s7
                  nop
                  sra         t2, s9, t5
                  c.addi4spn  a3, sp, 464
                  mulh        t0, a0, sp
                  c.mv        ra, s0
                  c.srai      a4, 6
                  rem         s0, t4, t3
                  mulhu       zero, s4, t3
                  sub         zero, t1, s5
                  srli        tp, zero, 25
                  slli        s10, s4, 22
                  auipc       t0, 744678
                  divu        t3, t0, a6
                  xor         s1, s4, s11
                  c.li        tp, 13
                  slti        t2, s6, -1257
                  sub         zero, s9, a7
                  slli        s9, s1, 25
                  c.sub       a3, a3
                  xori        a4, t3, -1585
                  slt         s3, s2, a6
                  sltu        s5, s11, a5
                  srl         a1, sp, s3
                  ori         gp, s3, -1782
                  mulhsu      a5, zero, t3
                  srai        zero, t6, 30
                  slli        a1, s7, 23
                  slli        t4, s4, 24
                  rem         s9, s4, s7
                  c.addi16sp  sp, 64
                  sltiu       t2, s5, 187
                  c.srai      a3, 30
                  addi        a0, s0, -123
                  andi        a4, a3, 153
                  nop
                  c.sub       a3, a3
                  c.addi16sp  sp, 320
                  sltu        zero, t6, sp
                  c.li        t4, 12
                  srai        zero, s9, 15
                  mul         s9, ra, tp
                  addi        s4, a7, 575
                  sub         a6, t1, zero
                  sltu        s3, t1, s6
                  sub         ra, s3, t1
                  nop
                  mulhu       a4, s7, s1
                  c.lui       gp, 2
                  mul         s7, a5, s5
                  slli        ra, a1, 3
                  c.addi16sp  sp, 64
                  c.and       a3, a1
                  c.add       a7, s5
                  divu        s10, s7, s11
                  xori        a5, a0, 1474
                  c.andi      a3, -1
                  mulhsu      sp, a0, t0
                  slti        zero, s6, 1507
                  xori        a2, a6, -409
                  mulhsu      a6, t2, t0
                  c.nop
                  xori        ra, zero, -1865
                  c.and       a3, a3
                  c.mv        t1, a6
                  mulhsu      a0, s5, s10
                  mul         s8, s0, s11
                  lui         zero, 844742
                  rem         a7, s4, s1
                  c.nop
                  sltu        a7, sp, s11
                  mulhu       a6, t0, s5
                  slli        a4, sp, 21
                  add         s3, t3, t1
                  rem         s8, t0, a2
                  srli        tp, t0, 5
                  or          t3, a1, t2
                  xor         a3, s8, s0
                  sltu        s7, a0, s1
                  andi        s5, a3, -1252
                  ori         ra, s6, -1033
                  slti        s9, t4, -1497
                  sub         s9, t5, t4
                  c.slli      s7, 20
                  slti        s9, a0, 491
                  nop
                  c.mv        s4, gp
                  srli        s2, a0, 10
                  rem         a1, zero, s8
                  mulh        a4, s7, t0
                  mulhsu      s2, t6, s7
                  xori        s8, a4, 382
                  sltiu       s8, a2, 43
                  addi        t0, s10, -1573
                  auipc       a3, 157659
                  xori        zero, s10, 846
                  mul         a5, t6, t2
                  c.sub       a3, a3
                  c.addi16sp  sp, -16
                  sra         s3, tp, a2
                  c.sub       a3, a3
                  or          gp, s8, t4
                  slt         a3, a5, s6
                  c.slli      s5, 22
                  c.li        ra, 9
                  mul         s5, s5, a0
                  c.srai      a3, 8
                  slli        s1, s2, 13
                  srai        s0, s0, 20
                  or          s9, a2, a1
                  c.addi4spn  a0, sp, 384
                  ori         ra, ra, 889
                  xori        t2, a6, -784
                  rem         a3, tp, s11
                  c.andi      a3, 3
                  nop
                  lui         t3, 664158
                  lui         s2, 580294
                  c.srai      a3, 18
                  or          s6, a6, a5
                  ori         t3, t1, -689
                  divu        a2, s2, t1
                  mul         zero, s6, a3
                  andi        tp, s7, 1450
                  andi        s2, a2, -46
                  c.xor       a3, a3
                  c.srai      a0, 10
                  c.xor       a3, a3
                  rem         zero, t0, s6
                  c.addi      s6, -1
                  c.addi16sp  sp, -16
                  mulhsu      zero, s1, s4
                  addi        s6, a2, -1440
                  c.addi      a6, -1
                  or          t4, s0, a5
                  nop
                  srli        tp, a2, 19
                  mul         t4, s8, gp
                  slti        s8, s11, 849
                  divu        zero, a2, a2
                  auipc       zero, 545193
                  sltu        s2, s6, tp
                  c.add       tp, a1
                  or          s2, a5, s3
                  or          s1, s11, a2
                  div         s8, a5, tp
                  xori        s9, s5, -1212
                  sltu        a0, ra, s10
                  sll         a1, s0, t3
                  c.mv        sp, t4
                  add         t4, s2, s0
                  c.sub       a3, a3
                  sra         zero, s4, a2
                  sub         s10, s6, s8
                  srai        s0, a2, 16
                  ori         s9, t1, -633
                  and         gp, a0, s6
                  nop
                  and         a3, t0, s4
                  srli        t0, a3, 31
                  c.srli      a3, 20
                  andi        s10, a0, 1348
                  c.srli      a3, 20
                  rem         a2, s7, s3
                  c.srli      a3, 8
                  slli        a4, s2, 14
                  mulhsu      tp, sp, t6
                  divu        a2, s9, s7
                  auipc       s6, 835690
                  mul         t1, t0, s4
                  add         sp, t3, s4
                  sltu        t1, sp, a1
                  mulh        t1, t0, tp
                  c.andi      a3, 17
                  divu        t2, a4, a7
                  srli        s8, t5, 25
                  slt         zero, s6, t4
                  srl         a6, t6, a4
                  mul         a4, t6, t5
                  lui         a6, 39675
                  srli        s0, s4, 9
                  c.li        s7, 28
                  mulhu       a4, t4, a4
                  c.srai      a3, 24
                  xor         zero, gp, a3
                  mulhu       s8, a7, zero
                  c.lui       ra, 29
                  sltu        zero, a3, tp
                  srli        s8, tp, 13
                  sra         a7, t1, a7
                  slti        gp, a4, 333
                  c.nop
                  c.addi16sp  sp, -16
                  sub         t2, t6, a4
                  srl         sp, t4, a0
                  lui         s0, 680846
                  sltiu       zero, s2, 1753
                  and         a3, t5, a0
                  c.and       a3, a3
                  c.srai      a3, 25
                  slt         s9, sp, s2
                  c.or        a3, a3
                  c.andi      a3, 29
                  divu        a1, t5, s6
                  c.addi      ra, -1
                  srl         s10, s11, a6
                  xori        s7, gp, -2004
                  and         zero, gp, s0
                  addi        tp, s6, -429
                  sll         gp, t2, sp
                  xor         t2, ra, t4
                  c.li        ra, 7
                  mulh        t1, sp, zero
                  sub         gp, ra, ra
                  srai        zero, a0, 10
                  c.li        s9, -1
                  and         a3, a3, t3
                  slt         a7, s0, s9
                  srl         zero, t0, ra
                  sll         zero, s5, t4
                  sub         s2, t0, a2
                  srai        ra, s1, 11
                  c.li        a3, 27
                  c.li        ra, 20
                  srai        a6, s10, 23
                  c.addi      a3, 22
                  div         s4, t3, a3
                  rem         s4, s7, s6
                  lui         a7, 556954
                  auipc       s10, 1019371
                  c.add       s3, s1
                  auipc       s4, 448131
                  c.addi4spn  a5, sp, 64
                  nop
                  mul         zero, gp, t5
                  rem         a5, a5, t0
                  and         s10, s11, a0
                  c.slli      s4, 23
                  srai        a4, s8, 13
                  c.and       a4, a0
                  srai        a5, s6, 15
                  divu        s0, a2, a4
                  srai        t0, s7, 28
                  slli        t4, t0, 25
                  c.xor       a3, s0
                  div         s4, a0, a2
                  sub         t1, s0, s8
                  srai        s3, s8, 6
                  nop
                  srli        ra, s4, 2
                  sra         zero, a4, a7
                  srl         t0, t1, s7
                  sll         t2, s3, zero
                  c.or        a3, a3
                  srai        a3, s1, 1
                  c.or        a3, a3
                  slti        s9, t0, -72
                  andi        a2, a5, -401
                  c.li        a0, -1
                  c.andi      a5, -1
                  mul         s3, a7, s1
                  addi        sp, s10, 554
                  xori        a1, t2, -689
                  auipc       sp, 157997
                  nop
                  c.xor       s1, a3
                  c.addi      a1, -1
                  srai        zero, s0, 12
                  c.or        a3, s1
                  div         zero, tp, s7
                  c.mv        ra, a5
                  xor         s1, s1, s5
                  auipc       a4, 370128
                  xor         s3, t3, a2
                  sra         t0, a6, s0
                  mulhsu      a4, s6, a1
                  sltu        s5, s10, s7
                  sra         a6, s3, ra
                  sltiu       t3, sp, -645
                  mulhu       s9, s4, s9
                  srai        s2, s11, 8
                  mul         t2, a0, t2
                  c.and       a3, a1
                  addi        a0, s10, 58
                  sltu        ra, s0, a1
                  sltu        a4, a6, zero
                  c.addi      a7, -1
                  c.lui       ra, 24
                  srli        a0, t2, 18
                  and         ra, ra, s9
                  mulh        t2, a2, s1
                  ori         tp, s11, -14
                  srli        ra, s1, 19
                  mulh        t4, t1, t5
                  xori        ra, a1, -1375
                  c.mv        s3, t0
                  add         s7, a0, s1
                  lui         a3, 750995
                  andi        t3, s11, -1577
                  mulh        tp, a0, t3
                  c.xor       a2, a1
                  sub         s8, s3, a1
                  sra         s0, a5, a3
                  add         a1, a3, t3
                  slti        s9, a4, 1438
                  mulh        zero, a1, a5
                  sub         s8, t2, zero
                  c.andi      a3, 9
                  add         a2, a2, t4
                  srli        t1, a4, 25
                  srl         a4, tp, a3
                  c.sub       a3, a1
                  lui         s6, 76286
                  add         zero, a1, a5
                  sll         a7, a6, s11
                  c.srai      a3, 16
                  and         ra, a1, t3
                  c.addi16sp  sp, -16
                  sltiu       sp, t2, 770
                  c.andi      a5, 29
                  c.xor       a3, a2
                  sltiu       a3, zero, 1860
                  div         s9, t6, t1
                  c.sub       a3, a3
                  c.xor       a3, a3
                  c.srli      a3, 7
                  xor         zero, s6, s5
                  slti        s5, tp, -226
                  c.andi      a3, 18
                  srai        s0, t4, 6
                  mulh        ra, s5, a1
                  nop
                  xori        s7, a4, -1224
                  mulhsu      t1, a0, a2
                  rem         a1, s5, s0
                  rem         s5, a3, s4
                  c.srai      a3, 11
                  addi        a0, ra, -1216
                  slti        sp, zero, 792
                  ori         a4, s5, 1137
                  sltu        s5, s3, t0
                  sub         s4, a7, a4
                  srli        zero, s11, 5
                  or          s3, a2, s2
                  and         t1, s7, ra
                  c.andi      a2, -1
                  auipc       gp, 528328
                  rem         a3, a6, s0
                  and         t2, t5, s9
                  auipc       t1, 919947
                  and         s7, a5, a1
                  or          a1, a0, t5
                  mulhsu      s9, a0, s7
                  c.sub       a3, a3
                  c.mv        ra, sp
                  slti        s10, a5, 1089
                  c.srli      a3, 4
                  c.srai      a3, 16
                  lui         s9, 168565
                  c.slli      t4, 29
                  rem         a4, s6, s7
                  c.slli      s1, 25
                  and         tp, sp, a7
                  c.nop
                  c.li        t4, -1
                  mulhu       t1, s2, sp
                  rem         a2, a7, s7
                  srl         zero, a5, s11
                  sltiu       s9, t0, -1066
                  c.nop
                  ori         t1, t2, -563
                  or          s3, a1, a7
                  c.mv        s9, gp
                  mulhu       s6, s5, s7
                  or          a6, a7, gp
                  addi        zero, t0, -274
                  lui         a2, 100076
                  divu        sp, t3, t4
                  xori        s3, ra, 408
                  c.xor       a3, a3
                  sra         s7, tp, a3
                  mulhu       s2, sp, s5
                  c.li        t4, 0
                  mulhu       t0, ra, t0
                  xor         a1, a5, a5
                  and         s7, a0, s7
                  srl         gp, s0, s7
                  srl         zero, s11, t2
                  c.or        a3, a1
                  rem         a2, s1, s11
                  andi        a4, s5, -38
                  c.lui       t4, 11
                  rem         a1, zero, a4
                  c.and       a3, a3
                  andi        a6, t6, -730
                  c.add       ra, s6
                  c.and       s1, a3
                  c.mv        t0, t2
                  c.li        s2, -1
                  lui         a0, 1003026
                  divu        a0, s10, tp
                  c.and       a3, a3
                  slli        s7, s8, 4
                  rem         t3, s4, a3
                  and         zero, zero, a4
                  c.or        a3, a3
                  sub         s9, a3, gp
                  c.slli      a1, 3
                  c.lui       a1, 1
                  sltu        t2, s11, zero
                  srai        s9, s9, 21
                  sltiu       s9, s0, -1547
                  rem         t2, s0, tp
                  c.sub       a3, a3
                  sltu        a5, s11, t0
                  and         tp, a2, a7
                  sra         t0, sp, t1
                  divu        s10, s6, t4
                  srli        gp, a0, 30
                  slli        zero, tp, 4
                  rem         s9, s10, t0
                  rem         gp, sp, a7
                  c.slli      s8, 23
                  divu        s10, s1, a7
                  c.mv        ra, s0
                  srli        gp, s6, 2
                  add         s2, s3, a7
                  xor         t1, s0, s6
                  ori         s4, s7, -124
                  srl         a0, s11, a3
                  c.andi      a3, -1
                  c.xor       a3, a3
                  lui         a0, 999086
                  sll         s0, zero, s1
                  xor         a0, sp, s2
                  srl         a4, zero, a1
                  lui         zero, 148384
                  mulhsu      s3, t3, gp
                  andi        a3, s3, -1062
                  sll         t0, a6, s4
                  divu        s10, a7, t5
                  mulhu       t3, a3, s5
                  c.nop
                  lui         sp, 998493
                  mulh        t0, s9, s10
                  srai        s4, s9, 18
                  c.mv        s3, a4
                  mulh        s2, t2, a2
                  rem         s0, a2, a4
                  add         s2, a7, s8
                  sltiu       s6, a7, 61
                  c.li        a1, 20
                  c.srai      a3, 30
                  mulh        gp, s6, s8
                  addi        t1, ra, 1300
                  auipc       s10, 640466
                  c.lui       s0, 3
                  rem         s8, s9, tp
                  sltu        t4, s2, t1
                  c.addi16sp  sp, 16
                  slt         s10, t4, s10
                  slli        s8, t3, 26
                  mulhu       s0, s2, sp
                  c.nop
                  sltiu       t2, a5, 1827
                  c.sub       a5, a3
                  slt         zero, zero, t2
                  c.xor       s0, a3
                  sll         a1, a1, s0
                  rem         s6, s4, s6
                  sll         a1, tp, sp
                  sll         s3, s4, sp
                  c.and       s1, a3
                  div         a4, s5, s0
                  srl         a6, s6, s0
                  xor         zero, sp, s10
                  lui         s0, 359669
                  div         s7, s1, a3
                  c.mv        a3, a3
                  xor         a6, a7, s5
                  mulhu       s6, sp, s0
                  c.nop
                  c.mv        t0, s8
                  ori         a2, sp, 6
                  c.xor       a3, a3
                  mulhu       t0, zero, zero
                  mul         a4, s5, a7
                  mulh        zero, a5, a0
                  sltiu       s4, t2, 2021
                  ori         s8, a0, -1852
                  srli        gp, a0, 28
                  c.li        a3, -1
                  mulhsu      t3, a4, sp
                  ori         a5, s11, 1030
                  mulhsu      s8, s0, s2
                  nop
                  or          a4, t0, a2
                  c.nop
                  c.addi16sp  sp, 320
                  xori        s3, s7, -1403
                  mulh        t0, a4, a7
                  slti        a7, t2, -1353
                  mulh        t1, s11, a3
                  slli        sp, zero, 8
                  div         tp, s1, a0
                  addi        gp, tp, 1192
                  ori         t4, a2, -1931
                  divu        s10, s8, t1
                  c.srai      a3, 10
                  c.lui       a1, 15
                  srl         gp, s5, s11
                  xori        s7, tp, -1952
                  mul         s9, s0, s5
                  slli        t3, t6, 0
                  nop
                  c.or        a2, a3
                  c.addi4spn  a3, sp, 64
                  c.addi4spn  a3, sp, 960
                  add         a1, s6, s5
                  mulhu       s0, t1, a4
                  c.slli      ra, 6
                  auipc       t2, 910782
                  srli        s9, s3, 2
                  c.sub       a3, a3
                  c.li        a4, 15
                  sub         a3, a4, gp
                  slt         zero, a5, zero
                  sltu        s3, ra, gp
                  nop
                  srl         a5, a3, ra
                  c.sub       a3, a3
                  c.or        a3, a3
                  auipc       a7, 294306
                  c.sub       a3, a3
                  mulh        s10, s9, ra
                  nop
                  rem         a7, a7, s7
                  slt         s4, a1, gp
                  c.srai      a3, 2
                  lui         a2, 750453
                  c.or        a3, a3
                  div         t4, t2, sp
                  nop
                  mulhu       sp, s9, t2
                  c.xor       a3, a3
                  auipc       zero, 106341
                  div         a6, ra, s0
                  slt         a5, t0, a5
                  c.lui       s8, 28
                  slt         s8, ra, t1
                  c.addi4spn  a4, sp, 64
                  c.mv        t2, s8
                  c.sub       a3, a3
                  rem         a2, s10, s2
                  c.li        a1, -1
                  mulhsu      s3, t0, a0
                  c.xor       a3, a3
                  divu        s4, sp, t4
                  srl         t2, a3, s4
                  add         s6, tp, a5
                  slti        t4, s6, 665
                  nop
                  sltu        zero, s10, s10
                  c.addi4spn  a3, sp, 16
                  c.addi4spn  a3, sp, 192
                  mul         a1, a1, s11
                  c.or        a3, a3
                  add         zero, s2, s5
                  srl         s7, t2, t0
                  sltiu       s2, t0, -566
                  c.mv        s1, s10
                  c.srli      a3, 8
                  c.slli      gp, 20
                  c.li        t3, -1
                  lui         s7, 614889
                  c.add       s8, s6
                  c.li        t2, 28
                  mulh        a5, s2, t0
                  or          zero, a3, a5
                  c.addi16sp  sp, 384
                  c.addi4spn  a3, sp, 576
                  c.srai      a3, 10
                  mulh        sp, sp, zero
                  c.li        sp, -1
                  c.srli      a5, 18
                  c.or        a3, a3
                  c.or        a3, a1
                  c.addi16sp  sp, 384
                  c.or        a3, a3
                  c.addi16sp  sp, -16
                  c.srli      a3, 27
                  divu        s9, a5, gp
                  mulh        t4, t5, ra
                  srl         s6, a5, s5
                  mulhsu      gp, gp, a3
                  srli        s0, s6, 31
                  mulh        s2, a7, s5
                  rem         s0, s10, s5
                  andi        a3, sp, 524
                  c.sub       a3, a3
                  c.nop
                  c.xor       a3, a3
                  slti        a7, a7, -1978
                  rem         t3, s9, a7
                  c.mv        a4, s11
                  sltu        s10, a7, s11
                  xori        a1, s9, -216
                  c.addi4spn  a3, sp, 832
                  c.addi      s7, 22
                  sub         s4, s10, a1
                  auipc       a1, 872585
                  slti        zero, a6, 884
                  slti        a2, t2, 938
                  c.mv        a5, t4
                  c.mv        t1, a2
                  nop
                  nop
                  div         a1, t2, s1
                  c.srai      a3, 29
                  xori        sp, a1, 1230
                  and         s7, gp, t0
                  slti        t3, s3, 1355
                  or          s1, t0, s4
                  sltiu       t4, s6, 265
                  srai        s5, a1, 8
                  srli        s3, s6, 5
                  sltiu       a1, t1, -1362
                  div         t1, a1, s8
                  slli        s7, tp, 27
                  c.srai      a3, 12
                  c.lui       s10, 13
                  mul         t2, sp, s10
                  c.addi4spn  a3, sp, 192
                  c.add       a3, t1
                  div         a7, a1, sp
                  c.or        a3, a3
                  auipc       t3, 522562
                  ori         a6, sp, 800
                  c.slli      s9, 13
                  xori        s7, tp, -538
                  c.li        a3, -1
                  c.and       a3, a3
                  nop
                  slli        zero, s1, 4
                  srl         sp, t5, a2
                  lui         zero, 886002
                  c.srai      a3, 19
                  add         zero, s11, a6
                  c.or        a3, a3
                  or          s6, a3, t2
                  xori        gp, s6, 719
                  xor         s7, t3, a4
                  sub         a3, s5, s6
                  c.and       a4, a3
                  c.addi4spn  a3, sp, 896
                  ori         s7, s3, 400
                  and         s7, s7, gp
                  c.li        ra, 18
                  c.srli      a3, 1
                  c.add       a4, a0
                  and         s7, ra, s2
                  c.addi4spn  a3, sp, 64
                  rem         ra, t3, t4
                  c.andi      a5, -1
                  c.srai      a3, 5
                  lui         ra, 671062
                  nop
                  c.sub       a3, a3
                  addi        t4, s11, 728
                  c.andi      a3, -1
                  c.or        a3, s0
                  mulhsu      s4, a5, s10
                  slt         s1, t2, s5
                  andi        a5, s6, 1633
                  c.srai      a3, 12
                  srl         gp, s6, s8
                  nop
                  sub         a2, s7, s5
                  or          s9, a1, t6
                  div         t2, t1, t2
                  c.srai      s0, 6
                  c.or        a3, a3
                  sra         s9, s4, s3
                  sra         ra, a1, a2
                  sltiu       s9, tp, 1817
                  c.and       a3, a3
                  srl         t1, s2, s1
                  sra         s9, a3, t0
                  div         a2, tp, s7
                  rem         a0, s0, s0
                  andi        s7, s8, -870
                  c.mv        s2, s11
                  c.lui       gp, 28
                  c.lui       a5, 29
                  mulh        s9, tp, s2
                  sll         tp, a1, t1
                  mulhsu      s7, a2, s1
                  c.and       a3, a3
                  mul         s4, s10, s3
                  c.or        a3, a3
                  auipc       t1, 158713
                  mul         gp, a5, s10
                  sltu        zero, a5, a2
                  c.li        ra, -1
                  sltu        a5, a0, t3
                  ori         s9, a5, 1454
                  mulhsu      t0, a6, s1
                  c.add       a2, t6
                  mulh        ra, sp, a2
                  c.srai      a3, 16
                  rem         s2, ra, ra
                  c.nop
                  auipc       a7, 944641
                  addi        s8, zero, -1752
                  mulhsu      tp, t1, t5
                  sra         t1, t0, a0
                  c.and       a5, a5
                  nop
                  nop
                  c.srai      a3, 10
                  c.addi4spn  a3, sp, 64
                  c.or        a3, a3
                  srl         s1, s11, t0
                  c.or        a3, a3
                  c.or        a3, a3
                  xor         a7, s3, s1
                  c.xor       a3, a1
                  and         zero, a4, s0
                  sub         s5, a1, s7
                  c.xor       a3, a3
                  sra         t2, s1, s2
                  sltiu       t1, s3, -1723
                  nop
                  c.addi      a7, 10
                  c.srai      a3, 5
                  srl         s3, t2, s3
                  sltiu       a0, t4, 841
                  mulhsu      tp, a5, s9
                  c.or        s1, a5
                  mulhsu      s6, t0, a3
                  or          t0, a6, a0
                  srl         zero, s2, s6
                  nop
                  sltu        a0, a2, t0
                  c.and       a3, a3
                  andi        tp, s7, 664
                  c.li        ra, 24
                  c.add       gp, s11
                  c.addi4spn  a3, sp, 304
                  xor         s8, t1, s3
                  ori         sp, ra, 1923
                  c.sub       a1, a3
                  mulhu       a3, s10, zero
                  c.andi      a3, 24
                  c.addi      s1, 22
                  c.or        s0, a3
                  c.andi      a3, -1
                  srli        tp, a0, 22
                  c.and       a2, a3
                  mulh        sp, sp, t2
                  c.slli      s1, 14
                  slli        s7, a4, 1
                  mul         s10, t5, t0
                  sub         zero, zero, s0
                  c.nop
                  c.slli      s1, 2
                  c.slli      ra, 16
                  slli        t4, s7, 8
                  lui         t0, 323949
                  andi        sp, a1, 1167
                  sra         t0, s2, a5
                  andi        a6, t0, 1191
                  sub         s8, a7, a0
                  and         a4, a7, s0
                  mul         sp, zero, s4
                  mulhsu      s10, a2, a2
                  c.srli      a0, 28
                  c.addi      ra, 3
                  div         t0, t5, s11
                  c.srai      a3, 17
                  xori        t3, s1, -148
                  srl         a7, s6, s8
                  sltu        s6, s10, t4
                  c.addi      s1, 8
                  sra         t4, s11, a3
                  sra         zero, gp, s11
                  or          ra, a4, ra
                  and         sp, zero, a0
                  c.slli      s10, 1
                  mul         zero, s1, sp
                  div         s0, t0, s7
                  slti        zero, s6, 419
                  mulhsu      s5, s10, s3
                  c.lui       ra, 11
                  div         a1, t5, s5
                  addi        s7, s5, 814
                  c.xor       a1, a3
                  c.andi      a3, -1
                  sra         a6, t6, s3
                  and         s10, s0, s9
                  divu        ra, t4, s6
                  srai        s2, gp, 10
                  addi        s7, t5, -2021
                  mulhsu      ra, t1, s6
                  srai        a3, a5, 12
                  srl         s0, s1, a0
                  sll         sp, a4, s11
                  c.addi16sp  sp, -16
                  c.or        a3, a3
                  c.add       sp, s8
                  srl         s6, a7, t3
                  sub         a5, s10, a7
                  mul         a4, s0, s6
                  c.xor       a3, a3
                  c.or        a3, a3
                  c.sub       a3, a3
                  or          a7, a0, s1
                  c.srai      a3, 21
                  c.srli      a3, 29
                  c.mv        ra, s4
                  sll         a7, a4, a7
                  and         a6, tp, s2
                  c.slli      ra, 21
                  xori        a2, ra, -688
                  sub         a1, s3, s10
                  sltu        s9, t2, s4
                  c.andi      a3, -1
                  or          s4, t2, a1
                  slti        t3, s5, -944
                  c.srai      s1, 4
                  andi        s3, s6, -69
                  c.addi      t3, -1
                  c.add       t2, s7
                  srli        s9, a6, 17
                  c.add       a1, s4
                  div         a2, s1, t2
                  c.srli      a5, 2
                  c.nop
                  c.addi4spn  a3, sp, 784
                  mulh        t1, a6, a1
                  sll         s0, s4, s5
                  and         tp, gp, s10
                  c.srai      a3, 7
                  xori        a2, t1, -1501
                  c.sub       a3, a3
                  c.li        s10, -1
                  divu        t3, t0, s9
                  rem         a1, zero, t4
                  mulhsu      s2, s4, sp
                  xor         s10, s11, t3
                  c.nop
                  sra         a6, s0, s7
                  xor         zero, s2, s7
                  addi        a4, s9, -1044
                  sltu        a0, a0, ra
                  slli        s2, s7, 21
                  li         t4, 0x1 #start riscv_int_numeric_corner_stream_5
                  li         s9, 0x0
                  li         s10, 0x284ddaa7
                  li         s2, 0x2c4e9de2
                  li         t3, 0x0
                  li         a0, 0x5d0936f7
                  li         t1, 0x1
                  li         s7, 0x123f4f83
                  li         a1, 0x1
                  li         t2, 0x1
                  c.mv        t2, s3
                  div         s6, a3, s0
                  c.mv        s5, s6
                  mul         s2, t2, s3
                  auipc       a7, 306913
                  auipc       t3, 521824
                  c.li        s4, -1
                  sub         s10, a5, sp
                  c.addi      a1, 26
                  c.lui       s4, 1
                  c.add       s9, s7
                  c.addi16sp  sp, -16
                  mulh        s8, s0, t4
                  c.lui       s6, 16
                  sub         ra, a2, s2
                  c.li        t4, -1
                  add         zero, tp, zero
                  c.addi16sp  sp, 240
                  lui         s4, 996161 #end riscv_int_numeric_corner_stream_5
                  slti        s3, s1, -553
                  c.andi      a3, -1
                  c.slli      t2, 3
                  c.srli      a3, 9
                  srli        s9, a7, 15
                  addi        t0, s11, -1383
                  sra         ra, a5, t0
                  sll         s9, s10, s0
                  c.slli      s0, 29
                  sub         t2, s10, gp
                  c.andi      a4, -1
                  c.and       a3, a3
                  slti        s8, t0, -28
                  mulhu       a5, s0, tp
                  mul         zero, a0, s0
                  c.addi16sp  sp, 352
                  and         a7, t6, a6
                  xori        zero, s11, 450
                  srai        t3, t4, 19
                  andi        zero, t3, -1277
                  c.xor       a3, a3
                  c.srai      a5, 25
                  rem         t4, t5, s1
                  div         s7, ra, s8
                  rem         s10, s3, a6
                  sll         t0, t3, t5
                  divu        t1, t6, sp
                  slt         s10, s1, t4
                  sll         s7, t3, t5
                  c.add       a2, a4
                  c.lui       ra, 21
                  c.slli      t2, 1
                  c.mv        ra, a2
                  c.mv        s8, a4
                  auipc       s8, 305315
                  xor         zero, s3, ra
                  slt         a2, t1, a0
                  c.slli      s3, 8
                  ori         s6, s9, 1955
                  sra         t1, s2, t6
                  rem         s1, a6, s8
                  c.addi      s6, -1
                  c.li        s0, -1
                  auipc       a7, 420453
                  and         zero, t5, s11
                  ori         a2, t5, -270
                  rem         s10, s1, a2
                  c.addi      s10, 7
                  c.andi      a3, 31
                  and         a7, a7, ra
                  slti        t3, s6, 17
                  nop
                  c.xor       a3, a3
                  auipc       a0, 74024
                  srai        zero, t2, 30
                  c.or        a3, a3
                  lui         s9, 796516
                  sll         zero, a1, t4
                  sra         a1, a5, s7
                  c.srli      a3, 13
                  or          tp, ra, s0
                  and         gp, gp, tp
                  c.and       a5, a4
                  mulhu       a7, s5, t3
                  mulhu       s2, ra, a7
                  slt         a1, s0, a7
                  sltiu       zero, t1, -75
                  c.srai      a0, 19
                  sub         s6, s3, t4
                  c.andi      a3, 25
                  mulhu       s9, t6, ra
                  c.li        s10, 28
                  mul         t0, a5, s0
                  slt         a6, t4, s10
                  c.mv        t0, s5
                  add         s1, tp, a6
                  andi        sp, a2, -419
                  c.and       a3, a3
                  ori         s1, t4, 1577
                  mul         s6, t1, a6
                  lui         t0, 912990
                  srli        s5, s6, 20
                  divu        a4, t2, a5
                  mul         s1, s0, t2
                  rem         t4, s3, s11
                  or          s5, s4, sp
                  c.nop
                  add         a1, a2, a3
                  c.nop
                  slti        zero, a6, 1203
                  and         s6, tp, s9
                  mul         sp, zero, zero
                  divu        sp, t5, a4
                  mulhu       ra, s8, a4
                  xori        a6, a1, -182
                  srli        tp, tp, 20
                  c.addi      ra, 24
                  ori         s2, s10, -300
                  srli        s8, a0, 24
                  c.add       s7, t6
                  sub         zero, a4, s5
                  c.xor       a3, a3
                  c.li        a4, -1
                  c.or        a3, a2
                  mul         a0, t3, a4
                  c.addi4spn  a3, sp, 720
                  c.and       a3, a0
                  mulhsu      t3, t3, s3
                  mulh        s8, zero, s6
                  mulhu       sp, ra, a0
                  c.slli      s6, 23
                  sra         tp, t6, a1
                  c.nop
                  xori        t1, a1, 1694
                  rem         t2, t1, t6
                  slt         t2, a4, gp
                  c.mv        s8, a2
                  slli        zero, t2, 11
                  c.or        a3, a3
                  c.mv        s2, a1
                  or          a3, a2, t5
                  sra         t4, s7, a6
                  c.and       a3, a3
                  xori        s2, sp, 1746
                  c.and       a3, a5
                  or          a7, a1, t6
                  addi        zero, t4, -1859
                  c.srli      a3, 14
                  c.srai      a3, 22
                  c.srli      a3, 31
                  div         s8, t5, s3
                  mulh        zero, ra, a5
                  mulhsu      t3, t0, a5
                  addi        a1, a6, -1978
                  mulhu       t4, t4, sp
                  c.slli      s0, 28
                  mulhsu      t4, s1, s11
                  mulh        s2, s10, t6
                  div         t0, a7, s3
                  c.mv        t4, t2
                  mulh        zero, a6, s9
                  c.xor       a3, a3
                  add         sp, ra, a1
                  mulh        s1, s8, a0
                  c.slli      ra, 21
                  sub         tp, t2, tp
                  c.addi      s2, -1
                  sltiu       sp, s4, -403
                  auipc       s1, 800032
                  sub         a3, a2, sp
                  slli        ra, zero, 24
                  nop
                  c.sub       a3, a3
                  sll         zero, s5, ra
                  rem         sp, s11, sp
                  or          s4, s5, t1
                  or          tp, a0, s9
                  sll         s7, s5, zero
                  c.add       tp, s3
                  and         t3, a7, a7
                  auipc       s5, 855961
                  c.srli      a3, 13
                  c.and       a3, a3
                  div         s8, tp, s8
                  srai        s10, s9, 26
                  divu        a1, t5, s4
                  c.addi16sp  sp, -16
                  c.li        s8, -1
                  mul         a2, s2, a2
                  c.slli      tp, 26
                  mulhsu      a5, a1, ra
                  slti        a7, s9, -1621
                  c.or        a3, a3
                  sltiu       t0, t1, -2041
                  c.li        s1, -1
                  c.xor       a3, a3
                  c.nop
                  auipc       zero, 829363
                  c.nop
                  c.or        a3, a3
                  c.li        a2, 13
                  mul         s5, ra, t4
                  c.addi4spn  a3, sp, 624
                  nop
                  mulh        zero, s8, a0
                  srli        sp, s3, 3
                  c.add       a2, s0
                  c.li        s4, -1
                  xor         s4, gp, t3
                  divu        a6, s3, s7
                  mulh        s2, a5, t5
                  c.addi16sp  sp, -16
                  mul         a3, s2, s6
                  ori         t2, a6, 1027
                  c.andi      a3, -1
                  sll         a5, a4, zero
                  or          t2, t3, s7
                  srli        t3, t1, 4
                  c.lui       ra, 7
                  sltiu       s1, s3, 1931
                  slti        s7, ra, -1886
                  addi        t0, a4, -579
                  sub         s1, s0, t3
                  rem         s7, s3, s10
                  sltu        a0, s11, t1
                  rem         a5, a2, s4
                  andi        s4, ra, -389
                  slli        s0, s0, 0
                  sll         a4, s3, t4
                  c.addi16sp  sp, 176
                  div         s7, gp, t4
                  c.srai      a3, 3
                  addi        s1, s8, 1182
                  divu        s10, s1, s2
                  c.nop
                  c.mv        gp, t0
                  c.slli      a5, 6
                  c.addi16sp  sp, -16
                  slt         s9, a1, s2
                  c.nop
                  c.addi4spn  a3, sp, 416
                  and         s0, tp, s9
                  slti        s6, s6, 994
                  c.addi16sp  sp, 400
                  c.xor       a3, a3
                  rem         a0, s0, t6
                  slli        t4, a4, 28
                  c.srli      a5, 1
                  c.addi4spn  a3, sp, 576
                  c.li        gp, -1
                  c.mv        t2, a7
                  c.sub       a3, a3
                  c.or        a3, a3
                  sltu        gp, ra, a0
                  c.andi      a1, 15
                  slti        s6, s3, -612
                  add         ra, a3, a2
                  sll         t3, s2, s2
                  c.slli      s10, 14
                  sra         s2, s9, s6
                  c.and       a3, a3
                  sra         t1, a4, a1
                  c.or        a3, a2
                  c.addi      a6, -1
                  addi        a0, s11, 1649
                  or          sp, a4, a0
                  nop
                  c.xor       a3, s0
                  andi        zero, s3, -307
                  sltu        gp, s9, s5
                  andi        s4, a7, -1133
                  div         s0, t3, zero
                  mulhu       t4, sp, zero
                  c.lui       s9, 27
                  slti        s8, a0, 1401
                  lui         s1, 279308
                  c.li        ra, -1
                  xor         t2, t6, s2
                  divu        zero, zero, s6
                  mulh        zero, s0, s2
                  rem         a5, s2, s6
                  sltiu       s6, t0, 1930
                  addi        s3, a0, -574
                  andi        s6, s2, 1687
                  addi        zero, s2, 635
                  srli        a3, s11, 25
                  sltiu       s1, t3, 1577
                  mulhu       s7, tp, s11
                  c.xor       a3, a3
                  c.addi      a3, -1
                  andi        a3, t5, 1317
                  c.nop
                  divu        s0, t5, s4
                  or          s7, a0, t1
                  srl         a4, a7, t3
                  c.or        a3, a5
                  xor         s10, a2, t1
                  c.and       a3, a3
                  mulhu       s8, t5, s10
                  divu        zero, tp, s1
                  c.lui       s0, 10
                  mul         s7, s2, a6
                  ori         s3, s5, -1759
                  mulh        s5, s3, a6
                  c.or        a3, a3
                  slti        a6, a3, 906
                  c.lui       a7, 2
                  div         s8, t4, a3
                  sra         a3, t1, s10
                  or          zero, s5, t5
                  sltu        a7, a2, tp
                  sra         a5, sp, sp
                  c.mv        a2, s2
                  sltu        s0, s4, a7
                  c.xor       a3, a5
                  srli        zero, a4, 13
                  ori         zero, a0, -1990
                  lui         a2, 720370
                  and         s8, t3, a6
                  addi        a7, sp, -2025
                  c.slli      a3, 15
                  c.sub       a3, a3
                  andi        t2, s5, 1285
                  nop
                  c.srai      a2, 13
                  c.nop
                  sll         s1, s7, t6
                  or          a5, gp, t1
                  xori        a7, s2, 578
                  c.or        a3, a3
                  c.sub       a3, a3
                  c.srli      a3, 27
                  slt         t2, s4, a3
                  c.xor       a3, a3
                  c.xor       a3, a3
                  c.addi16sp  sp, -16
                  add         ra, a6, ra
                  sltiu       a2, a5, -373
                  c.srli      a3, 24
                  or          a4, s1, t3
                  c.and       a3, a3
                  add         s0, s9, s10
                  divu        zero, t4, a3
                  c.srai      a3, 28
                  srai        t1, t0, 20
                  c.srli      a4, 26
                  c.addi16sp  sp, -16
                  slti        s1, s11, 775
                  srl         s3, a6, a2
                  addi        s8, s7, 890
                  nop
                  or          ra, t5, t0
                  srai        zero, s11, 1
                  nop
                  c.and       a3, a3
                  mul         zero, s6, s10
                  xor         t0, a7, s11
                  and         a0, s6, tp
                  c.srli      a4, 30
                  sltiu       s7, s3, -1495
                  slti        t2, ra, 1966
                  srai        a3, t3, 4
                  c.slli      ra, 8
                  srl         s10, s8, a5
                  c.addi      ra, -1
                  and         t1, a2, a6
                  c.addi16sp  sp, 48
                  lui         a3, 816082
                  lui         s7, 1041125
                  c.srai      a3, 16
                  div         s0, t0, sp
                  srli        sp, t5, 29
                  slti        s4, tp, -949
                  ori         a1, t2, -1289
                  srli        s9, zero, 6
                  auipc       t3, 60771
                  and         a4, a4, s1
                  c.addi      t3, -1
                  sra         s9, a6, s7
                  sltu        t2, s2, a1
                  c.xor       a0, a3
                  c.srai      a3, 2
                  c.addi      t0, 9
                  andi        s7, a6, 593
                  sltu        s4, s2, a3
                  or          a7, t3, t5
                  and         s6, a6, t6
                  ori         t1, s2, -823
                  and         a0, s3, a1
                  c.or        a3, a2
                  rem         s5, a0, tp
                  c.xor       a3, a5
                  nop
                  add         s9, tp, a3
                  c.srli      a5, 22
                  c.srli      a3, 24
                  c.xor       a3, a3
                  mulhsu      a3, t2, a4
                  c.andi      a3, 4
                  c.addi      t3, -1
                  c.mv        t0, s7
                  divu        t2, a3, a4
                  xor         sp, tp, t4
                  c.xor       a3, a3
                  slti        s6, s2, 1947
                  c.nop
                  c.li        s4, -1
                  mulh        t4, a1, s4
                  slli        zero, a0, 22
                  xori        s7, t6, -22
                  and         a6, s1, sp
                  c.li        s1, 4
                  nop
                  slli        zero, s2, 11
                  c.andi      a3, 27
                  c.add       a5, a6
                  mulhsu      a7, a1, ra
                  mulh        t1, a0, t0
                  slti        a0, a4, 340
                  c.sub       a3, a3
                  add         s9, t5, t0
                  c.add       s2, sp
                  auipc       zero, 448813
                  ori         zero, s3, -823
                  mulhsu      ra, s1, s4
                  sltu        zero, s9, a1
                  auipc       ra, 1017581
                  addi        s7, a1, 591
                  rem         t3, s11, s9
                  nop
                  srl         zero, a6, t5
                  sltiu       a2, tp, -1729
                  rem         sp, s6, s11
                  div         s0, t5, s9
                  rem         a5, a5, t5
                  or          s10, s4, a7
                  rem         a5, sp, s6
                  sra         tp, t5, zero
                  c.li        a5, 12
                  srai        zero, s6, 16
                  c.addi4spn  a5, sp, 832
                  srl         zero, gp, t3
                  sub         t3, s8, t4
                  srai        s0, s11, 25
                  c.li        s4, 12
                  slt         zero, a1, sp
                  add         a7, a4, a4
                  mulhsu      zero, a2, t5
                  c.li        ra, 21
                  c.lui       ra, 31
                  slt         a2, a2, a3
                  rem         s8, t5, a2
                  c.add       t2, t5
                  c.srai      a3, 17
                  c.slli      a0, 2
                  rem         gp, tp, s0
                  c.andi      a1, 20
                  lui         t1, 269523
                  ori         s1, s11, -1731
                  lui         zero, 413119
                  sltiu       zero, s7, -358
                  c.lui       s8, 22
                  slti        s8, s11, 1674
                  srai        zero, s10, 11
                  c.slli      a1, 15
                  c.add       t2, s0
                  slt         ra, t5, sp
                  c.srli      a3, 6
                  c.addi4spn  a3, sp, 96
                  rem         t3, a1, s4
                  xor         s10, s2, s1
                  auipc       zero, 713961
                  c.srai      a3, 10
                  c.lui       ra, 30
                  mulhu       a3, a4, a5
                  mul         a7, t1, a7
                  c.srai      a3, 17
                  add         a1, a4, s10
                  xor         s2, a0, a1
                  rem         s9, a3, s2
                  c.or        a1, a3
                  c.sub       a3, a3
                  mul         a2, t4, s9
                  srli        s1, t2, 13
                  mulhu       zero, a7, t4
                  c.srai      a2, 4
                  rem         s5, zero, s6
                  srai        a1, s9, 23
                  mulh        s6, s0, tp
                  add         t0, s1, a7
                  auipc       s3, 337186
                  srai        a6, ra, 7
                  c.and       a3, a2
                  c.addi      s8, -1
                  auipc       t1, 57973
                  srai        ra, tp, 4
                  mulhsu      s0, a0, s5
                  auipc       zero, 220562
                  slt         a7, a1, gp
                  srl         a2, s7, a1
                  or          t0, a2, s11
                  and         sp, a3, sp
                  srli        a5, a1, 14
                  c.addi4spn  a3, sp, 320
                  lui         t0, 870331
                  lui         s10, 407516
                  mulh        a6, t1, a3
                  ori         t2, t1, 1327
                  mul         ra, t0, ra
                  lui         s1, 184564
                  c.nop
                  c.and       a3, a3
                  divu        a2, s1, s8
                  c.srai      a2, 20
                  srl         s6, a5, t2
                  or          gp, a0, a7
                  and         a4, t5, a4
                  c.addi16sp  sp, 144
                  sub         a4, s11, zero
                  div         s5, a3, t1
                  nop
                  and         s10, t0, s4
                  c.and       a3, a3
                  sll         s3, s11, tp
                  srai        s6, t6, 12
                  slt         a6, s4, zero
                  xori        s6, gp, 1559
                  c.li        t1, -1
                  c.srai      a1, 16
                  c.lui       s3, 21
                  c.addi16sp  sp, 16
                  sltiu       t0, t2, -367
                  c.add       ra, s10
                  auipc       t4, 299739
                  slti        t3, s1, -1740
                  slti        s10, s8, 1282
                  sltiu       s4, s1, -1868
                  andi        a6, t2, -1516
                  or          s3, s0, a7
                  c.add       t3, t6
                  c.xor       a3, a1
                  c.nop
                  c.srli      a3, 4
                  and         zero, s11, a0
                  slt         a7, s8, ra
                  andi        t2, s3, 146
                  divu        t3, a3, zero
                  mul         s3, tp, s6
                  addi        t0, s2, -1017
                  and         ra, t4, s6
                  sub         s7, t5, t0
                  addi        t0, s5, 47
                  mulh        a4, sp, gp
                  c.mv        s2, s4
                  addi        ra, a5, -1023
                  slt         a0, s6, s7
                  c.slli      s7, 7
                  div         tp, a7, t3
                  c.srli      a0, 11
                  c.andi      a3, -1
                  mulh        a6, zero, t0
                  srli        ra, a7, 31
                  sra         s7, t2, t5
                  or          t3, s1, s4
                  or          s7, t0, t0
                  c.xor       a3, a3
                  and         s10, sp, s3
                  slt         t0, a2, a7
                  addi        a7, a6, 31
                  srl         s10, s0, s2
                  mulhu       s10, ra, s7
                  c.and       a3, a3
                  lui         zero, 241921
                  srli        zero, s2, 13
                  c.addi      s8, -1
                  mulhsu      gp, s10, a2
                  lui         s1, 304055
                  addi        zero, s3, -1527
                  slti        zero, a5, 543
                  c.andi      a3, 29
                  c.sub       a3, a3
                  srl         s7, s8, zero
                  c.andi      a3, -1
                  add         s4, s11, tp
                  slli        ra, s7, 23
                  add         t1, t1, t6
                  c.li        t1, -1
                  mul         t2, s4, a4
                  auipc       s10, 649696
                  sltu        t3, s8, t5
                  slti        s9, s8, 886
                  mulh        a1, t1, a1
                  c.li        s0, -1
                  mulh        s7, t1, s1
                  c.andi      a3, 16
                  auipc       a5, 179743
                  mul         ra, a7, a1
                  c.nop
                  divu        gp, a3, a6
                  div         a0, s5, s0
                  srl         s9, a7, ra
                  div         s6, s3, t1
                  sub         s5, s7, t5
                  c.or        a3, a3
                  c.slli      t2, 1
                  c.li        ra, -1
                  addi        s4, t0, 31
                  c.slli      a6, 15
                  srai        a6, t3, 4
                  c.addi      a2, -1
                  div         s2, t4, s0
                  c.sub       a3, a3
                  sra         t0, a0, a3
                  add         s3, a3, s10
                  srli        gp, s9, 29
                  sub         s3, a4, a3
                  c.mv        sp, s6
                  c.and       a3, a3
                  lui         s3, 167818
                  ori         s4, zero, 883
                  srl         s9, s2, zero
                  c.andi      a3, -1
                  c.lui       ra, 28
                  sltu        sp, zero, a3
                  ori         sp, t4, 1523
                  addi        s10, s9, 1873
                  c.add       t1, s5
                  or          t3, s7, s5
                  div         s6, t6, a2
                  c.li        s2, -1
                  c.mv        a2, tp
                  slli        s3, a0, 2
                  sltu        s6, tp, a6
                  rem         t3, s9, sp
                  rem         a3, s3, s4
                  sltu        zero, t2, gp
                  c.or        a2, a5
                  c.addi4spn  a3, sp, 96
                  sub         s8, zero, s8
                  and         zero, gp, s7
                  slti        a1, a6, 1888
                  c.srai      a3, 15
                  slti        t0, a2, 1052
                  c.andi      a3, 13
                  slti        a5, s11, -568
                  slli        t0, a4, 4
                  slt         t3, s7, a4
                  srai        tp, tp, 2
                  c.sub       a4, a3
                  sub         t3, a1, t5
                  c.lui       s10, 1
                  rem         t4, a6, s11
                  nop
                  div         t4, a1, s10
                  c.addi      s10, -1
                  slti        zero, t6, 925
                  c.and       a2, a3
                  c.addi4spn  s0, sp, 896
                  c.xor       a3, a3
                  andi        tp, a7, -276
                  lui         zero, 217080
                  c.li        s8, -1
                  lui         s1, 628629
                  c.lui       gp, 10
                  mulhu       zero, a4, a2
                  sltu        s8, t3, t5
                  c.lui       ra, 20
                  c.srli      a0, 20
                  c.or        a3, a3
                  c.add       s3, a7
                  c.sub       a3, a3
                  c.sub       a3, s0
                  auipc       a0, 505982
                  c.addi16sp  sp, 256
                  c.and       a3, a3
                  srai        a3, t2, 27
                  or          s0, s10, s4
                  sll         zero, t0, s5
                  lui         s0, 450836
                  divu        s10, s5, a7
                  mulhsu      sp, a2, s11
                  xor         s2, s9, ra
                  sub         s9, s11, a3
                  srli        s6, zero, 29
                  mulhu       a5, t5, t0
                  lui         s10, 324284
                  c.sub       a3, a3
                  sltiu       zero, t6, 1394
                  c.nop
                  mulhsu      zero, t0, s4
                  slli        s8, s4, 7
                  c.srli      a3, 1
                  sub         a6, a1, s2
                  mulhsu      s3, s8, s3
                  mulhsu      a0, t1, s8
                  c.sub       a3, a3
                  c.addi16sp  sp, 192
                  srli        zero, s11, 14
                  sltu        s2, a5, a7
                  xor         s2, s0, s5
                  c.mv        a7, t1
                  srl         zero, s9, t2
                  c.mv        t2, a3
                  srl         zero, s0, a2
                  srli        t2, zero, 8
                  slli        tp, t4, 31
                  slti        s7, sp, -1572
                  div         sp, s8, a7
                  slt         s2, gp, gp
                  c.srai      a3, 14
                  sll         zero, s9, a0
                  c.li        s7, 9
                  sltu        a6, s8, s3
                  c.addi4spn  a0, sp, 640
                  c.mv        t3, s5
                  sub         s0, t5, s1
                  c.nop
                  or          s2, s3, s0
                  sltiu       a3, a4, 399
                  c.sub       a3, a3
                  xor         t1, s2, a3
                  c.mv        a3, tp
                  c.srai      a3, 23
                  c.li        t0, -1
                  c.xor       a5, a2
                  c.or        a3, a3
                  or          s5, s6, s9
                  sltu        s3, t6, zero
                  slli        tp, gp, 0
                  c.andi      a3, 28
                  sub         zero, t6, t4
                  slti        t0, s6, 349
                  c.srai      a3, 23
                  srl         a7, ra, s11
                  c.andi      a3, -1
                  srli        s4, a0, 2
                  c.addi16sp  sp, 64
                  c.lui       a7, 19
                  slli        a2, t4, 18
                  c.nop
                  srl         a1, tp, t0
                  srai        s7, t1, 12
                  nop
                  c.slli      s10, 11
                  c.addi      ra, 14
                  addi        s3, a1, 1985
                  mul         s10, tp, t4
                  srai        t4, t6, 27
                  sltiu       s2, zero, 1877
                  c.srai      a1, 30
                  sra         s7, s10, s10
                  c.addi      a3, 16
                  sltiu       a7, s7, 1049
                  sltiu       a1, a1, 1801
                  c.nop
                  c.addi16sp  sp, -16
                  c.srli      a3, 28
                  mulhsu      t3, s7, s0
                  lui         a0, 469348
                  c.srai      a3, 15
                  divu        s4, a6, t1
                  c.add       s5, t5
                  srl         gp, a1, sp
                  srai        s7, a2, 16
                  c.sub       a3, a3
                  mulhsu      a0, s10, s1
                  slli        zero, sp, 29
                  sltiu       zero, s10, 229
                  c.nop
                  sltiu       a3, s1, 745
                  mulhu       s9, a6, gp
                  c.xor       a3, a3
                  mul         zero, t2, s8
                  mul         s0, s8, ra
                  sltiu       a1, tp, 245
                  slt         s1, s3, s4
                  slt         ra, zero, t1
                  mul         a2, s8, t2
                  mulh        s1, ra, s7
                  mulhsu      s6, a6, s11
                  c.and       a3, a3
                  srli        s8, t0, 30
                  c.srai      a3, 27
                  srli        s4, zero, 22
                  sub         t1, s8, t0
                  and         zero, s7, t4
                  nop
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_1
                  li         t3, 0x1
                  li         s10, 0x0
                  li         t0, 0x1
                  li         a0, 0x1
                  li         a7, 0x0
                  li         sp, 0x72c074f4
                  li         s8, 0x0
                  li         s3, 0x1
                  li         s2, 0x1
                  c.addi16sp  sp, -16
                  rem         s4, zero, a5
                  c.add       t0, a0
                  mul         s8, s4, a7
                  c.addi16sp  sp, 160
                  c.mv        a1, s11
                  auipc       zero, 618771
                  nop
                  c.li        t4, -1
                  mulhu       gp, s0, s0
                  mulhsu      s5, a7, s3
                  lui         gp, 981528
                  c.addi16sp  sp, -16
                  nop
                  sub         s7, s7, a3
                  auipc       zero, 331486 #end riscv_int_numeric_corner_stream_1
                  or          a1, a6, s8
                  c.or        a3, a3
                  sltiu       a7, s11, -598
                  auipc       a3, 836823
                  mulhsu      t0, s4, s9
                  mulh        s2, a0, t2
                  sll         s9, s2, t0
                  c.and       a3, a3
                  c.lui       tp, 6
                  nop
                  sltiu       s6, sp, 1631
                  xori        t2, sp, -638
                  sltiu       zero, s8, 1154
                  srl         zero, zero, a7
                  c.addi16sp  sp, -16
                  or          sp, a7, a3
                  sltiu       a6, s6, -902
                  rem         s7, a6, s2
                  addi        s5, t1, 893
                  auipc       t2, 325623
                  srli        a3, s7, 19
                  srl         s4, a0, a0
                  auipc       a0, 972463
                  slti        a5, t2, 1048
                  addi        zero, s6, -1635
                  c.or        a5, a3
                  c.xor       a3, a3
                  c.or        a3, a3
                  addi        a2, t0, -1304
                  c.andi      a3, -1
                  c.li        s7, -1
                  div         t2, s1, s9
                  sub         a6, s6, t3
                  c.srli      a3, 26
                  c.sub       s0, a3
                  mulh        a1, a1, s10
                  c.andi      s1, 12
                  sltiu       s0, a5, -580
                  sltu        s5, t5, s1
                  c.xor       a2, a3
                  mulhsu      s2, s1, ra
                  c.mv        s6, s5
                  slti        tp, t4, 403
                  sll         zero, t5, t4
                  div         a7, a5, s8
                  rem         t3, t5, s1
                  andi        s5, a4, -2044
                  xor         a4, zero, s3
                  c.andi      a3, 13
                  and         zero, s0, a2
                  c.sub       a3, a3
                  sll         s2, t5, ra
                  c.lui       ra, 3
                  srai        a2, t4, 11
                  c.addi4spn  a3, sp, 720
                  xori        a7, s2, 242
                  lui         s8, 1047320
                  c.sub       a3, a3
                  slli        gp, s1, 20
                  div         a1, a4, t4
                  sub         s8, s10, t1
                  c.andi      a3, -1
                  lui         a2, 513698
                  rem         s9, a3, sp
                  c.and       a3, a3
                  lui         tp, 241008
                  c.lui       a3, 2
                  mul         a0, s7, sp
                  srai        s2, gp, 3
                  lui         zero, 238191
                  c.addi      s9, 1
                  c.or        a3, a3
                  div         s10, t1, t3
                  mul         a5, t2, a0
                  c.srli      a5, 25
                  srl         a3, ra, a6
                  rem         zero, t5, t6
                  c.xor       a3, a2
                  divu        sp, a0, s9
                  sra         tp, s8, gp
                  sltiu       s4, a1, -1966
                  xor         s10, t1, s11
                  c.nop
                  c.nop
                  c.andi      a3, -1
                  and         a0, a4, s8
                  c.or        a0, a3
                  sra         a5, zero, s4
                  c.xor       a3, a3
                  divu        a4, a4, s8
                  sltiu       ra, zero, -1351
                  xori        a5, s10, 81
                  sltu        a3, s10, s5
                  srli        a7, s11, 9
                  c.and       a3, a3
                  sub         tp, tp, s3
                  c.and       a3, a3
                  c.or        a3, a3
                  mulhu       zero, s10, s2
                  divu        ra, s7, gp
                  and         s3, s10, t6
                  xori        a5, t3, -1782
                  mulhu       s7, s1, s0
                  mulh        s10, s5, tp
                  c.addi      a5, 16
                  sll         t1, s10, ra
                  rem         t0, s2, sp
                  sll         zero, gp, s1
                  lui         s3, 978573
                  lui         zero, 752191
                  c.addi16sp  sp, -16
                  rem         a2, a2, s10
                  sub         tp, s0, a3
                  mul         zero, t1, s9
                  divu        zero, s9, t6
                  c.li        t1, 4
                  rem         a6, gp, s10
                  srli        tp, a7, 1
                  slli        s0, s2, 6
                  c.li        a1, 25
                  c.sub       a3, a3
                  srl         a0, a3, s1
                  divu        a7, sp, a7
                  mulhu       s4, gp, s4
                  slti        s8, t5, -356
                  slt         zero, s7, s10
                  sll         s10, a5, a4
                  mulhu       s6, a3, ra
                  mulhsu      sp, tp, a4
                  divu        t4, sp, a3
                  lui         t2, 435014
                  mulhu       a3, t6, s6
                  mulhsu      s0, ra, s10
                  c.srli      a3, 26
                  slti        a1, a7, 1392
                  lui         gp, 933035
                  and         s4, a3, tp
                  sra         gp, ra, t5
                  c.srli      a3, 24
                  mulh        a3, a0, a4
                  c.andi      a3, -1
                  mul         t2, a4, s0
                  mulhu       s8, a3, zero
                  sltu        s3, s8, t6
                  c.srli      a3, 3
                  andi        s5, s8, 1154
                  ori         t4, t4, 1238
                  auipc       s7, 75013
                  addi        a3, s7, 1284
                  or          zero, t5, tp
                  xor         tp, s1, s11
                  c.andi      a3, -1
                  ori         a3, t2, -1672
                  or          s2, ra, s10
                  auipc       s8, 712106
                  xor         zero, s10, s1
                  c.andi      a3, 18
                  and         s6, s7, t4
                  mulhsu      s0, a6, a1
                  auipc       a0, 173964
                  andi        a3, t0, -1456
                  sltu        t0, a6, sp
                  slti        a6, tp, -1876
                  mul         t1, tp, a6
                  mulhu       s9, t1, tp
                  add         s7, s7, a6
                  c.srli      a5, 31
                  sub         zero, a5, s6
                  addi        zero, sp, 618
                  slli        t0, s5, 28
                  add         gp, t5, s8
                  xori        t3, gp, -1232
                  sll         zero, s7, a6
                  andi        a2, s0, 747
                  xor         ra, s8, s6
                  divu        t2, sp, s4
                  ori         t0, s0, 25
                  lui         s3, 653597
                  c.lui       t2, 5
                  c.li        t0, 31
                  ori         a4, t1, 1762
                  and         ra, s1, s3
                  slli        s8, a7, 24
                  addi        a6, a2, 2004
                  slt         gp, a5, a4
                  mulh        s5, a0, a3
                  c.addi4spn  a3, sp, 320
                  rem         a0, gp, t4
                  sltiu       s1, ra, -1201
                  div         s4, s1, t6
                  sltiu       gp, s4, 1939
                  c.li        ra, -1
                  srai        a3, s7, 11
                  mulhsu      s4, a3, a7
                  c.add       a1, s10
                  sltiu       zero, a4, 336
                  mul         zero, s0, t1
                  addi        a5, a2, -674
                  rem         s1, s0, t1
                  c.li        tp, 9
                  c.addi      a1, 4
                  c.addi4spn  a3, sp, 64
                  xor         a6, s0, a5
                  mulhu       a2, t1, a6
                  sltu        zero, a7, a2
                  c.lui       t1, 9
                  c.li        a5, 14
                  slli        zero, s5, 9
                  c.add       t1, t1
                  sltu        s6, s8, s1
                  rem         s2, s6, t5
                  mulhsu      a1, t4, s0
                  mulh        s9, t1, s3
                  sltu        a7, ra, a4
                  mulh        ra, a0, s3
                  mulh        zero, a4, t1
                  or          s9, t4, s3
                  srli        a5, t3, 21
                  c.slli      s2, 20
                  srli        s10, t0, 9
                  xori        zero, a7, -1395
                  auipc       s9, 566421
                  c.xor       a3, a3
                  ori         sp, a1, -637
                  andi        s2, s10, -1176
                  sltiu       zero, s6, 1769
                  div         zero, a7, s8
                  mul         a2, s5, t0
                  sub         t1, t1, s10
                  srli        a0, s7, 24
                  mul         s8, a7, ra
                  mulhsu      s4, a2, t4
                  slli        zero, gp, 6
                  addi        zero, ra, -842
                  div         s9, t4, zero
                  c.lui       t0, 16
                  c.or        a3, a3
                  c.sub       s1, a3
                  c.and       a3, a4
                  srai        s5, a2, 2
                  sltu        a4, ra, s9
                  slt         s10, tp, t2
                  srai        a0, s11, 4
                  c.slli      t0, 23
                  mulhu       s6, a6, ra
                  c.add       t1, a1
                  slt         zero, sp, t1
                  andi        s10, s2, -859
                  divu        zero, s10, t3
                  div         a3, s5, a3
                  mulh        s2, a2, a2
                  c.and       a3, a3
                  mul         s5, s10, a5
                  srl         zero, zero, a6
                  c.andi      a3, 30
                  c.slli      t1, 2
                  slli        s10, s4, 2
                  auipc       zero, 151858
                  slti        a2, a6, -9
                  c.slli      a0, 11
                  c.addi16sp  sp, 224
                  div         t0, s11, s0
                  mulhu       ra, gp, s2
                  c.srai      a3, 25
                  sltiu       a6, s6, -388
                  sll         s5, a1, a6
                  mulh        s6, t4, s1
                  c.addi16sp  sp, 192
                  rem         a5, a6, s1
                  auipc       s1, 685919
                  c.andi      s0, 5
                  sltiu       zero, t1, -56
                  sltu        s10, t1, a0
                  c.addi      t1, 13
                  c.addi16sp  sp, 320
                  c.add       t1, a6
                  sub         zero, s4, gp
                  srl         s9, s7, a5
                  auipc       s10, 706454
                  div         t4, s9, a1
                  addi        a3, t5, 1140
                  sltu        s7, a1, s1
                  srai        s2, tp, 30
                  srli        a3, s6, 13
                  div         s2, a0, sp
                  nop
                  c.andi      a3, -1
                  ori         tp, s4, -505
                  auipc       s1, 822623
                  mul         s6, s8, t2
                  srl         t4, a6, ra
                  c.nop
                  or          t3, a5, t4
                  sra         tp, s10, t2
                  slt         t4, a4, a3
                  c.or        a3, a4
                  c.slli      t2, 19
                  mulhsu      a7, s8, a5
                  srli        t2, a7, 21
                  c.srli      a3, 19
                  sll         t4, s10, a0
                  c.xor       a3, a3
                  sltu        s3, t1, s5
                  c.srai      a3, 17
                  rem         a5, s11, t2
                  srli        tp, s6, 27
                  c.mv        t0, ra
                  lui         t2, 818866
                  slli        a0, s11, 13
                  c.xor       a3, a0
                  slli        a5, t6, 17
                  c.li        a2, 15
                  rem         a5, t2, a4
                  c.xor       a3, a3
                  c.srai      a3, 2
                  nop
                  sll         s6, sp, s2
                  c.and       s0, a3
                  mulhu       sp, gp, a1
                  c.and       a3, a0
                  c.lui       t3, 21
                  c.add       a3, s9
                  srli        a7, s5, 16
                  c.and       a5, a3
                  xor         a4, s2, t3
                  c.sub       a3, a3
                  mul         a4, tp, a1
                  addi        t1, t0, -1943
                  or          s5, t3, zero
                  c.mv        a3, tp
                  slli        zero, tp, 28
                  c.or        a3, a3
                  c.slli      s4, 23
                  srai        a6, s4, 18
                  c.addi      t0, -1
                  slt         s4, s6, gp
                  c.mv        ra, s2
                  or          a3, sp, tp
                  slt         a0, zero, s6
                  andi        sp, s3, 202
                  srli        t1, t1, 11
                  slti        zero, sp, -1855
                  sub         a3, s2, t4
                  srl         s1, t6, t6
                  sra         a2, t6, s1
                  lui         gp, 167858
                  sra         a3, s0, t0
                  c.li        s1, 12
                  andi        t2, t5, 201
                  c.mv        s9, s11
                  c.andi      a3, 29
                  sltiu       a3, s1, 1266
                  c.slli      s2, 14
                  srli        s1, s1, 18
                  xori        s2, a6, 404
                  and         s5, ra, s10
                  c.addi      a4, -1
                  add         s2, s6, t6
                  c.srai      a3, 31
                  srl         zero, t0, a2
                  sra         a4, s1, s0
                  c.addi16sp  sp, 432
                  nop
                  sltiu       ra, t3, -826
                  auipc       a1, 823659
                  rem         zero, tp, s9
                  rem         s7, a1, sp
                  c.addi      a5, -1
                  sll         s1, a6, s11
                  c.li        t3, 0
                  sra         ra, s5, a6
                  sub         t2, s9, s2
                  slti        s1, a2, -1219
                  div         a4, a6, a4
                  auipc       zero, 868121
                  divu        a4, gp, t1
                  srl         zero, gp, a5
                  c.nop
                  c.andi      a3, -1
                  divu        s2, a1, s3
                  slti        a5, t0, 652
                  c.andi      a3, -1
                  c.addi4spn  a3, sp, 1008
                  c.mv        a5, tp
                  c.andi      a3, -1
                  andi        s4, s4, 1461
                  c.and       a3, a0
                  srl         s5, s10, ra
                  c.sub       a3, a3
                  ori         a0, a1, 366
                  sltu        s7, s9, s6
                  srli        t2, a1, 9
                  c.or        a3, a3
                  rem         gp, ra, gp
                  c.lui       tp, 28
                  c.addi16sp  sp, 80
                  c.or        a3, a3
                  c.lui       a0, 15
                  c.slli      ra, 15
                  addi        s0, a7, 518
                  c.sub       a3, a3
                  c.addi4spn  a3, sp, 320
                  mulhsu      s4, a5, s11
                  c.xor       a3, a3
                  andi        s2, s8, -1359
                  c.sub       a3, s0
                  mulhu       s5, t2, tp
                  c.or        a5, a3
                  andi        s8, tp, -928
                  sub         s3, a0, ra
                  sub         gp, a5, t1
                  mulh        s0, s6, ra
                  mul         a3, s6, s7
                  srai        zero, sp, 10
                  auipc       zero, 557323
                  c.addi      t0, -1
                  c.nop
                  c.addi16sp  sp, -16
                  div         a1, s10, zero
                  sub         s3, tp, gp
                  auipc       s7, 676737
                  c.lui       ra, 29
                  andi        s7, gp, 779
                  mul         s7, gp, a2
                  c.addi      s1, 9
                  lui         a1, 200504
                  ori         zero, ra, 1961
                  c.srai      a3, 10
                  auipc       a1, 491346
                  c.slli      a4, 25
                  c.slli      s1, 14
                  c.add       a4, t6
                  add         a7, t6, a0
                  sltiu       s4, t4, 1511
                  c.sub       a5, a3
                  sll         s8, a2, gp
                  srai        zero, sp, 4
                  sltiu       zero, a5, 1157
                  and         t0, s5, ra
                  c.add       a7, a0
                  sltu        s1, t3, s3
                  c.li        ra, 13
                  c.srai      a3, 23
                  ori         t2, sp, 1862
                  sltu        zero, t2, s9
                  sub         a0, t5, a7
                  c.li        a2, 0
                  sll         s8, s3, t1
                  c.li        s6, -1
                  mulhsu      t0, a6, s8
                  sra         a2, t5, t5
                  c.srai      a3, 26
                  sltiu       gp, sp, -845
                  lui         a3, 784104
                  sltiu       s3, sp, 1165
                  or          s2, s5, s5
                  divu        a0, s11, t2
                  nop
                  c.mv        t2, s1
                  c.andi      a1, -1
                  addi        a4, gp, -1996
                  lui         s4, 900143
                  c.addi4spn  a3, sp, 320
                  sra         a3, a5, zero
                  sra         zero, sp, ra
                  slli        s7, ra, 12
                  rem         s4, t2, t1
                  srli        a2, s3, 0
                  sll         t1, t2, tp
                  mulhsu      a1, s10, s3
                  mulh        zero, t6, zero
                  sll         a1, s2, t1
                  c.slli      ra, 29
                  c.or        a3, a3
                  xori        s5, s8, -607
                  mulhsu      s8, gp, t3
                  or          tp, s3, s9
                  slli        a0, zero, 5
                  or          s4, s6, s10
                  slt         s4, sp, a4
                  c.nop
                  mulhu       t2, s8, t3
                  c.srli      a3, 2
                  mulh        zero, s10, a6
                  srai        s9, s3, 3
                  c.li        gp, -1
                  slt         t3, s4, t4
                  and         a2, a5, a1
                  auipc       s1, 960592
                  auipc       s6, 633640
                  andi        a7, a7, 131
                  mulhsu      tp, s4, a0
                  rem         t1, ra, s5
                  slt         s5, s1, tp
                  xor         t3, s6, a3
                  c.or        a3, a3
                  divu        zero, a7, s0
                  c.addi4spn  a0, sp, 464
                  c.add       a0, s10
                  rem         a6, a0, a6
                  c.andi      a3, -1
                  srli        zero, a2, 6
                  and         zero, ra, ra
                  nop
                  c.slli      t0, 20
                  addi        s2, a7, 27
                  c.andi      a3, 6
                  ori         s2, t0, 1569
                  c.addi16sp  sp, 48
                  xori        s1, s2, -217
                  div         zero, a4, t1
                  mulh        a4, a2, s9
                  lui         ra, 953279
                  andi        s5, s10, -481
                  mulh        a1, ra, t2
                  c.srai      a3, 2
                  andi        s4, s11, 1278
                  and         zero, s9, tp
                  c.addi      a5, 1
                  mul         t2, s2, a3
                  c.slli      ra, 17
                  mulh        a4, s6, s5
                  c.and       a3, a3
                  sltu        zero, a7, gp
                  c.addi16sp  sp, -16
                  andi        a4, s11, 843
                  addi        t2, t2, -1568
                  c.xor       a3, s0
                  auipc       a5, 553025
                  c.li        s1, -1
                  c.lui       a7, 18
                  slt         gp, a2, s9
                  c.addi16sp  sp, 320
                  c.or        a3, a4
                  srai        gp, ra, 4
                  srai        a4, s8, 29
                  or          s2, zero, a7
                  mulhsu      s8, s5, t6
                  srl         a7, t3, zero
                  and         zero, s2, a4
                  slti        t3, s0, -956
                  mulhu       s7, s3, s3
                  slli        t2, a1, 25
                  c.srai      a0, 2
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_20
                  li         t3, 0x0
                  li         s10, 0x53be4c50
                  li         ra, 0x0
                  li         s5, 0x0
                  li         s9, 0x0
                  li         s1, 0x0
                  li         a7, 0x0
                  li         s2, 0x0
                  li         a1, 0x1
                  mulhu       s1, s6, a5
                  c.mv        ra, ra
                  addi        zero, s0, 86
                  c.mv        s8, ra
                  c.addi      a5, 16
                  sub         s10, tp, sp
                  c.li        t2, 18
                  auipc       a5, 1004474
                  mulhu       t4, sp, t0
                  mul         s8, tp, s10
                  c.addi4spn  a3, sp, 64
                  auipc       s6, 932957
                  mulhu       t1, a2, t2
                  mulh        gp, s3, t4
                  lui         a0, 265830 #end riscv_int_numeric_corner_stream_20
                  auipc       s8, 720936
                  divu        t1, s11, a3
                  xori        a7, s11, -1301
                  xori        t2, a4, -1153
                  c.or        a4, a3
                  rem         zero, s6, t5
                  sra         tp, s0, s11
                  c.mv        ra, gp
                  sltiu       s10, gp, -859
                  c.li        ra, 31
                  sub         s5, s11, sp
                  c.sub       a3, a3
                  ori         s5, a6, -915
                  c.addi16sp  sp, -16
                  c.addi      t2, -1
                  mulhu       s10, s1, a0
                  mul         a3, t0, tp
                  c.srli      a3, 13
                  xor         zero, t5, t4
                  mulhu       zero, tp, s10
                  div         ra, zero, s5
                  c.sub       a3, a5
                  srl         s2, t0, ra
                  sltu        s7, tp, a0
                  slli        zero, a1, 6
                  lui         a3, 1006628
                  nop
                  mulhu       s5, s6, a5
                  c.addi      a6, -1
                  divu        a2, zero, sp
                  slli        a0, s9, 11
                  c.mv        a7, a0
                  sra         a2, s11, a5
                  c.nop
                  srl         t4, tp, a2
                  c.and       a3, a3
                  c.addi      s4, 23
                  c.and       a3, a3
                  slt         s10, t2, s9
                  c.add       t2, sp
                  sltu        a6, t2, a2
                  mulhu       a5, s0, s1
                  mul         s7, s10, a2
                  rem         t0, s3, t2
                  auipc       a1, 666732
                  c.xor       a3, a3
                  slli        s5, s2, 18
                  c.nop
                  c.mv        t4, a4
                  c.srli      s0, 10
                  slli        s0, a0, 9
                  c.srli      a3, 26
                  lui         sp, 730624
                  rem         t3, s5, s7
                  srai        s0, s2, 8
                  c.srli      a3, 25
                  c.addi      s4, 27
                  srai        a0, s10, 9
                  addi        tp, a2, -93
                  c.srai      a3, 12
                  and         a2, zero, s10
                  c.lui       ra, 14
                  c.or        a3, a0
                  mul         s1, ra, s10
                  sll         a4, a6, s6
                  lui         s7, 639469
                  c.addi4spn  a3, sp, 640
                  c.sub       a3, a3
                  c.srai      a3, 10
                  addi        a6, tp, -168
                  c.addi      s6, -1
                  sra         ra, ra, a5
                  divu        a1, tp, zero
                  and         s2, s1, s10
                  c.andi      a3, 17
                  c.or        a3, a3
                  mulhsu      s4, t1, s9
                  nop
                  c.mv        a5, t6
                  nop
                  srli        t0, s2, 7
                  c.nop
                  slli        a0, s10, 14
                  c.srai      a4, 9
                  div         gp, a3, s8
                  addi        t1, a5, 322
                  mulhsu      s6, s1, a3
                  divu        a2, s8, s4
                  c.xor       a3, a3
                  c.andi      a3, -1
                  c.li        s10, 26
                  xor         a3, t0, t6
                  sltu        ra, s0, a0
                  srl         s5, a6, a1
                  auipc       s7, 326748
                  c.mv        s6, sp
                  slli        t3, s8, 14
                  mulhu       s7, a0, tp
                  slti        a3, s1, 5
                  rem         gp, sp, zero
                  c.mv        s10, a1
                  sub         gp, a4, s6
                  xori        s7, a3, -1639
                  srai        a3, s2, 16
                  slt         s7, ra, s5
                  c.and       a3, a3
                  auipc       zero, 160646
                  c.add       s1, s11
                  xor         s6, a5, t1
                  sll         tp, s5, ra
                  and         s1, s1, s10
                  slli        tp, zero, 11
                  xori        tp, zero, -1800
                  lui         a1, 547083
                  lui         a6, 483130
                  srai        a3, t0, 4
                  c.srli      a4, 26
                  xor         ra, sp, s4
                  c.addi4spn  a3, sp, 624
                  sub         s3, s9, s3
                  lui         t3, 279759
                  mul         tp, a6, a2
                  divu        s3, tp, s8
                  c.addi16sp  sp, -16
                  rem         zero, s9, s0
                  c.addi16sp  sp, 208
                  mulhu       s6, zero, sp
                  nop
                  sll         s9, a3, t4
                  c.xor       a3, a3
                  sltiu       a0, t6, -974
                  sra         a3, s7, tp
                  c.srai      a3, 14
                  srli        ra, s4, 26
                  andi        zero, a2, 1338
                  c.li        ra, 16
                  c.addi4spn  a2, sp, 960
                  c.addi      sp, 4
                  c.nop
                  div         s6, gp, a1
                  c.addi      gp, 13
                  sltu        s1, ra, s9
                  mulhsu      a5, a2, a2
                  rem         s7, a3, s11
                  divu        s5, t6, sp
                  c.addi      s6, 29
                  c.srai      a3, 12
                  c.addi4spn  a3, sp, 320
                  srl         s5, a5, s1
                  c.addi16sp  sp, -16
                  divu        s9, ra, a2
                  addi        gp, s9, -585
                  and         ra, s4, s3
                  c.addi4spn  a3, sp, 384
                  sra         a3, t2, s1
                  nop
                  lui         s4, 97315
                  andi        ra, a2, -1457
                  c.andi      a3, -1
                  c.sub       a3, a3
                  divu        sp, a7, gp
                  addi        a1, a0, -762
                  c.mv        s6, s3
                  c.sub       a3, a3
                  srai        t0, s5, 26
                  or          t2, t5, a5
                  mul         a1, a5, gp
                  c.nop
                  c.add       s8, sp
                  add         gp, s11, sp
                  sra         s5, t5, s7
                  c.andi      a3, 27
                  ori         s2, s3, 507
                  addi        s1, s8, 2029
                  xori        a7, a6, -1792
                  mul         zero, t6, tp
                  addi        a7, t5, 1689
                  div         a7, s3, a4
                  sll         s8, s8, s4
                  c.nop
                  c.srli      a3, 19
                  c.srli      a3, 29
                  sub         s9, a2, s10
                  c.srai      a3, 4
                  divu        tp, ra, s0
                  nop
                  add         s10, a6, a0
                  c.srai      a3, 27
                  rem         t0, a3, a6
                  ori         s9, tp, -760
                  sra         s3, s10, t4
                  sltu        t4, ra, t2
                  c.lui       s9, 2
                  sltiu       t2, s2, 1306
                  ori         a6, s7, -573
                  c.andi      a3, -1
                  c.sub       a3, a5
                  lui         t4, 430849
                  slt         s4, a3, a6
                  slti        t1, s7, 1216
                  c.srli      a3, 15
                  c.lui       a7, 25
                  sub         s7, a0, s7
                  sltu        a4, s8, a4
                  add         t3, t3, s6
                  mulhsu      s10, t6, t1
                  c.sub       a3, a3
                  slt         s9, s5, zero
                  c.nop
                  c.xor       a3, s1
                  c.add       a2, t6
                  c.addi      a3, -1
                  c.add       s1, s9
                  c.or        a4, a3
                  c.or        a3, a3
                  slti        a2, s2, 118
                  c.addi16sp  sp, 336
                  and         s8, s9, t5
                  mulhu       t2, s8, s7
                  c.srli      s1, 30
                  c.srai      a3, 8
                  c.li        s6, -1
                  c.sub       a3, a3
                  add         s6, s0, gp
                  c.li        ra, 18
                  sltiu       s4, t0, 593
                  sub         s1, s3, t2
                  sltiu       s6, t2, 782
                  mulh        a0, s2, s0
                  auipc       t0, 137153
                  andi        t4, s0, -1538
                  srai        s1, a1, 21
                  c.addi4spn  a3, sp, 720
                  c.xor       a3, a3
                  add         gp, s10, s11
                  sll         t3, t3, s9
                  c.sub       a5, a2
                  addi        t2, t4, -1274
                  mul         a1, s3, s4
                  c.lui       ra, 18
                  c.nop
                  sub         t4, s6, s1
                  and         s1, s4, t2
                  addi        tp, a2, 1677
                  andi        a6, t4, 821
                  xor         s10, a3, s11
                  c.srai      a3, 17
                  c.addi16sp  sp, 160
                  div         a7, s8, gp
                  c.lui       s4, 28
                  xor         a4, a3, s6
                  sub         s6, zero, a5
                  c.add       a7, s9
                  c.xor       a3, a0
                  sub         zero, a7, gp
                  and         s8, s2, a5
                  sltu        s6, a3, a5
                  slli        a4, a4, 29
                  c.addi      ra, 21
                  add         s9, s8, sp
                  sub         sp, s7, t4
                  srl         a4, sp, s6
                  c.mv        a6, t3
                  c.mv        ra, s6
                  rem         s2, a2, s5
                  slt         ra, s10, s0
                  mulhsu      gp, t0, t5
                  srl         t4, s9, a0
                  c.addi4spn  a3, sp, 896
                  nop
                  srli        s4, a1, 3
                  add         s10, s6, s6
                  c.slli      ra, 16
                  slt         t3, s1, t2
                  div         s1, sp, s3
                  c.or        a2, s0
                  and         s1, a1, t0
                  auipc       t4, 1017855
                  c.srli      a5, 1
                  c.li        a2, -1
                  slt         t0, t6, a6
                  xori        zero, s6, -1508
                  c.lui       a4, 23
                  slt         t1, a6, a3
                  c.slli      s6, 1
                  slt         s2, sp, t0
                  mulhsu      tp, s10, a3
                  slt         t3, s1, t6
                  add         t0, t6, t4
                  rem         zero, t5, sp
                  ori         a6, s4, 1879
                  slli        zero, t0, 3
                  rem         t1, s6, a5
                  c.addi      t3, -1
                  sra         s3, a3, a0
                  mulhu       t2, s1, a2
                  slli        zero, s11, 17
                  srai        t4, t5, 26
                  or          a7, a5, s3
                  slt         a4, ra, t4
                  div         s4, t0, t5
                  mulhu       t4, s7, t5
                  srl         s4, t4, t2
                  or          t0, s0, zero
                  and         a3, s8, sp
                  mulh        tp, s5, s0
                  c.nop
                  lui         a3, 208781
                  rem         t4, t1, s6
                  xor         zero, t0, ra
                  srli        s3, s0, 31
                  c.li        a3, 6
                  ori         sp, t2, -699
                  mulhsu      s0, s8, s9
                  sll         a1, a5, a2
                  sll         ra, t5, s2
                  add         a1, t5, s5
                  c.lui       ra, 13
                  andi        a7, tp, -1056
                  c.srli      a3, 28
                  div         tp, t3, zero
                  sltiu       t4, t6, -916
                  c.or        a3, a3
                  mul         s10, s1, s4
                  div         s9, a3, a7
                  slt         ra, t6, a1
                  mul         a3, s9, sp
                  c.sub       a0, a3
                  c.nop
                  c.or        a1, a1
                  c.nop
                  c.nop
                  c.and       a1, a3
                  srl         t0, t3, s6
                  mulhu       s6, a1, s11
                  slt         a7, a7, t3
                  sltiu       s5, s3, 1235
                  c.mv        a4, tp
                  mul         t2, zero, t5
                  sltiu       gp, t5, -338
                  c.or        a3, a3
                  sltiu       a0, s11, 1172
                  c.li        a6, -1
                  c.or        a3, a3
                  slt         t2, s7, a6
                  div         t1, s3, s7
                  c.lui       s2, 6
                  c.sub       a3, a3
                  c.xor       a3, a3
                  c.sub       a3, s0
                  srli        a1, s10, 31
                  sra         t0, tp, t3
                  nop
                  xori        zero, zero, 1809
                  c.mv        gp, s6
                  srl         s8, zero, t1
                  srl         zero, zero, a6
                  slt         zero, s5, s4
                  and         s8, t1, t6
                  c.srai      a3, 12
                  c.sub       a1, a3
                  mulhsu      tp, sp, a7
                  lui         s6, 199087
                  sra         t4, a6, a7
                  c.srli      a3, 9
                  xor         t0, a5, s9
                  mul         a4, t6, gp
                  mulhsu      s8, sp, t3
                  sltiu       t3, s11, 1279
                  slti        s9, tp, 1446
                  mulhsu      s4, gp, s3
                  c.nop
                  c.and       a4, a3
                  c.sub       a3, a3
                  sub         a2, s5, tp
                  c.andi      a3, -1
                  sll         s9, a4, s11
                  c.srli      a3, 27
                  slli        a2, s0, 19
                  slt         zero, t2, s4
                  sll         zero, s1, s8
                  c.andi      a3, 24
                  addi        s2, a0, -673
                  c.addi      s9, -1
                  c.mv        sp, t4
                  c.slli      t3, 5
                  c.or        a4, a1
                  c.addi      ra, -1
                  c.srli      a3, 28
                  div         s7, a6, t5
                  c.andi      a3, 8
                  c.li        ra, 7
                  xori        ra, a4, 1849
                  addi        tp, a6, 795
                  or          zero, a7, s6
                  slti        t1, sp, -1784
                  c.nop
                  and         t3, a7, s9
                  or          s5, a3, t2
                  or          zero, a4, t5
                  c.srai      a3, 2
                  c.li        a7, -1
                  andi        zero, s9, 1181
                  c.nop
                  lui         s3, 572529
                  c.addi16sp  sp, 416
                  slt         zero, t3, s8
                  srl         zero, s4, t0
                  slti        a6, a0, 1208
                  nop
                  and         a2, s7, t1
                  sll         s10, s1, t1
                  c.srai      a3, 24
                  lui         s9, 633796
                  c.sub       a3, a3
                  lui         zero, 640299
                  auipc       s6, 648201
                  mul         s2, t2, s2
                  xori        zero, s11, -1436
                  slti        a2, s4, -456
                  c.lui       ra, 25
                  c.srai      a3, 26
                  mulhu       a3, s2, a4
                  c.addi      t1, 27
                  c.or        a3, a3
                  c.and       a3, a3
                  nop
                  c.andi      a3, -1
                  sub         ra, a5, zero
                  c.srli      a3, 22
                  srl         t1, s10, s2
                  srai        sp, t2, 14
                  c.addi      a2, -1
                  mulh        zero, t0, zero
                  c.addi      s0, 14
                  ori         s4, t4, 1075
                  c.nop
                  xor         zero, s1, s6
                  c.add       t0, s3
                  c.addi      a3, 17
                  c.andi      a1, -1
                  slt         a3, s8, t6
                  c.nop
                  or          s6, a7, s5
                  c.li        a1, 4
                  sll         s7, sp, a7
                  mul         s5, a6, a7
                  c.mv        a4, a6
                  c.li        a3, 14
                  xori        s5, a2, -1110
                  mulhu       zero, ra, t5
                  c.xor       a3, a3
                  c.li        s10, -1
                  c.xor       a3, a3
                  divu        s10, s2, t5
                  slt         s0, ra, sp
                  c.addi      a0, 14
                  c.addi      t0, 31
                  andi        a5, s10, -1450
                  sub         s7, sp, a6
                  lui         s3, 532834
                  c.lui       s0, 16
                  slti        gp, s10, -1118
                  c.andi      a3, 16
                  ori         s6, s1, -1370
                  divu        zero, gp, s7
                  sll         s1, a0, t4
                  c.xor       a3, a4
                  c.nop
                  sra         t2, s7, a3
                  c.li        t2, -1
                  c.andi      a3, -1
                  slli        s8, a1, 25
                  xori        zero, zero, 1081
                  rem         t2, tp, a2
                  or          s8, s6, t6
                  c.mv        a5, s0
                  c.nop
                  slt         tp, a6, t3
                  c.li        ra, 15
                  c.nop
                  srai        a5, s4, 1
                  sra         gp, t4, s9
                  sll         ra, zero, s0
                  mul         t3, s8, s11
                  c.slli      a4, 10
                  andi        a4, ra, 645
                  c.slli      ra, 19
                  add         s9, s8, a4
                  andi        t4, s7, -143
                  sra         sp, a0, s7
                  mulhsu      a4, t0, s11
                  c.srli      a3, 21
                  mul         s7, t0, tp
                  sll         s9, a5, a7
                  sra         a7, a4, s10
                  add         t2, t1, a3
                  c.slli      ra, 17
                  c.lui       s6, 4
                  c.addi      tp, 2
                  sra         zero, t6, t6
                  sra         zero, t3, sp
                  c.srli      a3, 27
                  c.slli      sp, 23
                  ori         a0, t1, -1587
                  div         ra, t2, s4
                  c.srli      a3, 30
                  sltiu       s0, s10, -229
                  and         t1, s5, s10
                  mul         s2, s2, s0
                  c.li        s1, -1
                  auipc       s5, 6274
                  srl         a7, t0, s6
                  c.or        a3, a3
                  c.add       t0, a2
                  c.li        s3, -1
                  c.add       a4, s7
                  c.sub       a2, a4
                  mul         t0, s9, a1
                  rem         zero, s2, a3
                  or          zero, s2, s3
                  divu        gp, s9, s7
                  nop
                  auipc       s0, 457691
                  c.mv        t2, t1
                  xori        t0, a1, -1520
                  c.mv        ra, t1
                  c.nop
                  sltu        zero, a6, gp
                  divu        tp, t4, a2
                  srli        a1, s1, 18
                  c.srli      a4, 4
                  and         s3, t0, zero
                  auipc       t3, 160824
                  mul         gp, s4, t6
                  mulhu       a4, s8, s4
                  slli        s0, s1, 29
                  srai        a5, s1, 17
                  mulhu       s2, s9, a0
                  slt         s5, gp, gp
                  c.and       a5, s0
                  nop
                  slt         a1, s6, a5
                  c.lui       ra, 15
                  and         s4, a0, a6
                  sub         ra, s4, tp
                  andi        s4, t3, 1782
                  c.srli      s1, 1
                  and         zero, a1, t4
                  addi        t1, gp, 662
                  c.srli      a2, 28
                  andi        a3, t2, -321
                  ori         a4, t1, -1385
                  mul         a5, a6, s5
                  c.addi4spn  a3, sp, 96
                  slti        s7, sp, 1761
                  andi        zero, s9, -828
                  c.addi16sp  sp, -16
                  mulhu       s7, zero, s8
                  sub         t1, a5, s9
                  mulh        s8, s6, s10
                  sub         s5, s6, s0
                  mulh        s4, a3, sp
                  slt         a5, t1, tp
                  slli        t0, s5, 0
                  xori        zero, s7, 867
                  nop
                  or          a2, t1, t5
                  mulh        s3, a3, tp
                  divu        gp, s10, s0
                  c.addi      s6, 1
                  slti        s2, s9, -706
                  mul         s8, t6, t0
                  c.srli      a3, 10
                  c.or        a3, a0
                  lui         gp, 557380
                  mulh        ra, s2, s11
                  c.and       a2, a3
                  srli        zero, s10, 22
                  nop
                  mulhsu      a6, t0, t1
                  c.andi      a3, 2
                  c.add       t0, s4
                  c.sub       a3, a3
                  c.slli      t4, 1
                  c.xor       a3, a3
                  srl         s9, s7, a1
                  and         a0, a4, s1
                  c.srai      a3, 5
                  add         s2, s10, a7
                  xor         s9, s0, sp
                  mulhsu      ra, s3, s0
                  c.sub       a3, a3
                  c.xor       a3, a3
                  slli        a4, s11, 18
                  c.srai      a3, 27
                  xor         t0, a3, s8
                  slti        a7, t4, 2037
                  c.addi16sp  sp, 352
                  rem         a7, s5, a7
                  andi        s10, sp, 4
                  c.addi4spn  a5, sp, 480
                  divu        sp, a0, t4
                  sra         gp, s4, t4
                  div         s2, s9, s0
                  c.xor       a3, a2
                  c.slli      t0, 28
                  srli        tp, t3, 27
                  mulhsu      sp, a2, s1
                  mulh        gp, a2, tp
                  lui         t3, 415622
                  c.mv        a7, a0
                  slti        sp, s6, -821
                  c.li        a1, 14
                  c.slli      a5, 27
                  c.add       a0, t2
                  c.addi      tp, -1
                  c.addi4spn  a3, sp, 832
                  c.addi      s1, -1
                  sltu        t0, a5, a6
                  c.srli      a3, 12
                  or          t2, a1, s6
                  xori        t1, t2, 550
                  c.and       a3, a3
                  andi        s1, s4, -587
                  slti        t2, a5, -826
                  mulhsu      tp, s1, a3
                  ori         zero, a3, -1886
                  c.srai      a3, 13
                  c.lui       a6, 24
                  c.srai      a3, 29
                  lui         a7, 192845
                  c.mv        t2, t0
                  c.lui       tp, 19
                  srl         s0, s3, a7
                  mulh        t3, t2, t6
                  c.andi      s0, 8
                  and         t1, a7, a6
                  srli        a5, a5, 1
                  c.nop
                  c.xor       a3, a3
                  c.srli      a3, 4
                  c.srai      a3, 21
                  divu        zero, a0, sp
                  mulh        tp, t6, s3
                  c.srai      a1, 13
                  slt         s10, a5, zero
                  srli        a4, a1, 9
                  c.andi      a0, -1
                  xori        t1, s4, -987
                  slt         s8, t4, s10
                  c.addi16sp  sp, 288
                  mul         a6, gp, tp
                  c.nop
                  c.lui       ra, 10
                  xor         s6, zero, s4
                  mul         t3, a1, s2
                  srl         zero, a7, a0
                  xori        s4, s7, 1891
                  add         s0, t5, sp
                  add         s9, s1, s4
                  xor         s2, s0, s9
                  sll         ra, a1, t0
                  mul         a7, t6, a3
                  andi        zero, s1, -1396
                  c.mv        s0, s8
                  c.addi      s9, 17
                  and         zero, gp, t0
                  srl         t0, s11, tp
                  slti        a2, a2, 1193
                  divu        s10, gp, a1
                  or          s1, s5, s6
                  srl         s8, s11, s3
                  addi        s3, s0, -1322
                  add         zero, s3, zero
                  slti        s8, ra, -1422
                  nop
                  slti        s1, ra, 1077
                  mulh        s7, s4, a7
                  mulhsu      a4, s4, a2
                  c.xor       a0, a3
                  c.srli      a3, 10
                  xori        s1, s8, 82
                  c.lui       a5, 17
                  c.addi16sp  sp, 80
                  c.addi4spn  a3, sp, 816
                  ori         s6, t2, 243
                  sub         a6, s11, a4
                  slt         s9, a3, s10
                  c.lui       s2, 2
                  c.addi4spn  a3, sp, 352
                  sll         a3, a4, t0
                  sltiu       s3, tp, 1863
                  divu        s6, a7, s0
                  c.and       a3, a3
                  ori         t1, s1, 1835
                  sltiu       s8, s1, 1335
                  c.or        a3, a2
                  c.sub       a3, a3
                  c.or        s0, a3
                  mul         s1, zero, zero
                  slt         a1, a6, a6
                  c.add       s6, gp
                  sra         s3, a1, s10
                  nop
                  c.slli      a6, 10
                  addi        s4, gp, -1572
                  or          zero, a6, ra
                  andi        a3, s5, 60
                  srai        s6, a0, 0
                  div         s0, tp, a3
                  lui         zero, 697403
                  c.addi      s4, -1
                  and         tp, gp, s1
                  srli        ra, a5, 0
                  addi        s0, s3, 1597
                  xori        s1, s3, 1541
                  c.srai      a3, 27
                  lui         tp, 683285
                  c.sub       a3, a3
                  mulh        s6, t4, ra
                  slti        ra, s0, -1003
                  c.mv        s8, s1
                  c.addi4spn  s0, sp, 384
                  sll         zero, s0, s3
                  add         s0, t0, s2
                  divu        a1, t6, t5
                  divu        a4, s1, s5
                  c.andi      a3, -1
                  srai        sp, zero, 9
                  ori         a2, a1, 1984
                  c.li        tp, 28
                  c.xor       a4, a3
                  srli        a2, a7, 1
                  and         a0, s4, a0
                  c.addi4spn  a3, sp, 640
                  srli        ra, tp, 20
                  div         sp, s7, s11
                  c.nop
                  c.nop
                  mul         s6, s5, s0
                  c.or        a3, a3
                  rem         s2, s11, a3
                  or          a5, s9, t6
                  srli        s7, a4, 21
                  c.sub       a3, a3
                  divu        s4, t5, s0
                  div         s3, gp, s10
                  andi        a2, s0, 891
                  mulhsu      a4, s7, s11
                  divu        s3, a1, a6
                  c.li        s6, 6
                  c.lui       a7, 31
                  and         s8, s2, s8
                  or          t4, a4, s6
                  c.addi      t0, 6
                  and         s7, s9, s3
                  c.add       a5, a3
                  andi        a0, s5, -1582
                  sra         s7, s3, s9
                  and         s2, s0, s10
                  or          a4, a1, s2
                  sltiu       zero, s10, 728
                  sltu        s2, s1, a0
                  or          s3, zero, s8
                  c.li        a6, 9
                  div         t0, s10, t2
                  slti        t4, a4, 422
                  c.and       a3, a4
                  div         ra, s0, t2
                  c.slli      s8, 9
                  c.and       a3, a3
                  srl         s5, s0, a4
                  divu        gp, sp, s5
                  rem         s1, a6, a1
                  slt         t0, zero, s11
                  c.add       s5, s3
                  c.andi      a3, -1
                  slt         s6, zero, a0
                  ori         s4, s0, -492
                  andi        a3, t3, 704
                  ori         t1, s6, -768
                  srai        s5, s2, 4
                  c.lui       s4, 20
                  nop
                  andi        sp, a4, 1659
                  slti        zero, s6, -1136
                  sll         tp, a3, s1
                  c.mv        s4, ra
                  sra         tp, sp, a5
                  mulh        s1, zero, sp
                  c.addi4spn  a3, sp, 448
                  c.add       gp, a7
                  slti        zero, t1, -1151
                  addi        zero, a5, 785
                  andi        a0, s4, 1445
                  c.mv        a4, ra
                  and         s0, a1, s7
                  c.nop
                  auipc       zero, 599646
                  c.srai      a3, 17
                  sltu        sp, s1, a1
                  c.andi      a3, 0
                  mulhsu      s9, a3, t1
                  add         a7, a7, s6
                  slt         t1, s6, s0
                  sltiu       a6, s3, 885
                  slli        a7, s0, 24
                  lui         s10, 723615
                  c.add       ra, a5
                  andi        zero, a7, -400
                  or          a2, s2, t6
                  c.mv        a7, t3
                  c.addi4spn  a3, sp, 896
                  sll         s0, ra, s11
                  or          t2, s1, a3
                  sll         a7, s8, t0
                  c.srai      a0, 3
                  div         s1, s9, a4
                  andi        a6, s1, -1753
                  slti        s1, a6, 1825
                  c.addi      a7, 10
                  c.srai      a3, 4
                  c.lui       s6, 1
                  xor         s2, a6, a2
                  addi        s0, s2, 1918
                  c.and       a3, a3
                  div         s2, ra, s9
                  lui         s5, 1004267
                  sll         a5, t3, t0
                  divu        a0, s10, t6
                  c.lui       s10, 1
                  add         a2, s8, t6
                  li         t4, 0x1 #start riscv_int_numeric_corner_stream_14
                  li         t3, 0x5e857ea4
                  li         s10, 0x0
                  li         a4, 0x0
                  li         t1, 0x0
                  li         s8, 0x1
                  li         s9, 0x0
                  li         a6, 0x0
                  li         s1, 0x0
                  li         sp, 0x0
                  c.mv        s4, s7
                  c.add       s1, t2
                  div         s4, s10, t0
                  add         a0, s9, s10
                  mulhsu      a5, a2, a2
                  mulh        s9, s7, s6
                  c.li        tp, -1
                  mulhsu      a5, a3, t4
                  divu        t3, a4, s7
                  mulhu       s8, sp, s7
                  addi        a4, s5, 558
                  div         t1, a7, s9
                  divu        s8, a7, s11
                  mul         t2, tp, tp
                  mul         a3, s2, t4
                  c.li        t3, 28
                  c.li        s7, 13
                  c.addi      ra, 27
                  rem         a4, sp, s11
                  mul         a3, a0, s4
                  mulhsu      s5, a1, s4
                  mul         s9, s5, s4
                  sub         s6, t6, t6
                  c.lui       t0, 7
                  mulh        ra, a7, t5
                  mulh        s3, sp, a6
                  auipc       s4, 672587 #end riscv_int_numeric_corner_stream_14
                  add         a5, ra, a3
                  add         t0, s5, s11
                  slti        s9, t1, -544
                  c.addi4spn  a3, sp, 896
                  divu        t3, s2, tp
                  c.addi      s1, 19
                  srai        s10, sp, 13
                  c.nop
                  c.slli      sp, 25
                  c.and       s1, a2
                  c.sub       s1, a3
                  auipc       a5, 916175
                  c.add       tp, t6
                  c.and       a3, a3
                  c.andi      a2, -1
                  rem         a2, s5, t5
                  c.addi      s10, -1
                  c.lui       t3, 30
                  c.addi16sp  sp, -16
                  c.or        a5, a3
                  slt         s5, s11, sp
                  xor         zero, s11, s1
                  c.addi4spn  s0, sp, 448
                  xori        zero, sp, 618
                  c.addi      s5, -1
                  xori        a6, s1, -1452
                  c.li        ra, -1
                  mulh        a4, t4, s0
                  andi        tp, t2, -256
                  mulhu       a0, t4, s4
                  c.mv        ra, ra
                  c.and       a3, a3
                  c.addi      s0, -1
                  div         t1, s7, gp
                  lui         t2, 975987
                  sub         s6, s8, t6
                  xori        a5, t6, -1389
                  c.xor       a3, s0
                  add         zero, s3, gp
                  addi        t2, t3, 1730
                  c.srai      a3, 25
                  c.add       s9, a5
                  c.nop
                  c.xor       a3, a3
                  div         zero, a5, gp
                  srai        a3, sp, 10
                  xor         zero, a7, t0
                  auipc       gp, 611322
                  c.addi16sp  sp, -16
                  c.and       s1, a3
                  ori         s6, t5, 1200
                  ori         tp, s2, 1566
                  c.nop
                  srl         t0, s6, zero
                  nop
                  c.mv        s6, t2
                  sltiu       a4, a7, -389
                  or          zero, a0, tp
                  rem         s1, sp, t6
                  c.nop
                  c.li        a7, -1
                  addi        a1, sp, 38
                  rem         zero, s11, a6
                  and         s7, t5, s9
                  xori        s5, s3, -2005
                  slt         a3, s8, zero
                  c.or        a3, a3
                  li         t4, 0x333ba6c6 #start riscv_int_numeric_corner_stream_13
                  li         s1, 0x0
                  li         t3, 0x0
                  li         s8, 0x0
                  li         s9, 0x0
                  li         tp, 0x1
                  li         a2, 0x0
                  li         s0, 0x1268a77c
                  li         a0, 0x0
                  li         s10, 0x0
                  divu        a1, ra, s8
                  c.nop
                  divu        a6, s4, s2
                  c.nop
                  c.addi4spn  a0, sp, 672
                  mul         sp, a7, s5
                  add         a0, s7, a3
                  nop
                  c.mv        a2, a2
                  c.mv        t0, a7
                  divu        zero, a7, s0
                  addi        ra, a6, 1093
                  mulhu       a0, a2, gp
                  auipc       t0, 44014
                  c.addi4spn  s0, sp, 960
                  c.addi4spn  a3, sp, 784
                  mulh        sp, s2, s9
                  c.nop
                  c.addi4spn  a3, sp, 144
                  addi        s3, t3, -1139
                  sub         t4, a0, s1
                  c.addi4spn  a3, sp, 448
                  c.nop
                  addi        a5, t2, 1811 #end riscv_int_numeric_corner_stream_13
                  mulhu       t0, sp, s2
                  c.li        t2, 22
                  mulhsu      s1, t5, a7
                  slt         t3, s2, s1
                  nop
                  and         a2, s10, sp
                  c.sub       s0, a3
                  c.addi16sp  sp, 336
                  slti        s2, s0, -1311
                  c.or        a3, a3
                  addi        s0, s0, -1589
                  mulh        s0, ra, a4
                  mulhu       a1, a2, a3
                  sub         s4, s4, s7
                  srl         s6, s11, t4
                  srai        s6, gp, 17
                  c.sub       a3, a3
                  xor         s0, a3, a7
                  c.and       a3, a1
                  slti        a1, t2, -1824
                  slli        s9, s5, 23
                  srli        t2, s1, 5
                  c.or        a3, a3
                  srai        s5, a6, 1
                  c.mv        a7, a6
                  auipc       t3, 182086
                  c.xor       a5, s1
                  srli        a2, t1, 2
                  lui         t4, 788211
                  divu        a0, a4, a7
                  ori         t3, a4, 314
                  slt         s10, s9, a4
                  auipc       s10, 512354
                  c.slli      a6, 19
                  sra         zero, s7, s9
                  mulh        s4, s9, a5
                  sra         zero, s0, gp
                  and         s6, s0, a1
                  add         a2, t0, t2
                  ori         sp, a0, -55
                  mulhu       t0, a0, a4
                  srl         a3, gp, zero
                  sub         t0, t2, tp
                  c.sub       a3, a3
                  c.add       sp, sp
                  c.mv        a5, t6
                  and         zero, gp, t0
                  c.slli      s5, 26
                  srl         s7, s11, a7
                  andi        a0, t4, -1632
                  c.andi      a3, -1
                  rem         s8, t3, s0
                  xor         tp, sp, s7
                  c.lui       a5, 9
                  c.and       a3, a3
                  mulhu       zero, s9, s9
                  srai        s1, t4, 17
                  xori        ra, a2, -1211
                  c.or        a5, a1
                  srli        zero, t2, 11
                  slti        s1, s6, -752
                  sltiu       s9, s11, 1710
                  sll         t3, s6, zero
                  rem         s3, a6, t1
                  c.add       a1, s4
                  xor         s7, t6, s11
                  srl         s6, a6, t3
                  sra         s6, a2, t6
                  c.sub       a3, s0
                  c.li        s0, -1
                  xor         s1, s10, t3
                  c.mv        gp, s7
                  mulh        s1, tp, t3
                  slt         a7, s3, t4
                  c.xor       a3, a3
                  sltu        t1, s7, a1
                  sub         s1, tp, s11
                  srai        s1, s11, 4
                  c.add       s6, t1
                  divu        t4, s2, s3
                  slti        s3, t3, -1648
                  sltu        t1, a1, t2
                  sra         t1, tp, sp
                  c.xor       a0, a4
                  andi        s3, s5, 847
                  rem         s4, s10, ra
                  c.srli      a3, 9
                  auipc       a6, 164518
                  c.xor       a5, a3
                  c.srli      a3, 6
                  slt         s9, t4, s0
                  slti        s6, a2, 1884
                  c.add       s7, a6
                  c.li        t2, -1
                  sra         a4, tp, s5
                  sub         tp, s10, gp
                  slt         a3, s8, t2
                  sll         s0, s5, s7
                  srl         s8, a1, s8
                  addi        a4, s9, -1969
                  and         a3, tp, t3
                  mul         tp, t6, a2
                  or          a0, s6, a7
                  lui         t4, 1000109
                  sltiu       zero, t2, -1851
                  c.sub       a3, a3
                  andi        s6, s10, -1349
                  rem         s1, s6, s6
                  c.addi      ra, -1
                  nop
                  c.sub       a3, a0
                  srli        t4, a0, 10
                  c.addi      a3, 31
                  sra         zero, s3, ra
                  mulhu       s7, a4, a2
                  lui         zero, 732513
                  c.addi      gp, -1
                  c.mv        ra, s5
                  addi        zero, a4, 1023
                  nop
                  c.mv        t2, s10
                  andi        s9, tp, -954
                  sltiu       s4, t3, -1341
                  ori         t4, t6, 182
                  srli        tp, a4, 15
                  sll         tp, sp, sp
                  c.add       a1, sp
                  xor         s0, tp, a6
                  xor         zero, a6, s0
                  c.nop
                  and         s10, s6, t5
                  sltu        a2, a0, s2
                  ori         s4, tp, -1404
                  and         s6, s2, s10
                  div         a3, a4, s9
                  div         t3, s4, s3
                  c.mv        s8, a0
                  rem         ra, s3, ra
                  sll         tp, s0, a4
                  mulhsu      s9, a5, s2
                  srl         a3, gp, s8
                  c.slli      s8, 6
                  c.slli      a3, 7
                  slli        ra, sp, 23
                  rem         t4, t4, gp
                  c.nop
                  mulh        a1, t4, sp
                  add         s3, s0, s6
                  c.add       s0, a2
                  divu        zero, a5, t4
                  c.slli      a4, 23
                  mulh        ra, tp, a0
                  sltiu       s4, t0, 495
                  and         a1, s8, t1
                  slt         tp, a4, s3
                  c.andi      a3, 10
                  c.srai      a3, 31
                  c.xor       a3, a3
                  lui         a4, 610281
                  c.and       a3, a3
                  c.sub       a3, a3
                  srl         a7, s9, a2
                  slti        a5, t1, -1970
                  c.srli      a3, 4
                  c.sub       s0, a3
                  nop
                  divu        t0, s7, t5
                  c.nop
                  sltu        gp, zero, a5
                  slt         s5, s11, t3
                  slli        zero, a1, 5
                  mulhsu      t2, s4, t5
                  c.xor       a3, a3
                  c.or        a3, a1
                  slli        s3, t2, 10
                  and         zero, t0, s4
                  c.li        s3, -1
                  xori        a6, a3, 1251
                  c.li        gp, -1
                  mulhsu      a3, a0, s5
                  c.mv        t0, sp
                  c.addi16sp  sp, 400
                  c.lui       t1, 8
                  rem         s6, a2, s0
                  c.srai      a3, 18
                  ori         a2, a6, -1379
                  c.li        s4, -1
                  xori        zero, a1, -1032
                  c.add       t1, s11
                  auipc       t1, 583107
                  c.slli      ra, 4
                  c.andi      s0, 15
                  c.sub       a3, a3
                  ori         t2, sp, -821
                  c.addi      a5, -1
                  xor         s2, t5, s3
                  c.addi      s2, 5
                  c.and       a0, a3
                  srli        zero, s7, 30
                  c.slli      ra, 30
                  nop
                  div         ra, ra, s4
                  sub         a2, s9, a2
                  c.add       a1, a7
                  sra         s10, s0, t4
                  c.add       s9, s8
                  c.addi4spn  a3, sp, 832
                  add         ra, a1, s5
                  c.nop
                  nop
                  add         s9, gp, t3
                  sra         a5, t6, t5
                  or          s10, ra, s11
                  ori         t1, gp, 932
                  c.nop
                  c.srli      a3, 7
                  srli        t2, s2, 23
                  lui         t0, 261191
                  c.mv        a7, s1
                  c.xor       a3, a0
                  slli        s1, s4, 6
                  c.sub       a3, a3
                  lui         zero, 55359
                  mulh        gp, t3, a7
                  c.addi16sp  sp, 464
                  c.or        a5, a2
                  mul         a3, sp, zero
                  add         t0, s1, s1
                  c.addi      a7, -1
                  mulhsu      a0, s9, s7
                  addi        t2, s1, 1623
                  divu        t4, t6, t0
                  mulh        s2, gp, s3
                  sll         tp, s11, gp
                  srli        s0, s11, 13
                  rem         a2, gp, s2
                  srai        s7, a3, 6
                  rem         s6, t4, s7
                  c.addi16sp  sp, 416
                  mul         zero, zero, t1
                  div         a4, t1, s2
                  ori         s7, tp, 1235
                  slti        s2, s7, -1157
                  xor         s1, sp, tp
                  xor         a3, a1, s0
                  nop
                  mulhsu      zero, s6, s1
                  srai        a5, s8, 3
                  c.lui       s4, 20
                  c.addi      t1, -1
                  c.addi      t0, 24
                  mulhu       sp, s6, s7
                  c.xor       a3, a3
                  mulh        zero, t2, t2
                  srl         a4, t5, s10
                  c.addi      t2, -1
                  mulhsu      s8, a3, s9
                  lui         tp, 633713
                  or          s0, a1, s0
                  ori         s7, a2, 1083
                  slt         gp, t3, zero
                  add         t1, a0, t2
                  sra         s3, a1, gp
                  srli        s8, a2, 10
                  divu        s7, gp, sp
                  c.xor       a3, a0
                  c.mv        ra, gp
                  lui         s4, 148853
                  lui         s4, 16437
                  slti        s3, ra, 1753
                  c.addi      s3, 11
                  srl         s1, s2, s5
                  nop
                  sub         a0, a5, s6
                  c.andi      a3, -1
                  c.slli      a4, 14
                  and         a3, s2, s6
                  srl         a2, t4, s10
                  slti        tp, s4, -1484
                  or          t4, zero, tp
                  slli        s0, a4, 12
                  and         zero, a3, a2
                  c.addi16sp  sp, 288
                  srli        a6, t3, 8
                  c.mv        ra, gp
                  or          t0, s11, a0
                  c.srai      a3, 8
                  xori        s4, a7, -1848
                  xori        t0, zero, 1152
                  sltu        sp, s5, t0
                  or          zero, a4, s1
                  slli        a0, a3, 16
                  ori         a5, zero, -1978
                  c.and       a3, a3
                  c.and       a5, a3
                  c.add       t4, s7
                  c.and       a3, a3
                  c.xor       a3, a3
                  srai        t4, gp, 24
                  ori         a0, s5, -1011
                  srai        s2, s1, 26
                  sltiu       zero, s7, -1136
                  c.xor       a3, a3
                  c.and       a3, a2
                  div         a4, t1, s11
                  divu        sp, s2, gp
                  c.addi16sp  sp, -16
                  srl         s5, s10, t4
                  c.slli      t2, 1
                  slt         s2, t6, t3
                  c.srli      a3, 22
                  sub         tp, s7, a4
                  sltiu       tp, t1, 1488
                  sub         t3, t2, t6
                  c.andi      a0, 8
                  c.srai      a3, 30
                  c.or        s1, a3
                  slti        a0, s6, 1041
                  xori        tp, a0, -455
                  div         s1, s5, tp
                  c.lui       s1, 3
                  addi        s3, t2, -461
                  c.addi16sp  sp, 416
                  div         s10, s0, s3
                  c.addi      t1, 28
                  auipc       t1, 624303
                  ori         gp, a0, 1884
                  mulhu       s1, a6, t2
                  mulhu       gp, t6, a4
                  c.srli      a3, 23
                  divu        t2, s11, a1
                  add         a5, a1, s2
                  sub         s10, t5, s1
                  and         a2, a6, t3
                  c.srli      a3, 7
                  divu        s1, a0, s1
                  c.add       gp, t5
                  xori        s10, s4, 1429
                  c.addi      s10, -1
                  c.nop
                  c.mv        s6, s8
                  c.srli      a1, 10
                  xori        t2, s2, 2024
                  c.addi16sp  sp, -16
                  c.or        a3, a3
                  c.addi      s3, 10
                  c.or        a3, a3
                  or          s9, sp, sp
                  sltiu       s7, a7, 1443
                  slt         t3, a1, s9
                  c.addi16sp  sp, 48
                  xori        gp, a4, 1068
                  or          a7, s2, s2
                  c.xor       a2, a3
                  sltu        zero, t6, gp
                  divu        t2, s2, s6
                  ori         s4, s1, 1616
                  addi        s10, s2, 1055
                  c.srai      a3, 19
                  c.xor       a3, a3
                  mul         t3, t5, ra
                  mulhsu      zero, s1, a1
                  srai        a2, s0, 2
                  rem         a0, s11, s8
                  slli        a2, a7, 29
                  c.srli      a3, 19
                  rem         a2, s11, a2
                  slt         s3, s4, s1
                  c.lui       ra, 15
                  c.and       a0, a3
                  c.and       a3, a3
                  c.lui       s7, 21
                  mulh        s6, s4, s7
                  auipc       tp, 108135
                  srli        s8, gp, 25
                  srl         s5, a7, sp
                  div         a2, t2, a2
                  c.addi16sp  sp, -16
                  c.andi      a0, -1
                  c.nop
                  div         a3, s3, t5
                  sll         a2, s9, s3
                  sll         a5, s11, s2
                  div         t4, s1, t4
                  rem         a5, s11, a0
                  mul         s1, s3, a4
                  c.andi      a3, 9
                  sll         gp, t1, t1
                  divu        s0, t2, s2
                  srai        a1, ra, 9
                  srai        ra, s3, 29
                  sltu        s6, s4, s2
                  sra         s0, s6, a5
                  div         a2, a1, s4
                  and         sp, s11, s6
                  auipc       sp, 156961
                  c.addi4spn  a3, sp, 832
                  c.and       a3, a3
                  c.lui       ra, 11
                  c.addi16sp  sp, -16
                  c.srli      a3, 29
                  sll         gp, s8, s2
                  c.andi      a3, 0
                  c.slli      t2, 8
                  andi        zero, sp, 1821
                  mulhsu      s4, s1, t3
                  ori         s6, tp, -24
                  divu        t3, s0, sp
                  andi        a6, s6, -964
                  sltiu       s8, t2, -1576
                  sltu        zero, s10, t6
                  nop
                  sll         s4, t2, t5
                  c.xor       a5, a0
                  sra         t1, a1, t1
                  slti        s9, s8, -1811
                  mulh        t1, a0, s6
                  c.andi      s1, -1
                  slti        s7, s7, -1138
                  xori        t2, s11, 1969
                  c.mv        ra, a0
                  lui         t1, 335024
                  sltu        a5, s6, zero
                  c.addi      s6, -1
                  or          zero, t2, s10
                  c.li        a6, -1
                  srl         a0, a7, s9
                  sll         zero, s5, s4
                  c.andi      a3, -1
                  c.srai      a3, 5
                  mulhsu      a1, a2, tp
                  slti        s6, s7, -1534
                  addi        a6, zero, -1107
                  c.xor       a3, a3
                  sltu        s4, sp, gp
                  c.srai      a3, 29
                  sltiu       zero, t6, 504
                  rem         zero, t3, t1
                  slli        zero, a3, 5
                  andi        a5, s7, 1798
                  c.addi16sp  sp, 384
                  c.srai      a3, 29
                  ori         sp, t2, 988
                  divu        a6, a0, s1
                  c.mv        s10, s0
                  c.srai      a3, 31
                  c.and       a3, a3
                  c.sub       a3, a3
                  c.lui       ra, 27
                  sra         zero, a2, a1
                  sll         zero, a7, s0
                  c.addi      s6, -1
                  sltiu       s6, a0, 1706
                  sltu        t1, s6, zero
                  srai        t3, t0, 12
                  add         s6, a2, s2
                  ori         a5, a3, -1891
                  slt         a1, s10, zero
                  c.addi      gp, -1
                  xori        t1, s7, -1944
                  c.sub       a3, a3
                  c.xor       a1, a3
                  and         a6, s11, a4
                  sra         a5, s2, s1
                  c.add       ra, ra
                  c.slli      sp, 14
                  mulhu       s5, gp, s1
                  c.addi16sp  sp, -16
                  and         ra, a5, s8
                  slti        zero, sp, -271
                  xori        s1, s1, 690
                  sll         ra, s3, s11
                  c.and       a3, a3
                  mulh        s5, a6, t3
                  c.nop
                  sltiu       t3, tp, -1046
                  c.lui       ra, 2
                  mulhu       zero, t2, a5
                  c.add       a2, sp
                  slt         zero, s1, s1
                  auipc       t3, 9875
                  sltiu       s9, a0, 256
                  rem         s8, s1, a1
                  or          s0, ra, t0
                  add         zero, s10, a5
                  divu        a5, ra, s10
                  slti        s4, sp, 1266
                  auipc       sp, 460651
                  c.srli      a3, 8
                  c.sub       a3, a3
                  rem         s3, t3, zero
                  andi        s9, t3, 1840
                  mulh        s4, t6, t0
                  srl         s8, tp, s0
                  rem         ra, s2, ra
                  andi        s5, t2, -721
                  srai        t0, a7, 26
                  div         zero, tp, ra
                  c.srai      a3, 13
                  srl         zero, t1, s2
                  c.slli      s9, 13
                  c.sub       a3, a3
                  ori         a0, a1, -1669
                  c.mv        s0, ra
                  or          a7, sp, a2
                  sll         a5, s4, s4
                  divu        s4, a5, a5
                  srli        t4, t6, 19
                  auipc       a3, 571215
                  addi        gp, s7, 37
                  auipc       gp, 1025776
                  c.addi4spn  a2, sp, 416
                  c.and       a2, a3
                  c.addi      a5, 22
                  c.slli      a0, 16
                  c.nop
                  andi        zero, t6, 1804
                  div         a1, a2, a5
                  c.addi      s1, 29
                  c.slli      ra, 10
                  and         s1, s2, t4
                  ori         s6, gp, 591
                  c.nop
                  divu        zero, s7, a5
                  c.addi16sp  sp, -16
                  auipc       a3, 259787
                  auipc       t2, 752647
                  div         s10, a2, sp
                  andi        zero, s11, -511
                  addi        a0, sp, -1720
                  c.sub       a5, a3
                  sra         tp, s7, s1
                  c.li        gp, 16
                  sra         a4, t4, gp
                  sltu        a5, t4, s4
                  sra         zero, t2, ra
                  addi        zero, a2, -1086
                  mulh        a4, sp, s7
                  mulh        a7, s0, tp
                  slli        s0, t1, 18
                  c.srai      a3, 5
                  slti        s6, s8, 1236
                  c.srai      a3, 9
                  rem         s1, s4, a4
                  addi        gp, s3, 111
                  auipc       ra, 253348
                  c.and       a3, a3
                  c.xor       a3, a3
                  mulhsu      s0, zero, s11
                  c.srai      s1, 2
                  mulhsu      s6, s10, t3
                  srai        s9, t3, 5
                  c.srai      a4, 3
                  c.addi4spn  s1, sp, 192
                  andi        t2, t3, 1569
                  slti        zero, ra, -136
                  lui         s7, 541524
                  mulh        gp, t3, t3
                  sub         sp, s7, s10
                  srl         t4, s6, s0
                  sra         a3, t1, t6
                  c.and       a3, a5
                  c.mv        ra, sp
                  slt         zero, t0, t0
                  or          t3, s3, t5
                  sltiu       zero, s10, 934
                  add         tp, a0, a7
                  c.andi      a3, 15
                  c.srai      a3, 27
                  c.and       a3, a3
                  addi        s5, t0, 712
                  ori         gp, ra, -1191
                  div         t0, s11, tp
                  xori        t3, s3, -1237
                  c.srli      a0, 8
                  andi        gp, s11, 407
                  slli        a2, t6, 23
                  mulh        zero, a4, s0
                  mulhsu      zero, s7, s1
                  c.add       a3, s2
                  c.srai      a3, 31
                  xori        ra, s9, 502
                  auipc       sp, 146770
                  c.slli      a4, 12
                  slt         a1, s6, t3
                  c.andi      a3, 29
                  div         s7, zero, s10
                  mul         zero, s3, s7
                  ori         zero, t2, -9
                  sltiu       a0, t6, 1720
                  srli        s3, t6, 18
                  c.mv        s9, t0
                  mulhsu      a4, gp, ra
                  c.andi      a5, -1
                  srli        s8, a2, 5
                  c.li        t3, 21
                  add         zero, a5, t6
                  c.addi16sp  sp, 272
                  addi        a4, t2, -268
                  c.nop
                  c.and       a3, s1
                  c.nop
                  c.xor       a0, a3
                  srli        a4, a3, 7
                  c.li        tp, -1
                  divu        a2, s4, a7
                  c.lui       t4, 15
                  c.nop
                  lui         t1, 748748
                  andi        zero, s10, -941
                  xori        a4, ra, 747
                  srai        t3, t5, 28
                  c.add       ra, s3
                  rem         zero, s0, t1
                  c.or        a3, a3
                  mulhu       t1, s3, s6
                  mulhsu      ra, a7, sp
                  div         a4, a1, s10
                  mulh        a7, s4, s8
                  slti        s0, a3, 1229
                  sll         a1, sp, t5
                  and         s1, t0, t5
                  xor         tp, s9, a4
                  c.srli      a3, 14
                  xori        a4, t2, 1672
                  ori         a7, t6, 811
                  nop
                  mul         s5, s4, t2
                  c.lui       s3, 9
                  slti        s0, t1, 367
                  c.add       ra, a6
                  srai        a6, s11, 4
                  c.nop
                  addi        gp, sp, -1360
                  c.andi      a2, -1
                  sltiu       t2, a0, -1258
                  addi        zero, gp, 1363
                  sll         t1, t2, s1
                  sub         gp, s10, s3
                  srl         s2, t4, s6
                  mulhsu      zero, sp, a5
                  c.addi4spn  a3, sp, 640
                  mulh        a1, zero, a2
                  c.nop
                  c.slli      s6, 10
                  c.or        a3, a3
                  slti        a1, t3, 47
                  c.slli      s8, 17
                  mulhu       t1, a3, ra
                  c.srli      s0, 28
                  c.mv        s1, ra
                  c.and       a3, a3
                  slti        t2, s1, 2033
                  mul         a7, s9, a6
                  c.or        a3, a3
                  addi        s7, a7, -83
                  xori        a3, t2, 890
                  c.li        ra, -1
                  slt         s6, s11, t5
                  srl         s7, s0, sp
                  srl         s6, ra, a0
                  mulh        zero, s1, a4
                  c.li        ra, -1
                  sltu        zero, tp, tp
                  sra         s3, gp, ra
                  srl         t0, s9, a4
                  xor         a7, t5, a3
                  xori        a1, s10, -955
                  mulhsu      a7, s7, zero
                  mulh        a1, s0, s9
                  mulh        a4, a1, zero
                  srli        a7, a5, 0
                  c.sub       s1, a3
                  mul         a6, s4, a7
                  c.xor       s1, a3
                  c.add       a3, ra
                  c.slli      s8, 23
                  c.sub       s1, a3
                  srl         s4, s1, ra
                  auipc       s2, 589162
                  divu        t4, sp, t6
                  mulh        s9, a5, s5
                  c.li        a2, -1
                  ori         a2, gp, 1135
                  nop
                  xori        a7, s7, -1528
                  and         ra, gp, t4
                  srai        zero, t2, 0
                  slli        s4, a5, 5
                  div         t2, gp, t0
                  div         a6, tp, s0
                  xori        tp, tp, -1850
                  andi        zero, a3, -1019
                  c.sub       a3, a3
                  srl         s6, s7, s11
                  mul         s5, t3, t0
                  rem         sp, t5, s11
                  c.and       a3, a3
                  ori         a7, gp, 688
                  andi        s7, tp, 1692
                  addi        s4, s2, -1345
                  auipc       s2, 717267
                  divu        s10, s2, a3
                  addi        s5, a4, 1105
                  c.srai      a3, 15
                  mulhu       s3, a3, ra
                  c.andi      a3, -1
                  srli        a4, a3, 23
                  srai        s3, ra, 15
                  sltu        s9, a0, a5
                  mulhsu      sp, s7, s11
                  mulh        t0, gp, sp
                  rem         a0, s8, sp
                  c.srai      a4, 28
                  ori         s0, a5, -1101
                  c.addi4spn  a0, sp, 896
                  mul         a3, s4, t0
                  andi        s3, s0, -1640
                  srai        s4, t3, 23
                  rem         s7, s1, t1
                  srl         t1, sp, s8
                  c.srli      a3, 25
                  slli        s9, s6, 17
                  c.sub       a3, a3
                  srli        zero, a4, 31
                  srl         a4, s10, s9
                  c.lui       s10, 20
                  slt         a0, a1, a0
                  c.srai      a3, 12
                  sra         t2, sp, s1
                  c.addi16sp  sp, 448
                  c.addi4spn  a3, sp, 704
                  srl         tp, gp, s8
                  andi        ra, a6, 1119
                  c.or        a3, a3
                  c.slli      ra, 15
                  c.slli      a7, 2
                  slt         a6, ra, a0
                  sltu        zero, a6, s10
                  c.slli      ra, 26
                  sltiu       sp, sp, 1105
                  slti        a5, s6, 1279
                  c.add       s4, a3
                  slti        t0, s7, -1002
                  nop
                  c.addi16sp  sp, 192
                  addi        a7, s0, -1702
                  c.xor       a1, a3
                  sll         a3, t1, t0
                  div         s0, s5, sp
                  srl         a0, s2, t4
                  c.xor       a3, a3
                  srl         s1, s7, s7
                  sltu        s7, a0, s5
                  sll         s9, s4, ra
                  nop
                  c.addi16sp  sp, 96
                  c.addi      s10, 10
                  andi        zero, t1, -1127
                  c.srli      a3, 22
                  slt         s1, t4, a1
                  c.add       a5, a3
                  slt         a4, s2, s7
                  div         s3, s1, t0
                  auipc       zero, 558169
                  divu        a4, ra, s5
                  c.srai      a3, 2
                  c.nop
                  sltiu       s1, s5, -1893
                  sll         a2, t2, a7
                  xori        zero, s0, -221
                  c.slli      a3, 10
                  sll         s10, s4, t2
                  c.and       a5, a3
                  c.and       a3, a3
                  c.lui       tp, 7
                  sltu        s3, t3, a7
                  div         a4, a0, a4
                  c.sub       a3, a3
                  sltu        ra, s0, t3
                  mulh        a1, s2, s2
                  c.addi4spn  a3, sp, 704
                  sub         a2, a5, s11
                  srl         s7, s10, s10
                  add         zero, t0, tp
                  sltiu       s0, a4, -1347
                  srl         s0, a6, s10
                  sll         a2, s2, a5
                  c.lui       a2, 25
                  c.mv        ra, gp
                  c.sub       a3, a3
                  c.mv        ra, a0
                  sltu        s2, s1, zero
                  add         sp, a0, t4
                  c.sub       a3, a5
                  mulhsu      a1, s7, s5
                  xori        s5, s10, -1285
                  nop
                  mul         s1, tp, t2
                  c.li        a0, 22
                  c.lui       a6, 11
                  and         t1, s0, a7
                  divu        s3, s2, sp
                  c.and       a3, a3
                  c.srli      a3, 21
                  c.or        s0, a4
                  c.mv        a2, t3
                  srai        s10, s8, 23
                  add         t0, a7, a2
                  sltu        s2, s1, zero
                  srl         a1, s10, s11
                  rem         s0, s7, t2
                  c.addi16sp  sp, -16
                  and         a2, zero, a7
                  nop
                  c.slli      s9, 23
                  c.andi      a3, -1
                  c.and       a3, a3
                  auipc       sp, 1007010
                  c.addi      a7, -1
                  c.lui       s3, 29
                  c.xor       a3, a0
                  c.slli      ra, 27
                  c.lui       t1, 22
                  add         s1, zero, s5
                  rem         a4, a1, t6
                  xori        a6, t5, 1365
                  c.addi      ra, 22
                  auipc       s7, 486840
                  add         t2, t6, s5
                  c.nop
                  slti        t0, s6, 1017
                  addi        a4, tp, 231
                  c.add       s2, s9
                  add         t2, sp, s0
                  or          a7, a5, sp
                  c.li        a0, -1
                  or          sp, gp, gp
                  lui         s9, 380126
                  c.sub       a3, a3
                  sll         t2, a1, a4
                  slti        sp, s8, 559
                  srli        zero, s8, 22
                  sub         zero, s4, sp
                  c.or        a3, a1
                  div         s1, t3, s11
                  sra         a6, s11, s8
                  srli        zero, a3, 16
                  mulhu       t1, s0, s1
                  div         s3, zero, s8
                  slli        a3, s0, 12
                  mul         s1, s7, t2
                  add         t0, s11, s6
                  c.srli      a3, 14
                  c.sub       a3, a3
                  mul         s8, sp, s7
                  c.addi16sp  sp, -16
                  c.srli      a3, 18
                  c.slli      s6, 23
                  and         sp, s4, s4
                  c.addi4spn  a3, sp, 384
                  and         t0, sp, t1
                  c.and       a3, a3
                  c.andi      a3, 23
                  c.sub       a3, a3
                  nop
                  mulhu       a7, a1, s10
                  srl         zero, s11, s8
                  mulh        s7, s6, a5
                  c.xor       a3, a1
                  sltu        s1, a2, zero
                  add         a2, s3, s6
                  c.srli      a3, 31
                  sub         s2, s9, t4
                  and         a5, t2, s8
                  c.and       a3, a2
                  c.addi16sp  sp, -16
                  c.xor       a3, a2
                  nop
                  andi        sp, t3, -949
                  c.nop
                  c.addi      tp, -1
                  nop
                  c.addi      a5, 1
                  or          s0, s0, a7
                  ori         zero, s7, -408
                  srli        s5, tp, 24
                  srli        s0, t5, 27
                  mulhu       t2, sp, s3
                  li         t4, 0x1a239855 #start riscv_int_numeric_corner_stream_23
                  li         a1, 0x0
                  li         t3, 0x0
                  li         s5, 0x0
                  li         s8, 0x0
                  li         s10, 0x1
                  li         a2, 0x5d51eb9f
                  li         s9, 0x0
                  li         a7, 0x0
                  li         s4, 0x0
                  c.addi      a1, -1
                  mulh        s1, s0, tp
                  lui         zero, 273080
                  nop
                  c.lui       ra, 12
                  rem         a1, s0, a6
                  auipc       zero, 483555
                  c.sub       a3, a0
                  c.sub       a3, a3
                  auipc       s1, 133860
                  mulhsu      a4, zero, s6
                  rem         a1, gp, a5
                  mulhsu      a7, a1, a5
                  auipc       t3, 93060
                  lui         s10, 645108
                  c.addi4spn  a3, sp, 128
                  divu        a7, t0, t5
                  c.add       gp, t3
                  c.add       s6, s10
                  andi        t1, a5, -1020
                  c.xor       a3, a3
                  c.lui       t0, 12
                  c.addi4spn  a5, sp, 192
                  xori        s10, s5, 565
                  c.mv        ra, s5
                  c.add       gp, t3
                  srl         s1, s2, tp
                  c.nop
                  nop
                  c.li        a6, -1
                  c.slli      s6, 22
                  sltu        s6, s8, s8
                  div         a4, tp, s0
                  c.addi4spn  a3, sp, 736
                  c.slli      tp, 9
                  rem         s7, s10, s1
                  sub         a1, a1, t1
                  xori        t2, s5, 1448
                  c.addi4spn  a3, sp, 640
                  sltu        a6, t3, s2
                  c.mv        s6, s10
                  nop
                  c.addi      ra, 12
                  c.add       tp, t0
                  slli        t3, t0, 18
                  c.li        t1, -1
                  mulh        zero, gp, s4
                  sra         a4, zero, a0
                  slt         t4, s7, a3
                  and         s8, t1, s3
                  c.add       t4, gp
                  nop
                  ori         a4, s9, -743
                  nop
                  sll         zero, s6, s2
                  slti        ra, a5, -681
                  c.srai      a3, 5
                  c.sub       a1, s0
                  sub         s0, t6, tp
                  lui         t0, 597684
                  divu        t2, s0, s8
                  add         s1, t5, a6
                  mul         ra, a2, s4
                  sltu        a0, t5, t6
                  addi        s4, s4, -1693
                  rem         a1, s6, s8
                  ori         sp, s7, -635
                  c.srli      a3, 24
                  c.nop
                  div         s0, t1, a2
                  c.addi4spn  a3, sp, 448
                  c.xor       a3, a3
                  addi        zero, a1, -807
                  sltu        sp, s10, s2
                  sll         t2, s5, s10
                  sltiu       a6, s2, -1902
                  c.nop
                  div         t0, a3, a3
                  lui         a5, 274123
                  sra         t0, s2, tp
                  sltiu       a2, s0, 697
                  c.srai      a1, 11
                  sltu        s2, t3, gp
                  sra         s1, a3, a1
                  mulhu       s7, s2, a2
                  mul         t2, ra, t1
                  sub         s7, a2, a3
                  lui         a3, 942355
                  add         s5, s3, a2
                  slti        a3, a1, -798
                  srl         a3, s7, s3
                  c.add       s4, s3
                  c.andi      a3, 20
                  mul         s10, s0, s2
                  sltiu       sp, a2, -142
                  c.slli      sp, 28
                  lui         t4, 997115
                  c.or        a3, a5
                  xor         zero, ra, zero
                  c.sub       s0, a2
                  mulhsu      s3, a2, s10
                  div         s10, a3, ra
                  sll         a3, s1, a0
                  sll         a2, s4, s4
                  ori         t0, s7, -1942
                  srli        t1, t4, 28
                  sltiu       s1, tp, -1377
                  slt         s9, gp, t2
                  divu        s4, t5, a6
                  srl         t4, a1, a1
                  sltu        zero, s3, a3
                  mulhsu      a5, a3, s4
                  mulhu       s7, a4, gp
                  andi        s0, a1, 886
                  rem         zero, t2, ra
                  mulhu       t1, s1, t0
                  c.li        a5, -1
                  c.or        a3, a3
                  c.add       ra, a6
                  xor         a4, a6, t5
                  sltu        s3, s8, zero
                  or          gp, s0, s8
                  c.add       a6, s7
                  sltiu       s7, a7, 195
                  sub         s4, s2, a2
                  sub         t3, t1, sp
                  c.sub       a3, a0
                  addi        t0, sp, 1808
                  c.li        s1, -1
                  srai        zero, a3, 10
                  c.srli      a3, 22
                  srli        a0, t2, 26
                  lui         t4, 246331
                  or          s8, s7, t3
                  c.and       a3, a3
                  c.lui       t4, 10
                  c.andi      a3, -1
                  c.or        a3, a3
                  c.and       a2, s1
                  div         a7, a6, s4
                  or          zero, t0, tp
                  div         s0, ra, t4
                  c.sub       a3, a3
                  sll         s8, a1, s4
                  slt         sp, t0, s7
                  addi        t2, t3, -1281
                  sltiu       s10, a4, 347
                  sll         s4, s8, s2
                  add         s6, t0, a3
                  and         a7, s5, t6
                  add         a7, a0, s3
                  mul         t3, s3, a2
                  c.li        ra, -1
                  srl         zero, a1, t2
                  sra         a5, t2, a6
                  c.and       a3, a3
                  c.xor       a3, a3
                  auipc       zero, 183012
                  xor         s10, t1, s3
                  c.add       s0, a2
                  lui         a1, 441804
                  div         tp, a3, a1
                  sll         s1, s9, t4
                  addi        t2, s3, -951
                  c.srli      a3, 5
                  lui         zero, 938652
                  slli        s7, s9, 25
                  srl         s9, t0, t1
                  c.and       a4, a3
                  c.addi      t2, -1
                  slli        a7, a3, 21
                  lui         s7, 382970
                  mulhsu      s2, ra, sp
                  mulhsu      zero, a3, a0
                  c.addi16sp  sp, -16
                  lui         s10, 641778
                  nop
                  addi        a6, t0, -1166
                  srli        t0, s5, 2
                  c.addi4spn  a3, sp, 320
                  sltu        s2, t1, s6
                  c.lui       gp, 29
                  add         a7, tp, a1
                  c.mv        t0, s6
                  c.lui       a4, 4
                  lui         s10, 335447
                  c.and       a3, a1
                  c.mv        t3, s10
                  mul         zero, s2, s3
                  c.srai      a3, 16
                  c.sub       s0, a3
                  xor         t0, a3, s3
                  c.srli      s1, 24
                  sltiu       gp, a5, -619
                  sub         zero, s3, s9
                  c.or        a3, a3
                  ori         s8, s2, 1714
                  sub         gp, s8, a4
                  slli        tp, s9, 10
                  addi        gp, s10, 1079
                  c.add       ra, s10
                  nop
                  c.sub       a3, a3
                  c.addi      s9, 29
                  mulhu       t1, t4, a1
                  slt         s3, ra, t4
                  c.lui       s8, 8
                  c.andi      a3, -1
                  slt         zero, s0, s2
                  slli        s4, s9, 6
                  slti        s1, s3, 1555
                  xor         a1, zero, zero
                  c.or        a3, a3
                  slt         a3, t1, s7
                  nop
                  nop
                  slt         a4, a1, a0
                  sltu        a3, t1, gp
                  c.mv        s7, a6
                  mul         s10, s8, s1
                  mulhsu      s8, t2, s9
                  or          a0, s5, s11
                  c.nop
                  c.add       a2, a0
                  srl         s8, a7, s5
                  sltiu       s4, s10, -1880
                  c.lui       a6, 11
                  sltiu       s6, s9, -1762
                  c.slli      s3, 29
                  slti        s4, tp, -1279
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_6
                  li         ra, 0x1
                  li         a7, 0x0
                  li         t3, 0x1
                  li         s10, 0x0
                  li         s0, 0x41e3731
                  li         s1, 0x0
                  li         s8, 0x63d13094
                  li         s2, 0x0
                  li         s4, 0x0
                  lui         s10, 36741
                  nop
                  mulhu       a3, t3, s11
                  c.li        s7, 29
                  divu        zero, t5, tp
                  auipc       sp, 789609
                  rem         t0, t5, t0
                  addi        a3, s11, 1576
                  mulhsu      t4, a4, a3
                  mulh        s3, s7, ra
                  sub         t2, t0, sp
                  rem         s9, s4, t1
                  mul         ra, s5, t4
                  c.sub       a4, a3
                  rem         t3, t2, a6
                  mul         t2, t6, s10
                  add         zero, s0, t0
                  c.li        s6, 26
                  mulhsu      s3, s11, s10
                  mulhu       s10, t2, t5
                  mulh        t0, t6, s2
                  rem         t4, a1, s8
                  mulhsu      s10, t1, t2
                  c.nop
                  c.add       ra, ra
                  sub         a4, t3, t0
                  div         s9, t2, s5
                  divu        tp, t5, s3 #end riscv_int_numeric_corner_stream_6
                  c.srai      a3, 11
                  c.srai      a3, 19
                  div         gp, gp, s4
                  c.add       gp, a7
                  c.or        a3, a2
                  lui         zero, 570188
                  nop
                  ori         s6, s2, 106
                  mulhsu      s1, s8, sp
                  slti        t4, zero, -416
                  srl         a7, a7, gp
                  c.srli      a3, 16
                  c.xor       a2, a3
                  nop
                  divu        a4, t3, s7
                  ori         t2, a0, 493
                  c.addi      s1, -1
                  c.addi4spn  a3, sp, 128
                  sub         a4, gp, s5
                  c.addi      s8, 21
                  xor         t4, s6, t2
                  slli        s2, s7, 7
                  c.srli      a3, 18
                  auipc       s0, 708364
                  c.xor       a3, a3
                  c.addi      ra, -1
                  xori        a3, a1, -857
                  c.and       a3, a3
                  c.addi      a7, 29
                  slli        a6, t0, 26
                  c.add       t2, s11
                  rem         s10, s0, s6
                  c.srai      a3, 21
                  mul         s8, tp, t3
                  andi        s0, s0, -1645
                  slli        s0, a4, 22
                  sub         a5, t2, s2
                  slti        t1, t2, -358
                  and         s3, t6, s7
                  c.add       a2, a5
                  slli        t4, a6, 12
                  c.addi16sp  sp, -16
                  srl         a5, a7, t1
                  c.srli      a3, 19
                  and         s0, a0, t6
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_26
                  li         t3, 0x1
                  li         s8, 0x0
                  li         a2, 0x0
                  li         a3, 0x1
                  li         s9, 0x6a877e74
                  li         tp, 0x0
                  li         t1, 0x0
                  li         a5, 0x0
                  li         s2, 0x1
                  divu        a0, tp, ra
                  rem         t0, t4, s0
                  c.add       tp, t0
                  addi        a5, t3, 1646
                  c.nop
                  c.addi16sp  sp, -16
                  rem         s7, s6, t1
                  mulh        a4, t6, t2
                  c.lui       ra, 20
                  mulhu       s0, zero, s5
                  addi        a4, t4, -1306
                  lui         s0, 565435
                  mul         s9, s1, t0
                  mulhu       s0, a2, s9
                  c.addi4spn  a3, sp, 352
                  c.addi4spn  a3, sp, 144
                  add         tp, a5, t1
                  c.li        a5, 25
                  nop
                  sub         zero, s0, s6
                  c.addi4spn  a3, sp, 320
                  mul         s3, s1, s1
                  div         t1, zero, s7
                  divu        zero, a1, t6 #end riscv_int_numeric_corner_stream_26
                  c.add       sp, t3
                  c.xor       a3, a2
                  add         ra, s0, s3
                  lui         sp, 911539
                  mul         s3, a0, sp
                  slt         tp, s7, a3
                  c.andi      a3, 13
                  sll         a1, t6, t2
                  sll         s0, a3, t5
                  slti        s10, a5, 1633
                  or          zero, t5, a3
                  sltu        zero, t2, s7
                  srai        t2, t0, 25
                  mulhu       gp, s2, s3
                  nop
                  ori         s8, a3, 1826
                  add         a2, t3, a4
                  c.or        a3, a3
                  auipc       a4, 262668
                  andi        a0, s5, -108
                  c.and       a3, a3
                  c.mv        ra, a1
                  and         t2, t2, ra
                  slt         a6, s2, a7
                  slli        a0, a5, 0
                  mulhu       zero, t2, t2
                  div         a2, a2, a5
                  div         t0, t4, a3
                  srli        a0, a1, 15
                  slt         a7, s10, s10
                  auipc       s5, 2220
                  c.lui       ra, 7
                  slli        s6, s8, 11
                  slli        gp, s4, 5
                  c.xor       a2, a2
                  divu        s9, t5, s6
                  sra         a4, s0, a1
                  c.mv        ra, s5
                  sub         s6, s6, gp
                  c.srli      a3, 6
                  sltu        a0, s3, s5
                  auipc       t2, 436336
                  auipc       s1, 502258
                  sltu        ra, s9, t1
                  c.li        a2, 10
                  add         s1, s2, t4
                  sra         s5, s11, t5
                  c.srai      a3, 8
                  c.or        a3, a2
                  c.and       a0, a3
                  auipc       a7, 875723
                  div         s5, t2, s3
                  andi        s0, a3, 1409
                  nop
                  sub         sp, ra, a4
                  sra         s2, tp, a6
                  c.addi16sp  sp, -16
                  andi        zero, t5, -620
                  c.addi4spn  a3, sp, 960
                  srai        s9, a4, 3
                  slti        a1, s10, 1276
                  srl         s8, s10, gp
                  addi        zero, t1, 1904
                  mulhu       s0, zero, sp
                  slli        a0, a7, 20
                  div         s3, a5, s8
                  or          a0, s8, a1
                  c.addi4spn  a3, sp, 320
                  andi        ra, a7, -394
                  nop
                  c.mv        a2, sp
                  lui         a4, 718962
                  sll         a0, a7, a4
                  ori         t3, s0, 305
                  xor         a0, a1, s0
                  c.mv        s4, s8
                  c.addi4spn  a3, sp, 896
                  c.srli      a5, 15
                  srli        zero, tp, 21
                  c.srli      a5, 16
                  c.sub       a3, a3
                  xor         t0, s4, s1
                  c.addi      a2, -1
                  c.li        s8, 11
                  c.xor       a3, a3
                  and         a7, s10, t0
                  c.li        a4, -1
                  c.addi4spn  a3, sp, 896
                  c.add       ra, t0
                  sltu        tp, tp, zero
                  xor         t3, s2, a7
                  c.and       a1, a0
                  c.and       a3, a3
                  and         zero, a4, a4
                  c.srai      a4, 23
                  c.srai      a3, 14
                  c.srai      a3, 26
                  c.li        s9, 24
                  c.xor       s1, a3
                  c.lui       s7, 18
                  mulhsu      s3, s7, t6
                  c.addi4spn  a3, sp, 640
                  srl         tp, s1, s9
                  c.slli      s0, 24
                  rem         t2, t0, t6
                  ori         s6, s3, 1904
                  c.addi4spn  a1, sp, 976
                  sltiu       a5, t0, -2038
                  divu        gp, s0, a2
                  addi        s5, s11, 1997
                  sra         s9, s1, a4
                  srai        s1, s1, 28
                  div         a3, t0, s4
                  sltu        t2, a6, s7
                  c.add       s6, s4
                  srai        t0, zero, 19
                  c.sub       s1, a3
                  add         tp, t1, zero
                  addi        s0, t5, -62
                  addi        a5, s2, -458
                  mulhsu      s10, a2, t6
                  c.mv        s6, s3
                  sub         a6, a5, a0
                  sub         zero, a7, sp
                  c.addi4spn  a0, sp, 192
                  ori         sp, t0, -722
                  mulhsu      s5, ra, s0
                  c.lui       ra, 17
                  c.mv        s3, s1
                  c.or        a3, a3
                  mulhsu      t0, t1, s5
                  c.or        a3, a3
                  andi        s4, a7, 757
                  mulhsu      zero, zero, t6
                  c.addi4spn  a3, sp, 832
                  auipc       s0, 367055
                  and         a0, t5, t2
                  c.addi      s3, 7
                  or          zero, t2, t1
                  nop
                  c.add       t4, t2
                  auipc       s1, 410981
                  sll         t1, t5, s1
                  c.or        a3, s0
                  and         s8, zero, a6
                  c.andi      a3, 22
                  c.addi16sp  sp, -16
                  srl         t1, a4, s4
                  mul         s6, a4, t1
                  slti        a5, a2, 1664
                  sra         a7, t2, zero
                  slli        s10, a2, 9
                  sub         a6, s9, s4
                  and         a4, s8, a1
                  mulhsu      s2, s6, s0
                  xori        s8, s0, 563
                  c.mv        t0, s10
                  c.addi16sp  sp, -16
                  or          gp, t4, t0
                  c.addi16sp  sp, -16
                  c.addi4spn  s1, sp, 576
                  c.addi      a7, -1
                  add         tp, a2, zero
                  slli        s1, t6, 30
                  srli        a3, gp, 17
                  slli        t2, a6, 9
                  divu        gp, s10, sp
                  rem         a2, s5, gp
                  c.addi4spn  a3, sp, 96
                  andi        a2, a7, 1867
                  xori        a7, s0, 1372
                  sll         s8, gp, tp
                  slt         t0, zero, a2
                  c.addi      s10, -1
                  c.srli      a3, 1
                  slt         a4, s7, s3
                  nop
                  c.or        a3, a1
                  ori         s4, t5, -658
                  srai        a5, a7, 25
                  nop
                  c.mv        ra, s1
                  c.and       a3, a3
                  sltu        zero, t2, a6
                  c.or        a3, a3
                  sltiu       t2, a5, -370
                  slti        t2, s8, 492
                  nop
                  c.or        a3, a3
                  sll         s10, t3, t4
                  srli        a4, sp, 27
                  sltu        zero, s6, s11
                  mulhu       zero, s3, a6
                  srli        a6, a0, 31
                  c.li        ra, 4
                  add         s3, s4, s0
                  mulh        a2, a3, a7
                  sub         s8, sp, a5
                  slli        zero, s4, 1
                  slli        a4, ra, 29
                  srai        s6, a0, 0
                  slt         s10, a1, s4
                  c.li        tp, -1
                  divu        zero, s7, a7
                  sltu        a6, s5, sp
                  c.addi16sp  sp, -16
                  c.andi      a3, 10
                  c.addi4spn  a3, sp, 976
                  c.mv        a5, s0
                  c.srai      a3, 14
                  xori        a2, tp, -5
                  and         t4, a0, a4
                  c.addi      t3, 7
                  and         a0, a6, a7
                  c.nop
                  xori        s0, s3, 674
                  srai        s6, s5, 20
                  or          t3, tp, s7
                  sltu        s6, a2, s6
                  c.andi      a3, -1
                  nop
                  c.li        a2, -1
                  c.add       ra, s5
                  nop
                  sra         a4, zero, s3
                  c.sub       a3, a5
                  c.srli      a3, 21
                  div         s1, t3, sp
                  lui         t3, 99565
                  mulh        t2, s11, t4
                  srai        a0, zero, 31
                  addi        a1, a3, 1258
                  c.nop
                  c.nop
                  auipc       s1, 1042656
                  mulhu       s2, s8, zero
                  xor         t3, s6, t1
                  rem         t0, t1, a4
                  addi        zero, a5, -1195
                  slli        tp, s11, 16
                  auipc       s1, 857876
                  xor         a1, s5, s5
                  sub         t2, s8, t2
                  andi        s8, t3, 1298
                  lui         s6, 316675
                  slli        tp, s4, 0
                  sltiu       zero, a2, 490
                  auipc       a1, 319371
                  xor         tp, s2, s0
                  ori         zero, t0, 97
                  slti        s10, t6, -1578
                  c.andi      a3, 5
                  addi        a7, a5, -1788
                  sltiu       a1, t4, 998
                  andi        s9, a7, -166
                  lui         a0, 359195
                  c.addi4spn  a3, sp, 784
                  divu        s0, s9, s7
                  nop
                  srl         t3, tp, s2
                  slt         t1, s7, s0
                  mulhu       s2, tp, s6
                  sltiu       a0, gp, -41
                  mulhsu      s7, s0, s2
                  addi        t3, s7, 105
                  c.andi      a3, -1
                  lui         a6, 176287
                  nop
                  ori         t0, tp, -466
                  c.and       a3, a3
                  c.or        a3, a3
                  nop
                  c.and       a3, a3
                  c.or        a3, a3
                  srl         s0, tp, s10
                  sll         s10, a3, s7
                  and         t0, a4, t4
                  nop
                  sll         gp, s9, t3
                  c.nop
                  slt         s0, ra, s4
                  sll         t3, a3, zero
                  addi        s5, s4, 1214
                  mulhsu      s5, s7, zero
                  slt         s7, a3, a6
                  sll         t3, t0, tp
                  c.mv        ra, t5
                  c.add       t0, gp
                  c.li        t4, 14
                  sltiu       zero, t2, 1684
                  mul         t1, a6, s8
                  xori        s2, zero, -1545
                  c.mv        a4, a1
                  andi        a3, tp, 316
                  mulhsu      s6, a7, a3
                  andi        t0, s9, -1101
                  c.srli      a3, 26
                  slt         t3, s9, a3
                  mulhu       s1, a2, t5
                  xori        s10, s7, -286
                  c.andi      a3, 30
                  xor         zero, gp, a2
                  c.li        s0, 19
                  slt         a3, zero, tp
                  c.and       a3, a1
                  c.addi4spn  s0, sp, 96
                  srl         a1, a1, a3
                  c.addi      gp, 14
                  srli        t4, t5, 22
                  auipc       zero, 90858
                  mulhu       t4, t3, t4
                  ori         s5, s0, 1745
                  mulhu       t2, zero, t6
                  c.andi      a3, 13
                  ori         a3, t0, -1472
                  c.addi4spn  a3, sp, 160
                  or          s2, s10, s8
                  sll         s4, a1, a5
                  c.nop
                  addi        s7, s6, -263
                  c.slli      s2, 8
                  c.srli      a3, 12
                  slti        s2, s0, -275
                  c.xor       a3, a4
                  nop
                  sltiu       s9, a2, 421
                  c.addi16sp  sp, -16
                  c.srai      a3, 22
                  c.nop
                  c.li        ra, -1
                  add         t3, a0, a3
                  mulhu       s10, t5, t1
                  c.add       a7, s6
                  sltu        s5, s8, a1
                  xori        a3, t1, 866
                  slli        t3, s0, 0
                  c.addi16sp  sp, 272
                  c.slli      s3, 3
                  auipc       t1, 2739
                  xori        tp, a7, -387
                  sltiu       a0, s5, -1054
                  srli        s8, zero, 15
                  and         t1, s7, s7
                  sra         s9, a4, s6
                  srai        s3, a0, 3
                  c.and       a3, a3
                  c.add       s0, s1
                  c.andi      a1, 30
                  nop
                  c.lui       ra, 14
                  and         s4, t0, s10
                  c.add       ra, s8
                  c.addi4spn  a3, sp, 352
                  c.srai      a1, 24
                  c.li        s0, -1
                  srai        t1, s6, 16
                  c.sub       a3, a3
                  c.andi      a3, 16
                  c.srai      a3, 17
                  slli        s3, s1, 24
                  add         t4, s1, a0
                  mul         t3, a2, t5
                  c.add       s1, a3
                  c.nop
                  and         s2, t6, s3
                  divu        tp, gp, s0
                  c.and       a3, a3
                  c.srai      a3, 26
                  andi        s0, a7, 413
                  srl         t0, s1, s7
                  sra         zero, a6, s2
                  c.or        a3, a3
                  xori        a4, gp, 142
                  div         t0, s4, a4
                  c.sub       a1, a0
                  c.add       s5, a3
                  sra         s1, a4, s1
                  sll         a4, s2, s7
                  divu        a6, s11, t5
                  srl         s4, s10, s7
                  addi        a5, a4, -952
                  c.sub       a3, a3
                  c.mv        s3, s4
                  and         s5, t1, ra
                  c.andi      a3, -1
                  c.add       s8, sp
                  sll         t1, s0, s9
                  sub         t3, s8, s6
                  c.nop
                  sra         t0, a0, t1
                  xori        a4, a0, -1345
                  c.and       s1, a3
                  andi        a6, ra, 769
                  c.or        a0, a1
                  sra         s7, sp, s8
                  and         s8, sp, a5
                  c.sub       a3, a3
                  c.xor       a2, a3
                  addi        a3, s10, -1741
                  addi        a1, s5, 1669
                  mul         t3, s0, sp
                  div         sp, t4, s0
                  andi        s4, a1, -1797
                  div         a0, t1, t6
                  sra         zero, s3, a7
                  c.sub       a3, a5
                  c.add       s2, t2
                  add         t2, s3, s3
                  sltiu       s1, s9, -661
                  c.addi      s2, -1
                  srli        sp, t4, 24
                  slt         a0, s2, s8
                  ori         s9, s1, 368
                  srl         ra, s4, s2
                  srai        zero, s3, 28
                  c.xor       a3, a3
                  c.xor       a3, a3
                  c.and       a3, a3
                  c.li        ra, 11
                  div         a1, t6, t6
                  lui         gp, 786413
                  c.addi      s4, 20
                  c.slli      a6, 24
                  sltu        a6, s10, t3
                  nop
                  c.addi16sp  sp, 192
                  mulhsu      s9, t1, t6
                  div         gp, a0, s9
                  srl         a3, s3, s6
                  xor         s0, t6, s8
                  c.srai      a3, 22
                  sra         a5, a5, s0
                  addi        s2, s1, 364
                  c.nop
                  slti        a5, t0, -1860
                  c.addi4spn  a3, sp, 128
                  auipc       gp, 550198
                  slt         t1, zero, t2
                  sll         a5, sp, t2
                  sll         a3, t2, ra
                  c.sub       a3, a3
                  c.xor       a3, a3
                  c.and       a3, a3
                  slli        ra, s7, 25
                  c.li        a4, 27
                  srli        t4, a4, 24
                  mul         zero, s6, s2
                  or          zero, s0, s9
                  c.li        s6, -1
                  sltu        s5, s0, s1
                  c.lui       t2, 21
                  srai        t3, a6, 2
                  mulhu       s5, s7, s9
                  c.mv        t3, t0
                  srli        t4, t6, 3
                  c.addi      a2, -1
                  c.and       a3, a3
                  c.srli      a3, 10
                  sltu        a3, s0, a4
                  c.andi      a2, -1
                  slti        sp, a5, 1803
                  rem         gp, tp, gp
                  mul         s4, t1, zero
                  addi        zero, s7, -977
                  c.srli      a3, 25
                  c.addi16sp  sp, -16
                  andi        a6, a7, 326
                  c.li        s4, -1
                  div         a1, t4, a1
                  mulh        a5, s4, s11
                  c.sub       s0, a3
                  addi        gp, t3, -1209
                  mul         t2, a0, s1
                  mul         s0, a2, s8
                  sltu        ra, s10, s4
                  c.slli      s9, 15
                  mulh        zero, s9, t0
                  slt         gp, s3, sp
                  auipc       a2, 446728
                  c.sub       a3, a3
                  slti        s8, t4, 1160
                  rem         s7, s10, t1
                  c.mv        s0, a7
                  c.srai      a3, 20
                  c.srli      a3, 29
                  c.xor       a2, s0
                  mulhsu      s2, a5, a2
                  c.or        a5, a3
                  c.add       a2, a2
                  rem         ra, t4, s4
                  c.srli      a3, 17
                  sltu        a2, s9, gp
                  c.xor       a3, a3
                  c.addi4spn  a3, sp, 352
                  c.addi16sp  sp, 96
                  addi        s3, t4, 823
                  c.addi4spn  a3, sp, 704
                  sub         t1, s7, t3
                  rem         a6, a2, s3
                  c.lui       a4, 1
                  c.or        a3, a3
                  c.addi      s4, -1
                  c.sub       a2, a3
                  mulhu       a4, tp, a2
                  mul         a0, tp, s5
                  auipc       tp, 877233
                  rem         s3, s1, ra
                  and         s4, zero, ra
                  mulhsu      a5, s2, ra
                  xor         a5, s7, sp
                  nop
                  slli        s1, s6, 10
                  c.nop
                  sra         sp, s9, t4
                  sltu        a1, a4, t1
                  c.srai      a3, 5
                  c.andi      a3, 22
                  addi        s4, t3, -1783
                  mulhsu      zero, s4, gp
                  c.srli      a3, 27
                  c.mv        tp, tp
                  divu        s7, a7, a6
                  c.andi      a3, -1
                  c.li        s9, -1
                  lui         a6, 119576
                  srai        a0, t2, 10
                  sltu        s1, s7, s11
                  auipc       t1, 763435
                  xor         t3, s0, sp
                  mulhu       zero, a3, t1
                  addi        s9, s1, -715
                  c.sub       a3, a3
                  sltu        t0, t1, a7
                  and         s8, t4, a4
                  nop
                  slti        t0, s9, -1271
                  c.sub       a3, a3
                  c.addi      a0, -1
                  c.srli      s0, 2
                  mul         zero, t5, a3
                  mulhu       ra, s0, a6
                  c.or        a3, a3
                  xori        a7, sp, 903
                  mul         ra, t5, s10
                  andi        s7, s1, 231
                  c.addi16sp  sp, -16
                  rem         s3, s4, s3
                  div         tp, zero, s9
                  sltu        a7, a7, a3
                  srl         t4, a1, t2
                  sll         a0, gp, a0
                  and         zero, a0, a2
                  c.andi      a4, -1
                  and         t1, s4, t5
                  sltu        s10, s0, s5
                  div         a4, t3, ra
                  srai        a6, s0, 21
                  c.mv        t3, s7
                  mulhu       s8, t0, s11
                  andi        tp, zero, -1698
                  c.xor       a3, a5
                  xori        tp, s10, 957
                  slt         zero, s9, s9
                  slli        gp, a5, 30
                  c.li        t1, 9
                  c.slli      t4, 4
                  rem         a3, s5, s10
                  c.and       a3, a3
                  c.li        t3, -1
                  c.and       a3, a3
                  c.lui       s10, 23
                  slli        s0, tp, 13
                  c.andi      a5, -1
                  c.andi      s0, 31
                  xori        gp, t1, -1954
                  mul         s2, t0, a4
                  c.addi      t1, -1
                  lui         a1, 561961
                  sll         a0, t6, s10
                  mulhsu      a2, s6, a2
                  andi        s5, gp, -942
                  c.slli      s7, 24
                  divu        t0, zero, t3
                  c.srli      a3, 10
                  sra         t0, t4, t3
                  divu        s9, s1, s4
                  c.nop
                  c.sub       a0, a3
                  ori         a7, a3, 1386
                  c.add       a5, tp
                  c.add       s6, s6
                  srl         a1, s5, s0
                  sltu        s5, t2, t6
                  addi        zero, t5, -1449
                  andi        s3, s9, 109
                  c.add       a2, s2
                  c.mv        a2, t6
                  c.addi16sp  sp, 336
                  c.lui       ra, 4
                  and         s2, s10, a5
                  c.addi16sp  sp, 432
                  sub         zero, t2, a7
                  xor         t0, t5, t2
                  li         gp, 0x0 #start riscv_int_numeric_corner_stream_24
                  li         s7, 0x2771e328
                  li         t4, 0x1
                  li         s9, 0x71223625
                  li         a7, 0x6c41db9d
                  li         a3, 0x1f26b576
                  li         s8, 0x0
                  li         s5, 0x56a4481d
                  li         t3, 0x0
                  li         a2, 0x0
                  c.addi4spn  a3, sp, 128
                  c.lui       s5, 31
                  rem         a2, s3, a2
                  c.li        ra, 15
                  c.addi      t1, 21
                  rem         a6, s10, s1
                  mul         zero, t2, t6
                  mulhu       a5, ra, s6
                  nop
                  c.mv        s3, a7
                  divu        gp, s10, s7
                  c.nop
                  sub         s3, a6, s3
                  c.mv        a1, t4
                  nop
                  divu        zero, s1, s7
                  c.addi4spn  a3, sp, 640
                  add         t2, zero, sp
                  sub         s8, s9, s0
                  mulhsu      a3, t6, a5
                  c.mv        a7, s8
                  sub         zero, t2, s6
                  rem         s4, s10, t0
                  srl         t0, zero, a6
                  mulhsu      ra, zero, tp
                  c.mv        a0, t0
                  c.li        t4, -1
                  xor         gp, s5, a0
                  c.srli      a3, 25
                  rem         s2, a6, a0
                  add         s0, a2, t2
                  addi        s1, tp, -1416
                  c.nop
                  addi        a3, s5, -171
                  slti        t0, a5, 1421
                  xori        s7, s1, 864
                  auipc       tp, 362286
                  mul         s10, t6, a3
                  sll         s3, s0, t4
                  srai        t3, s3, 16
                  c.xor       a3, a1
                  mulh        a3, s3, s11
                  c.add       ra, t5
                  auipc       s8, 374741
                  c.li        s3, 11
                  sll         s2, s11, a2
                  c.slli      a6, 16
                  srl         s0, zero, s11
                  c.xor       a3, a3
                  c.lui       s2, 4
                  div         zero, s9, t4
                  sll         ra, t2, ra
                  and         t3, s9, s1
                  c.sub       a3, a3
                  c.addi16sp  sp, -16
                  andi        s6, ra, -604
                  srai        s4, s9, 13
                  and         gp, a3, a7
                  c.addi4spn  a4, sp, 320
                  xor         ra, s10, gp
                  andi        a1, t5, 1481
                  auipc       s2, 888067
                  c.addi      a5, 18
                  slt         s8, a4, gp
                  xori        zero, s5, 1679
                  c.srli      a3, 14
                  c.slli      s3, 10
                  c.srai      a3, 12
                  srli        zero, a6, 10
                  addi        a3, tp, 1715
                  sll         s9, s2, s5
                  sll         s3, a2, t6
                  or          a6, t5, s1
                  sltiu       tp, s1, 898
                  c.add       sp, gp
                  sll         s0, zero, a0
                  mulh        s2, s9, a4
                  xor         s3, s3, s5
                  div         a0, a0, s0
                  c.sub       a3, a3
                  mul         a6, s11, a2
                  ori         zero, a5, 896
                  sltiu       t1, s1, -33
                  sra         s5, gp, s6
                  sra         s10, t3, t6
                  nop
                  rem         s10, t6, s7
                  slti        sp, t5, -146
                  slti        s2, s5, -826
                  srl         zero, s8, t2
                  div         s4, t0, s7
                  c.lui       tp, 9
                  c.mv        t4, t2
                  c.slli      sp, 29
                  div         a0, zero, s10
                  c.srai      a4, 14
                  sub         t0, t5, s9
                  srl         s7, s7, a5
                  c.sub       a3, a3
                  andi        t4, s11, -734
                  c.and       s1, a3
                  c.xor       a3, a1
                  mul         zero, t1, a0
                  c.mv        a4, s5
                  mulh        tp, s3, s1
                  mulhsu      a6, s0, s7
                  c.sub       a3, a0
                  c.and       a3, a4
                  xori        s5, a2, 1079
                  c.li        a2, -1
                  c.or        a3, a3
                  c.addi      t3, 23
                  c.lui       ra, 12
                  divu        t0, s1, a7
                  c.addi16sp  sp, 192
                  mulh        a3, s0, t4
                  andi        t3, t0, -302
                  mulhsu      ra, tp, t0
                  sra         s9, s1, t0
                  c.and       a0, a1
                  c.and       a3, a3
                  slti        a7, t0, 1814
                  c.xor       a3, a3
                  divu        t2, t2, s0
                  xor         s7, s7, a3
                  xor         zero, s7, s10
                  sra         a2, zero, s9
                  c.add       a0, s11
                  auipc       a6, 1045217
                  and         a0, s0, tp
                  sra         s3, s3, t0
                  or          a6, a1, s6
                  auipc       a3, 574181
                  or          sp, t5, t6
                  c.srai      a3, 2
                  c.sub       a3, a3
                  li         t4, 0x0 #start riscv_int_numeric_corner_stream_11
                  li         t3, 0x0
                  li         a4, 0x0
                  li         s9, 0x0
                  li         tp, 0x2b0868f3
                  li         a5, 0x0
                  li         s4, 0x0
                  li         a2, 0x0
                  li         s3, 0x0
                  li         s8, 0x1
                  auipc       s0, 595562
                  sub         zero, a1, t1
                  nop
                  c.lui       a6, 2
                  mul         s3, t6, s3
                  lui         a4, 374793
                  mul         s3, a6, zero
                  c.addi4spn  s0, sp, 128
                  c.addi16sp  sp, 352
                  c.addi      s2, -1
                  mulh        a7, s11, gp
                  div         a1, s3, gp
                  c.sub       a3, a3
                  c.nop
                  c.addi      t2, 25
                  divu        a5, s7, s0
                  c.li        a3, 31
                  auipc       s3, 191165
                  c.add       t3, s8
                  auipc       s1, 582148
                  c.sub       a1, a3
                  mul         s5, s5, ra
                  mul         sp, a7, a1
                  mulhu       zero, a0, tp
                  sub         t0, s2, a6
                  c.lui       s0, 30
                  mulhsu      a0, a4, t2
                  and         a3, a3, t1
                  auipc       tp, 119900
                  c.slli      s7, 12
                  c.li        s3, 18
                  mulhu       a7, zero, s8
                  xori        ra, ra, 190
                  and         t4, a7, s6
                  sltu        ra, a4, a4
                  c.srai      a3, 8
                  divu        sp, t5, s6
                  nop
                  c.nop
                  xor         s2, a0, t4
                  mulh        a5, s7, s9
                  div         zero, a6, s9
                  c.andi      a3, -1
                  andi        a0, s1, 113
                  mulh        a7, sp, a3
                  addi        s4, a1, 321
                  srai        zero, a4, 18
                  add         a2, s8, ra
                  lui         s9, 365816
                  c.xor       s0, a3
                  c.nop
                  c.slli      s9, 31
                  slti        s3, s4, -1835
                  add         gp, a6, a4
                  sltiu       s1, s1, -1056
                  slt         sp, gp, ra
                  srli        zero, s10, 27
                  c.addi      s5, -1
                  slli        s8, s6, 3
                  c.addi4spn  a4, sp, 704
                  c.srli      a3, 11
                  c.slli      s2, 14
                  div         zero, s8, s9
                  srli        a1, a5, 12
                  xori        t3, s10, -1382
                  c.li        ra, 4
                  slt         ra, t4, a6
                  xor         gp, s8, s7
                  xori        s4, sp, -387
                  c.mv        gp, t5
                  mulhu       sp, a4, a1
                  srl         s8, t5, a0
                  auipc       t2, 984699
                  and         a3, t5, s6
                  add         s8, a3, t6
                  c.li        s1, -1
                  xori        s1, a4, -1622
                  mulh        s10, t0, t4
                  ori         ra, s9, -1177
                  srai        a2, s5, 26
                  c.andi      a3, 30
                  or          a0, s9, a4
                  xor         s9, a4, zero
                  sra         ra, s1, zero
                  mul         s0, t1, t1
                  rem         a1, sp, t6
                  mulhu       s5, ra, s2
                  and         s5, s9, s6
                  sra         s3, t0, t1
                  ori         a3, a2, -1789
                  mulh        t0, s4, s7
                  c.addi16sp  sp, 432
                  andi        zero, s10, 984
                  c.xor       a3, a3
                  c.mv        a4, s11
                  c.slli      a4, 7
                  divu        t2, a2, zero
                  divu        s0, t1, tp
                  slt         s8, a1, a6
                  c.slli      t1, 25
                  mulh        s5, t2, sp
                  mulh        a1, a5, zero
                  c.sub       a2, a3
                  c.or        a3, a3
                  or          sp, a4, tp
                  addi        zero, t0, -1950
                  c.xor       a3, a3
                  auipc       s8, 566050
                  sll         a2, t6, t4
                  c.or        s1, a3
                  sub         s8, tp, a7
                  addi        s6, s7, 1488
                  mulhu       a3, gp, s11
                  c.srli      a3, 17
                  c.addi      sp, 13
                  c.lui       ra, 12
                  mul         zero, s4, s3
                  ori         a3, gp, 1787
                  c.li        s6, 2
                  c.addi4spn  a3, sp, 384
                  xor         t2, s3, t0
                  c.li        ra, -1
                  c.xor       a3, a3
                  divu        s0, t6, s0
                  c.addi      tp, 24
                  c.xor       s1, a0
                  c.addi16sp  sp, -16
                  c.addi4spn  a3, sp, 128
                  xor         zero, t5, s1
                  xor         s0, a3, t2
                  c.add       ra, t0
                  c.lui       gp, 16
                  lui         a7, 656363
                  sub         s9, t6, ra
                  mulhsu      s5, a7, a1
                  c.andi      a3, -1
                  c.mv        s8, t4
                  rem         t0, s4, t4
                  andi        s10, tp, -1823
                  slt         s6, s1, t6
                  c.sub       a3, a3
                  c.srli      a3, 28
                  slt         ra, s0, tp
                  slti        s9, s5, 1381
                  c.or        a3, a3
                  c.addi16sp  sp, -16
                  ori         zero, a5, 631
                  sltu        s6, a7, t0
                  div         s2, gp, t3
                  mulhsu      zero, a3, t4
                  sra         zero, t3, s8
                  andi        a6, t3, 1610
                  c.xor       a5, a3
                  srai        a1, s5, 0
                  srli        s2, s5, 1
                  addi        ra, a6, 219
                  auipc       a3, 47197
                  rem         s6, t5, s3
                  srl         a1, s8, s3
                  divu        zero, zero, t4
                  c.add       s0, s7
                  c.and       a3, a3
                  c.lui       gp, 26
                  xor         s5, a4, t5
                  sltu        a5, s2, s1
                  or          s3, s10, s9
                  sra         zero, s10, s5
                  sltu        s9, t3, ra
                  c.mv        t0, a4
                  c.srli      a3, 25
                  c.addi16sp  sp, -16
                  c.li        s6, 24
                  srai        zero, s7, 15
                  c.slli      t1, 16
                  lui         t2, 133339
                  c.nop
                  auipc       s5, 572892
                  c.xor       a5, a3
                  mul         zero, a0, a6
                  slt         s3, t3, s6
                  sll         a3, zero, a0
                  and         s3, s11, t1
                  mulhu       t4, a0, a2
                  mul         s4, tp, t3
                  c.and       a3, a3
                  mulhsu      s3, t1, a6
                  nop
                  addi        a2, t4, -1038
                  c.mv        ra, a3
                  srai        tp, t1, 5
                  c.mv        a5, a2
                  c.add       a6, s6
                  srli        a6, t1, 1
                  c.or        a3, a1
                  slti        s5, a4, -2010
                  divu        s2, a6, t3
                  c.srli      a3, 3
                  c.sub       a3, a0
                  c.and       a3, a3
                  srl         s7, s11, s0
                  c.andi      a3, 1
                  mul         a6, tp, t0
                  sub         sp, a1, gp
                  lui         t3, 695186
                  xor         t0, gp, ra
                  c.and       a3, a5
                  sltiu       a1, tp, 282
                  c.lui       s5, 13
                  sltiu       zero, a3, 452
                  c.add       a2, t4
                  c.slli      t0, 28
                  or          zero, tp, t2
                  mulh        tp, s11, sp
                  c.li        t0, 23
                  c.xor       a3, a0
                  auipc       s8, 886030
                  lui         t3, 743237
                  add         t4, a1, t3
                  c.srli      a3, 23
                  c.slli      a7, 17
                  srai        s10, s6, 3
                  slt         gp, s11, ra
                  sub         ra, a6, a2
                  and         a3, sp, t1
                  divu        zero, a1, s5
                  slt         s2, s7, s8
                  andi        a1, s10, 1838
                  c.slli      a7, 15
                  c.andi      a3, -1
                  mul         zero, a3, t1
                  c.addi      a5, -1
                  sra         s8, s10, t1
                  andi        a7, s3, -573
                  c.andi      s1, -1
                  sub         zero, s11, t4
                  c.add       s7, t3
                  ori         gp, gp, -490
                  or          s1, s0, s3
                  ori         ra, tp, 1954
                  srai        a5, t4, 9
                  c.addi4spn  a3, sp, 64
                  sll         a1, a5, gp
                  mulhu       zero, a5, tp
                  sltiu       a1, s3, 1655
                  div         a2, s10, s3
                  c.li        s4, -1
                  xori        s9, tp, -1145
                  addi        t0, s4, 478
                  c.addi      a0, 3
                  sub         a5, s2, gp
                  rem         s9, tp, t2
                  c.add       a1, a5
                  srl         s3, s8, zero
                  srl         gp, s11, t5
                  mulhsu      ra, tp, sp
                  mulhsu      s9, t4, s3
                  ori         a0, s3, 109
                  lui         a2, 286540
                  nop
                  ori         a3, s2, -452
                  slt         s0, tp, s10
                  c.sub       s0, a3
                  c.mv        t0, a2
                  andi        gp, s4, -95
                  sltu        sp, gp, s7
                  c.xor       a3, a3
                  xor         s6, a5, t1
                  sub         t4, a5, a0
                  slt         a1, t2, s8
                  lui         a0, 436015
                  c.or        a3, a3
                  c.addi16sp  sp, 32
                  c.srai      a3, 6
                  xor         s8, t0, a1
                  sltu        s0, s4, s8
                  c.sub       a3, a3
                  add         zero, s10, s7
                  add         a4, s7, t6
                  xor         ra, zero, s6
                  c.or        a3, a3
                  auipc       sp, 766284
                  c.addi16sp  sp, 432
                  c.sub       a3, a3
                  or          t2, s11, tp
                  slti        a1, t2, 1284
                  c.li        s0, 7
                  c.nop
                  c.addi16sp  sp, -16
                  srl         s8, s6, tp
                  sltiu       a7, a1, 295
                  c.slli      a5, 29
                  mulhu       s2, ra, a2
                  slti        a6, t6, -1529
                  c.sub       a0, a3
                  mul         a4, ra, s11
                  sltu        gp, s0, s3
                  lui         zero, 1014011
                  c.nop
                  c.xor       a5, a3
                  addi        a4, a5, 1791
                  sra         s1, s4, s7
                  sub         s9, s2, sp
                  or          t1, t6, s1
                  c.li        s5, 25
                  addi        a7, s4, 265
                  or          s4, s6, a1
                  srli        s1, s11, 7
                  addi        a5, a3, -1549
                  mulhu       s5, sp, t4
                  c.srai      a4, 28
                  c.or        a3, a5
                  c.addi      ra, 16
                  c.mv        a4, a6
                  auipc       s9, 590029
                  c.li        t4, -1
                  slti        s10, tp, 1266
                  c.and       a3, a3
                  div         ra, gp, s10
                  divu        a0, t6, s2
                  mulhsu      t2, s10, a1
                  c.srai      a3, 31
                  c.nop
                  addi        a2, tp, 350
                  slti        zero, s3, -952
                  srai        a0, a4, 28
                  mulhu       zero, t6, a2
                  andi        zero, t5, 991
                  c.lui       ra, 27
                  sra         a1, zero, s3
                  c.mv        sp, s1
                  c.addi4spn  a3, sp, 896
                  mul         s4, s9, a6
                  c.srli      a3, 27
                  xori        t3, a5, -1207
                  div         a5, t1, t2
                  rem         zero, a1, gp
                  mulhu       s1, sp, s7
                  c.li        s4, 25
                  c.addi4spn  s0, sp, 832
                  c.addi16sp  sp, 320
                  srai        a5, a6, 26
                  c.xor       a1, a3
                  andi        s6, zero, -579
                  srl         a4, t0, t0
                  c.xor       a3, a1
                  c.or        a1, a3
                  and         a2, a4, a1
                  lui         zero, 1034224
                  c.and       a3, a3
                  c.andi      a0, -1
                  c.xor       a0, a5
                  and         zero, t0, gp
                  slti        s10, a0, -1659
                  mulhu       zero, a1, s7
                  auipc       s0, 745270
                  c.addi      s0, -1
                  srl         tp, a5, s4
                  rem         zero, s4, t1
                  c.sub       a2, a3
                  sra         zero, s2, t5
                  xori        t1, t2, 2035
                  srl         s5, a2, a4
                  lui         gp, 983665
                  c.lui       ra, 31
                  mulhu       s0, a3, t0
                  or          zero, s11, a2
                  c.addi4spn  a3, sp, 128
                  sltiu       sp, s10, 898
                  andi        t2, s8, -553
                  c.and       a0, a3
                  slti        t3, s9, -1660
                  c.and       a3, a4
                  c.addi4spn  a3, sp, 320
                  add         t3, s9, s10
                  c.sub       a3, a3
                  nop
                  srai        a4, t6, 14
                  c.li        t0, 8
                  c.addi      ra, 8
                  sra         zero, a5, a0
                  c.xor       a3, a3
                  nop
                  c.lui       s3, 25
                  srl         t4, a3, sp
                  andi        zero, a2, -689
                  slli        a5, a4, 20
                  srli        s9, s5, 9
                  add         ra, t4, t3
                  add         sp, a5, s10
                  slli        a4, a5, 5
                  div         a3, t5, s9
                  slt         s5, s4, s4
                  mulhsu      s8, a3, t3
                  xori        s2, tp, -2046
                  sra         gp, a4, sp
                  mul         a3, s11, t3
                  rem         s3, s7, a0
                  srl         a2, zero, a6
                  nop
                  sltiu       zero, sp, -1523
                  ori         a5, a4, -690
                  c.slli      a6, 23
                  sub         a7, s8, ra
                  xori        s0, s9, -1669
                  slli        s0, s5, 11
                  c.and       a3, a3
                  or          gp, s5, s1
                  nop
                  ori         s10, s2, -1689
                  srli        a5, a3, 23
                  sltu        zero, a5, ra
                  sltiu       a7, a0, 282
                  slti        t3, s1, -364
                  and         tp, ra, s0
                  lui         a6, 494436
                  c.and       a3, a3
                  c.slli      sp, 6
                  div         a5, sp, s5
                  c.lui       s10, 24
                  c.and       a3, a3
                  mulh        tp, t6, t5
                  mulh        tp, gp, s10
                  div         s6, a6, a1
                  slli        gp, a6, 29
                  divu        s5, s1, a3
                  slt         s2, ra, s4
                  srai        s3, a0, 24
                  sra         s1, s11, s1
                  andi        t3, t0, -777
                  or          s6, a4, a3
                  c.nop
                  xor         gp, t1, s3
                  nop
                  c.xor       a3, a3
                  c.srai      a0, 12
                  c.addi      s7, -1
                  nop
                  mulh        t0, t1, t0
                  and         s1, a1, t6
                  c.or        a1, a3
                  sltiu       zero, s4, 1254
                  sra         a1, t3, s4
                  sltu        a1, s2, s11
                  sltiu       t4, gp, 1199
                  mul         zero, a3, s9
                  c.and       a3, a3
                  c.srli      a3, 13
                  addi        a0, s2, 335
                  rem         t0, s0, s1
                  c.addi      a2, -1
                  addi        ra, a0, 1640
                  c.lui       t0, 10
                  or          zero, sp, s6
                  srli        a7, s2, 16
                  addi        a0, s8, 930
                  divu        s0, a5, tp
                  c.li        s6, -1
                  c.li        ra, -1
                  rem         a7, t2, zero
                  divu        s5, s0, s4
                  srl         a0, s5, tp
                  c.srli      a3, 3
                  nop
                  c.addi16sp  sp, 144
                  c.addi4spn  a3, sp, 64
                  c.srai      a3, 14
                  c.xor       a2, a3
                  sub         ra, s9, gp
                  mulhu       t4, t3, s5
                  sltiu       a1, t5, 840
                  sra         t4, s1, a0
                  slli        a2, t0, 30
                  andi        zero, zero, 822
                  add         s0, t0, a3
                  addi        s5, s4, -1325
                  addi        zero, s9, 384
                  c.nop
                  auipc       t0, 837335
                  c.li        sp, 7
                  c.mv        a0, a5
                  lui         a4, 843626
                  c.addi16sp  sp, 224
                  c.andi      a3, -1
                  xor         s2, s5, s0
                  slli        t1, t4, 6
                  srli        s1, t2, 13
                  divu        s10, t3, s6
                  c.add       sp, t1
                  or          t2, s10, zero
                  srai        t0, t0, 29
                  c.addi16sp  sp, -16
                  c.addi16sp  sp, 368
                  add         s1, t6, s10
                  mul         s7, t6, s5
                  c.add       s7, t1
                  nop
                  c.xor       a2, a3
                  or          s8, s10, t2
                  slt         s2, s4, t4
                  srai        tp, t0, 3
                  c.srai      a3, 25
                  c.srli      a3, 6
                  sltu        t0, s8, s11
                  andi        a5, s5, 587
                  c.srli      a3, 13
                  add         s2, t2, tp
                  mul         s8, s4, t2
                  c.srli      a3, 6
                  c.srli      a1, 28
                  addi        ra, a4, -1986
                  slti        zero, s11, 402
                  slti        a2, s5, 457
                  c.xor       a2, a3
                  sltu        zero, gp, t1
                  c.srli      a4, 28
                  c.srai      a3, 16
                  srai        s6, a1, 18
                  xor         s6, t0, a5
                  c.li        a3, -1
                  c.mv        ra, a1
                  c.addi      tp, -1
                  divu        zero, s1, t0
                  sra         zero, t3, a4
                  sub         zero, s5, s6
                  c.nop
                  xor         a5, sp, t3
                  c.srai      a3, 8
                  c.srli      a5, 20
                  c.xor       a1, a3
                  mul         s6, s3, s5
                  xor         s0, sp, a5
                  c.and       a3, a3
                  mulh        s9, t4, a7
                  divu        zero, a6, s1
                  mulhsu      zero, a0, a4
                  c.andi      s0, -1
                  c.xor       a3, a3
                  c.addi16sp  sp, 224
                  xori        t1, a7, -844
                  and         zero, t5, a2
                  c.xor       a3, a3
                  and         s9, a0, a7
                  c.and       a3, a3
                  c.srai      a4, 14
                  or          s8, a4, gp
                  nop
                  c.nop
                  c.addi4spn  a3, sp, 640
                  xor         a2, tp, t2
                  c.addi16sp  sp, -16
                  c.xor       a0, s0
                  ori         ra, gp, 1721
                  andi        t2, a2, 453
                  c.add       t4, a3
                  c.srli      a3, 8
                  slti        zero, a3, -1969
                  c.add       a0, sp
                  mulhu       zero, a4, s4
                  and         s10, s1, t4
                  c.nop
                  c.add       ra, ra
                  or          zero, ra, s10
                  ori         a6, s10, -1073
                  sub         s1, t3, s3
                  c.and       a3, a3
                  c.addi      tp, -1
                  mulhu       zero, a4, a0
                  divu        a3, s7, t5
                  addi        s7, s9, -1038
                  c.lui       s6, 10
                  c.xor       a3, a3
                  sltiu       t0, a3, -1962
                  c.or        a3, a3
                  sltu        t3, t3, a7
                  lui         t4, 659865
                  c.slli      t1, 16
                  c.lui       gp, 16
                  slt         a1, a4, a5
                  srai        a5, s9, 11
                  srl         zero, s2, tp
                  slli        a5, s8, 2
                  c.andi      a3, -1
                  srai        t4, a5, 21
                  div         t2, s7, sp
                  div         a6, t0, a0
                  addi        a7, s4, 2012
                  lui         ra, 669817
                  sltu        s10, t2, t2
                  auipc       t3, 862288
                  divu        a0, tp, a5
                  srl         a5, s4, tp
                  c.addi16sp  sp, -16
                  slti        a1, a0, -857
                  add         s6, s3, gp
                  slti        s7, ra, 709
                  srli        s9, s11, 12
                  sra         ra, s1, t1
                  rem         zero, s4, t1
                  mulh        s6, s8, s4
                  xori        s10, s7, 972
                  auipc       s3, 859016
                  c.sub       a3, s1
                  rem         zero, s1, s8
                  mulhsu      s10, a6, t1
                  c.addi4spn  a3, sp, 496
                  slti        t3, a0, 1893
                  c.slli      ra, 4
                  xori        a1, s8, -1930
                  c.andi      s0, -1
                  lui         s8, 743166
                  or          sp, zero, t2
                  c.sub       a3, a3
                  c.li        s3, -1
                  mulhsu      tp, s1, a4
                  slti        a1, a3, -1943
                  c.srli      a3, 21
                  slti        a6, t0, 1397
                  sltu        s5, ra, s11
                  c.addi4spn  a4, sp, 608
                  c.mv        a7, s2
                  c.lui       s2, 26
                  sll         a2, t6, t1
                  sltu        t3, t0, a4
                  c.nop
                  mulhsu      zero, a6, a1
                  c.srai      a3, 3
                  divu        s2, s6, t4
                  c.mv        ra, t5
                  c.li        sp, -1
                  add         s6, s6, a7
                  div         s7, t0, a4
                  mulh        s6, t3, t6
                  c.srli      a3, 26
                  c.add       s8, a3
                  srli        a4, s1, 13
                  nop
                  c.srli      a3, 21
                  c.xor       a3, a1
                  c.slli      s4, 1
                  ori         s9, a4, 897
                  c.addi16sp  sp, -16
                  andi        s6, tp, 1752
                  c.addi16sp  sp, -16
                  sltiu       ra, zero, 1861
                  ori         s6, a4, -1439
                  c.lui       a2, 22
                  c.srai      a3, 28
                  and         a7, a7, s9
                  c.andi      a4, 25
                  c.nop
                  srai        zero, s10, 10
                  mulhsu      s10, s3, t4
                  c.addi4spn  a1, sp, 416
                  c.sub       a3, s1
                  rem         t0, s9, s8
                  slti        a7, zero, 99
                  c.addi      t0, 27
                  divu        a7, a7, s8
                  c.addi16sp  sp, -16
                  c.andi      a3, -1
                  c.srli      s1, 29
                  slt         s0, s7, a4
                  c.srli      a2, 14
                  c.sub       a3, a3
                  or          t2, s6, t4
                  mulh        gp, a6, s7
                  mulhsu      tp, t4, a5
                  srl         t3, a1, s10
                  c.or        a3, a3
                  divu        s1, a1, s0
                  or          tp, t6, t5
                  div         t3, s5, s2
                  sll         zero, s2, t4
                  auipc       a3, 666677
                  mulhu       a2, s3, a7
                  sra         zero, s3, a1
                  lui         s3, 162235
                  c.srai      a3, 20
                  auipc       s9, 994713
                  c.srli      a3, 24
                  li         t3, 0x0 #start riscv_int_numeric_corner_stream_18
                  li         gp, 0x0
                  li         s8, 0x1
                  li         s10, 0x0
                  li         s9, 0x0
                  li         a2, 0x0
                  li         s1, 0x0
                  li         s3, 0x418f8dfe
                  li         s0, 0x1
                  li         t4, 0x2320f95b
                  c.addi      gp, 24
                  c.addi16sp  sp, -16
                  add         s3, s4, s9
                  mulhsu      zero, a6, a1
                  c.addi16sp  sp, 112
                  mulhsu      s8, a6, a5
                  auipc       sp, 963829
                  mul         zero, s11, a1
                  c.add       a4, ra
                  c.addi16sp  sp, 224
                  mulhu       a2, ra, s8
                  c.sub       a3, a3
                  c.li        s3, 18
                  c.lui       a4, 13
                  c.addi4spn  a4, sp, 560
                  c.lui       a7, 12
                  c.nop
                  sub         zero, a2, a0
                  c.add       sp, s4
                  mul         a4, gp, a6
                  addi        s7, s6, -1470
                  rem         t0, ra, s5
                  c.addi4spn  a0, sp, 608
                  c.addi      a4, -1
                  mul         t1, s1, zero
                  sub         s6, s8, t5
                  nop
                  sub         a6, sp, s1 #end riscv_int_numeric_corner_stream_18
                  div         a1, t6, sp
                  andi        s9, s3, 148
                  c.or        s0, a3
                  c.addi      s7, 21
                  c.xor       a3, s0
                  c.srli      a3, 29
                  mulh        a3, t4, t5
                  divu        s8, gp, a3
                  c.srai      a3, 1
                  c.addi16sp  sp, -16
                  nop
                  xor         t2, s9, ra
                  nop
                  c.srli      a3, 29
                  xor         s0, tp, t1
                  c.srai      a3, 11
                  slli        tp, tp, 28
                  c.xor       a3, a3
                  div         t2, ra, sp
                  or          s10, a6, s8
                  c.or        a3, s1
                  auipc       t0, 642871
                  c.srli      a3, 24
                  c.mv        s3, a3
                  c.xor       a3, a3
                  c.or        a2, a3
                  c.andi      a3, -1
                  c.lui       t0, 27
                  c.or        s0, a3
                  srl         gp, tp, s2
                  c.sub       a3, a3
                  andi        a1, s8, 380
                  c.srai      a3, 27
                  sra         s3, tp, s5
                  srli        s4, a4, 16
                  xor         s1, a5, a6
                  slt         s5, a6, t4
                  and         a7, a7, s11
                  srl         t3, s7, t1
                  xor         tp, t0, t2
                  c.addi      a3, -1
                  xori        s9, t1, -1288
                  slli        sp, t1, 3
                  sll         zero, s4, gp
                  c.or        s0, a2
                  mulhu       a0, t3, t2
                  srai        gp, a1, 13
                  c.mv        ra, a3
                  c.li        s4, -1
                  c.and       a2, a3
                  xor         a5, sp, a3
                  c.or        a3, a3
                  c.add       t0, tp
                  mulhsu      t4, t4, gp
                  c.srli      a1, 16
                  and         zero, a0, s5
                  c.xor       a3, s0
                  mulh        s5, t2, s7
                  or          t0, t4, zero
                  c.slli      ra, 14
                  divu        a6, gp, tp
                  rem         s1, t6, s3
                  lui         zero, 1041432
                  mul         t3, s1, t2
                  addi        zero, gp, 927
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
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_2:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_3:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_4:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_5:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_6:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_7:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_8:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_9:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_10:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_11:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_12:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_13:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_14:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_15:
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x342 # MCAUSE
                  srli x24, x24, 0x1f
                  beqz x24, 1f
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
                  csrrw x27, 0x340, x27
                  add x27, x30, zero
                  1: addi x27, x27, -124
                  sw x1, 4(x27)
                  sw x2, 8(x27)
                  sw x3, 12(x27)
                  sw x4, 16(x27)
                  sw x5, 20(x27)
                  sw x6, 24(x27)
                  sw x7, 28(x27)
                  sw x8, 32(x27)
                  sw x9, 36(x27)
                  sw x10, 40(x27)
                  sw x11, 44(x27)
                  sw x12, 48(x27)
                  sw x13, 52(x27)
                  sw x14, 56(x27)
                  sw x15, 60(x27)
                  sw x16, 64(x27)
                  sw x17, 68(x27)
                  sw x18, 72(x27)
                  sw x19, 76(x27)
                  sw x20, 80(x27)
                  sw x21, 84(x27)
                  sw x22, 88(x27)
                  sw x23, 92(x27)
                  sw x24, 96(x27)
                  sw x25, 100(x27)
                  sw x26, 104(x27)
                  sw x27, 108(x27)
                  sw x28, 112(x27)
                  sw x29, 116(x27)
                  sw x30, 120(x27)
                  sw x31, 124(x27)
                  csrr x24, 0x341 # MEPC
                  csrr x24, 0x342 # MCAUSE
                  li x29, 0xb # ECALL_MMODE
                  beq x24, x29, ecall_handler
                  li x29, 0x2 # ILLEGAL_INSTRUCTION
                  beq x24, x29, illegal_instr_handler
                  csrr x29, 0x343 # MTVAL
                  1: la x31, test_done
                  jalr x1, x31, 0

ecall_handler:    
                  la x24, _start
                  sw x0, 0(x24)
                  sw x1, 4(x24)
                  sw x2, 8(x24)
                  sw x3, 12(x24)
                  sw x4, 16(x24)
                  sw x5, 20(x24)
                  sw x6, 24(x24)
                  sw x7, 28(x24)
                  sw x8, 32(x24)
                  sw x9, 36(x24)
                  sw x10, 40(x24)
                  sw x11, 44(x24)
                  sw x12, 48(x24)
                  sw x13, 52(x24)
                  sw x14, 56(x24)
                  sw x15, 60(x24)
                  sw x16, 64(x24)
                  sw x17, 68(x24)
                  sw x18, 72(x24)
                  sw x19, 76(x24)
                  sw x20, 80(x24)
                  sw x21, 84(x24)
                  sw x22, 88(x24)
                  sw x23, 92(x24)
                  sw x24, 96(x24)
                  sw x25, 100(x24)
                  sw x26, 104(x24)
                  sw x27, 108(x24)
                  sw x28, 112(x24)
                  sw x29, 116(x24)
                  sw x30, 120(x24)
                  sw x31, 124(x24)
                  la x31, write_tohost
                  jalr x0, x31, 0

illegal_instr_handler:
                  csrr  x24, 0x341
                  addi  x24, x24, 4
                  csrw  0x341, x24
                  lw x1, 4(x27)
                  lw x2, 8(x27)
                  lw x3, 12(x27)
                  lw x4, 16(x27)
                  lw x5, 20(x27)
                  lw x6, 24(x27)
                  lw x7, 28(x27)
                  lw x8, 32(x27)
                  lw x9, 36(x27)
                  lw x10, 40(x27)
                  lw x11, 44(x27)
                  lw x12, 48(x27)
                  lw x13, 52(x27)
                  lw x14, 56(x27)
                  lw x15, 60(x27)
                  lw x16, 64(x27)
                  lw x17, 68(x27)
                  lw x18, 72(x27)
                  lw x19, 76(x27)
                  lw x20, 80(x27)
                  lw x21, 84(x27)
                  lw x22, 88(x27)
                  lw x23, 92(x27)
                  lw x24, 96(x27)
                  lw x25, 100(x27)
                  lw x26, 104(x27)
                  lw x27, 108(x27)
                  lw x28, 112(x27)
                  lw x29, 116(x27)
                  lw x30, 120(x27)
                  lw x31, 124(x27)
                  addi x27, x27, 124
                  add x30, x27, zero
                  csrrw x27, 0x340, x27
                  mret

pt_fault_handler: 

.align 2
mmode_intr_handler:
                  csrr  x24, 0x300 # MSTATUS;
                  csrr  x24, 0x304 # MIE;
                  csrr  x24, 0x344 # MIP;
                  csrrc x24, 0x344, x24 # MIP;
                  lw x1, 4(x27)
                  lw x2, 8(x27)
                  lw x3, 12(x27)
                  lw x4, 16(x27)
                  lw x5, 20(x27)
                  lw x6, 24(x27)
                  lw x7, 28(x27)
                  lw x8, 32(x27)
                  lw x9, 36(x27)
                  lw x10, 40(x27)
                  lw x11, 44(x27)
                  lw x12, 48(x27)
                  lw x13, 52(x27)
                  lw x14, 56(x27)
                  lw x15, 60(x27)
                  lw x16, 64(x27)
                  lw x17, 68(x27)
                  lw x18, 72(x27)
                  lw x19, 76(x27)
                  lw x20, 80(x27)
                  lw x21, 84(x27)
                  lw x22, 88(x27)
                  lw x23, 92(x27)
                  lw x24, 96(x27)
                  lw x25, 100(x27)
                  lw x26, 104(x27)
                  lw x27, 108(x27)
                  lw x28, 112(x27)
                  lw x29, 116(x27)
                  lw x30, 120(x27)
                  lw x31, 124(x27)
                  addi x27, x27, 124
                  add x30, x27, zero
                  csrrw x27, 0x340, x27
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
