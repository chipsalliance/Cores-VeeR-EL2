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
                  li x14, 0x40001104
                  csrw 0x301, x14
kernel_sp:        
                  la x22, kernel_stack_end

trap_vec_init:    
                  la x14, mtvec_handler
                  ori x14, x14, 1
                  csrw 0x305, x14 # MTVEC

mepc_setup:       
                  la x14, init
                  csrw 0x341, x14

init_machine_mode:
                  li x14, 0x1a00
                  csrw 0x300, x14 # MSTATUS
                  li x14, 0x0
                  csrw 0x304, x14 # MIE
                  mret
init:             
                  li x0, 0x7
                  li x1, 0x0
                  li x2, 0x0
                  li x3, 0x0
                  li x4, 0xf
                  li x5, 0xf3c47b58
                  li x6, 0x1
                  li x7, 0xf647876b
                  li x8, 0x80000000
                  li x9, 0xed79908d
                  li x10, 0x80000000
                  li x11, 0x80000000
                  li x12, 0x80000000
                  li x13, 0x80000000
                  li x14, 0xc
                  li x15, 0x0
                  li x16, 0xb0d23274
                  li x17, 0x80000000
                  li x18, 0x0
                  li x19, 0xf44a7d17
                  li x20, 0x9
                  li x21, 0xfe7efedc
                  li x23, 0x80000000
                  li x24, 0xc5a06f7b
                  li x25, 0x80000000
                  li x26, 0x1cc8d100
                  li x28, 0xfc2fbc3a
                  li x29, 0x0
                  li x30, 0x61560a9b
                  li x31, 0x80000000
                  la x27, user_stack_end
main:             li         t5, 0x0 #start riscv_int_numeric_corner_stream_7
                  li         t4, 0x0
                  li         t3, 0x1
                  li         s10, 0x0
                  li         s3, 0x1
                  li         s7, 0x0
                  li         a0, 0x1
                  li         t0, 0x0
                  li         s9, 0x1
                  li         s0, 0x1
                  mulhu       a0, s9, a1
                  div         ra, s7, t4
                  c.nop
                  divu        tp, t2, a3
                  rem         ra, t2, s3
                  c.addi16sp  sp, -16
                  lui         a6, 820675
                  divu        t2, a3, s2
                  c.lui       s3, 23
                  mul         s2, a2, a2
                  c.lui       tp, 21
                  addi        s8, s4, 232
                  mul         s2, a3, t0
                  rem         a5, tp, t1
                  rem         s9, a5, sp
                  c.sub       a3, a3
                  mul         a3, s5, t5
                  c.nop
                  c.mv        s8, s2
                  c.mv        tp, s6
                  auipc       t3, 44884
                  add         ra, t2, t5
                  add         a3, t5, s2
                  c.lui       s1, 31
                  c.li        t5, -1
                  c.addi4spn  a3, sp, 320
                  mulhsu      s4, tp, a5 #end riscv_int_numeric_corner_stream_7
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_8
                  li         s7, 0x68d6c105
                  li         a7, 0x1
                  li         t4, 0x0
                  li         s9, 0x0
                  li         t3, 0x56b3da3e
                  li         a3, 0x0
                  li         s1, 0x501e6511
                  li         a2, 0x1
                  li         s3, 0x0
                  rem         zero, s5, s3
                  c.li        ra, 29
                  c.mv        s5, s1
                  rem         t0, a2, t0
                  mulhu       tp, sp, t6
                  c.addi16sp  sp, 336
                  divu        t3, s1, s3
                  c.mv        s2, a4
                  mulhsu      s10, a1, s2
                  c.add       a1, t1
                  c.sub       a3, a1
                  div         zero, s4, tp
                  divu        s8, s4, a5
                  lui         s4, 502757
                  add         a4, zero, t1
                  lui         t1, 875532
                  addi        s7, a1, 732
                  add         ra, ra, a7
                  c.addi4spn  a3, sp, 896
                  mul         t1, s9, t0
                  sub         s3, s5, s7 #end riscv_int_numeric_corner_stream_8
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_11
                  li         s0, 0x0
                  li         t4, 0x0
                  li         t3, 0x0
                  li         s2, 0x0
                  li         s10, 0x0
                  li         a5, 0xe79da1b
                  li         sp, 0x1
                  li         t2, 0x1
                  li         a0, 0x2181c887
                  lui         zero, 1024233
                  c.addi      s3, -1
                  c.li        a7, -1
                  auipc       zero, 501836
                  auipc       s2, 956826
                  divu        a4, a7, s9
                  sub         t0, s2, s3
                  mul         ra, s7, s8
                  c.addi      ra, 4
                  c.addi4spn  s1, sp, 576
                  c.add       gp, a1
                  auipc       s7, 143451
                  divu        s2, s3, ra
                  c.addi4spn  a3, sp, 368
                  c.add       t3, s4
                  c.nop
                  c.addi4spn  a3, sp, 688
                  c.addi      ra, -1
                  c.add       t4, a2
                  c.add       a1, s0
                  c.addi4spn  a3, sp, 640
                  sub         ra, s1, t5
                  nop
                  sub         a5, s3, s9
                  c.add       sp, t3
                  rem         s2, t5, s11
                  c.addi4spn  a2, sp, 832
                  sub         zero, a3, t5
                  c.add       sp, a7
                  c.lui       ra, 11
                  li         a6, 0x0 #start riscv_int_numeric_corner_stream_4
                  li         a2, 0x28e7c2df
                  li         t5, 0x4264bde8
                  li         t0, 0x1
                  li         t4, 0x1
                  li         t3, 0x38b812d
                  li         a3, 0x4212e1ad
                  li         a4, 0x0
                  li         s9, 0x7250e349
                  li         a5, 0x0
                  lui         t3, 1023693
                  addi        a0, t3, -1997
                  c.nop
                  lui         t0, 51538
                  rem         s1, t5, a7
                  mul         a7, t2, zero
                  divu        a0, t2, t6
                  divu        t3, sp, s3
                  c.mv        sp, s2
                  mulhsu      ra, s9, s5
                  c.addi4spn  a3, sp, 448
                  c.li        t0, 27
                  mulhsu      s2, a2, t1
                  lui         a3, 945416
                  divu        s1, a4, t2
                  addi        s0, a0, 1514 #end riscv_int_numeric_corner_stream_4
                  li         gp, 0x5efed0d8 #start riscv_int_numeric_corner_stream_12
                  li         t5, 0x0
                  li         t4, 0x1
                  li         t3, 0x0
                  li         s10, 0x0
                  li         ra, 0x603d69a8
                  li         s9, 0x2344b9ea
                  li         s2, 0x0
                  li         s1, 0x77cea79
                  li         s8, 0x0
                  c.li        ra, -1
                  mulh        tp, s5, s1
                  mul         t5, s1, zero
                  c.addi      t4, -1
                  c.mv        ra, a1
                  rem         s1, s3, s10
                  c.addi16sp  sp, -16
                  c.li        t3, 25
                  c.lui       ra, 24
                  c.nop
                  c.add       s2, a2
                  lui         t2, 128957
                  lui         t0, 249006
                  c.mv        a2, a4
                  c.sub       a2, a4
                  c.mv        gp, t5
                  nop
                  lui         s9, 1034963
                  rem         a2, sp, zero
                  c.mv        ra, t6
                  div         s1, s4, gp
                  addi        s3, s7, 1791
                  auipc       zero, 321414
                  add         s8, a3, t5
                  c.add       a1, a1
                  mulh        tp, s5, gp
                  mulhu       ra, t3, s4 #end riscv_int_numeric_corner_stream_12
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_6
                  li         a6, 0x0
                  li         t4, 0x1
                  li         t3, 0x1
                  li         s1, 0x0
                  li         s9, 0x0
                  li         a5, 0x0
                  li         a2, 0x48148e66
                  li         sp, 0x0
                  li         a3, 0x0
                  c.addi      t0, -1
                  c.addi      a3, 22
                  mulh        s7, ra, tp
                  auipc       a4, 222328
                  c.li        t1, 24
                  c.nop
                  c.addi16sp  sp, -16
                  mul         a4, a0, s1
                  c.addi4spn  a3, sp, 128
                  lui         t4, 469233
                  c.addi4spn  a2, sp, 896
                  c.lui       gp, 6
                  c.lui       tp, 7
                  c.addi      s1, -1
                  c.addi16sp  sp, -16
                  c.addi4spn  a3, sp, 704
                  divu        s5, s9, s8
                  sub         a3, s11, t6
                  nop
                  mul         s4, s11, s7
                  divu        a2, a0, t6
                  mulh        ra, s7, s10
                  addi        t0, s3, -1096
                  auipc       sp, 667311
                  c.addi4spn  a5, sp, 896
                  c.addi      s0, -1
                  c.lui       s1, 13
                  lui         zero, 291240
                  c.mv        ra, a4
                  c.addi4spn  a2, sp, 960
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_13
                  li         t3, 0x0
                  li         s10, 0x0
                  li         s8, 0x0
                  li         t4, 0x75e288ca
                  li         s9, 0x1
                  li         a0, 0x0
                  li         s5, 0x0
                  li         a3, 0x1
                  li         a6, 0x1
                  div         s7, a7, t0
                  mul         a1, a6, tp
                  c.addi16sp  sp, -16
                  addi        t2, s3, 820
                  c.addi4spn  a3, sp, 832
                  nop
                  auipc       sp, 513736
                  c.li        s2, 31
                  c.nop
                  div         s5, a7, s3
                  lui         s1, 566821
                  sub         s7, a4, s2
                  div         t3, s3, s10
                  sub         sp, t1, t6
                  nop
                  c.lui       s10, 28
                  c.lui       s0, 25
                  sub         a7, t0, t3
                  div         zero, gp, a5 #end riscv_int_numeric_corner_stream_13
                  divu        tp, s6, s0
                  c.add       t2, t6
                  xori        s1, t4, -313
                  mulhsu      s2, a2, t5
                  sltiu       a6, s9, 1644
                  mulhsu      t0, ra, t1
                  sra         s8, a3, t6
                  div         zero, a0, tp
                  or          s5, ra, t4
                  slt         a6, t0, t6
                  c.mv        a6, s8
                  c.srli      a3, 14
                  srli        t3, s2, 20
                  sub         a2, s7, t5
                  c.nop
                  andi        zero, tp, 1271
                  slt         t5, s11, t1
                  add         s0, s2, a4
                  c.xor       a3, a1
                  and         gp, a1, s11
                  c.srai      a3, 10
                  mul         ra, s0, a2
                  divu        tp, a5, s9
                  c.andi      a3, 3
                  sub         s3, a0, s9
                  and         s7, a2, s10
                  c.addi      s8, 1
                  c.addi4spn  s1, sp, 656
                  nop
                  c.lui       s10, 23
                  ori         sp, a4, 702
                  mulh        s10, s2, a7
                  sltu        s7, t4, s10
                  c.mv        s2, a1
                  c.srai      a2, 28
                  c.xor       s1, a3
                  sub         ra, s10, s8
                  srli        s10, s1, 23
                  andi        s9, a6, 732
                  divu        zero, s8, sp
                  mulhu       t0, t0, s1
                  sltu        tp, sp, s0
                  c.sub       a3, a3
                  xori        s5, sp, -337
                  c.addi4spn  a3, sp, 896
                  sra         zero, s6, s5
                  c.sub       a3, a3
                  c.mv        t3, t3
                  mulhsu      s2, s5, t5
                  xori        ra, a3, 1480
                  c.slli      s10, 18
                  slti        s2, s8, -1801
                  sll         s2, t6, s4
                  sra         s4, s2, s3
                  mul         t5, t6, a0
                  mul         a3, t6, s7
                  div         zero, a2, a5
                  c.addi4spn  a0, sp, 576
                  srai        tp, t3, 26
                  mulhu       gp, a2, a2
                  c.lui       a7, 5
                  sltiu       s0, zero, -458
                  sll         s3, zero, a4
                  div         zero, zero, a7
                  xor         s5, t2, t0
                  c.andi      s1, 19
                  xor         a2, a2, zero
                  mulhsu      zero, s11, a4
                  srl         tp, a2, s7
                  c.lui       a5, 5
                  c.addi      ra, -1
                  lui         tp, 193427
                  slt         a3, s1, s9
                  ori         s2, s2, 1047
                  sra         zero, a1, s3
                  srai        gp, t1, 6
                  mulhu       ra, a1, t6
                  slt         t5, s6, s10
                  xori        s9, a0, -1229
                  add         a3, zero, tp
                  slt         a0, t0, a1
                  c.nop
                  srl         a7, s9, a0
                  nop
                  lui         a5, 176605
                  c.or        a3, a5
                  mulhu       s5, t2, a0
                  c.add       sp, s6
                  mul         s0, t0, a2
                  sltiu       s9, s4, 1086
                  c.li        a4, -1
                  c.srli      a3, 14
                  srli        a7, s1, 21
                  c.andi      a3, 3
                  c.nop
                  sltu        zero, a0, t1
                  c.addi4spn  a3, sp, 320
                  c.sub       a2, a3
                  slt         a5, a5, t2
                  divu        s10, s11, gp
                  c.or        a3, a1
                  xori        t3, t6, -820
                  slli        t0, s9, 18
                  srli        zero, a5, 12
                  c.xor       a3, a3
                  nop
                  rem         s8, zero, s1
                  ori         t1, s11, -1561
                  and         s4, t5, s8
                  srai        zero, a6, 1
                  c.li        ra, 16
                  divu        sp, gp, s5
                  sub         a4, s11, a2
                  c.lui       ra, 30
                  c.srli      a4, 25
                  c.andi      a3, 25
                  c.srai      a3, 25
                  add         s5, a5, t4
                  addi        t2, s0, -633
                  srl         t1, t0, t4
                  c.li        a0, 5
                  or          a4, sp, a4
                  auipc       s10, 460709
                  sltiu       a0, a0, 1052
                  ori         a5, s2, 1052
                  ori         t0, s2, -942
                  mul         a2, s6, a3
                  srai        t2, s9, 0
                  sltu        a3, t2, t0
                  nop
                  sra         t1, t6, s2
                  srl         a4, t4, a2
                  c.xor       s0, s1
                  mul         zero, t1, s5
                  c.srai      a3, 6
                  nop
                  andi        a5, a4, -710
                  or          a3, s1, s9
                  mulhsu      s10, t1, a6
                  slti        t2, s9, -1651
                  c.add       s0, t0
                  mulh        a5, s8, a4
                  sltu        a6, a2, s3
                  c.slli      t0, 5
                  c.slli      ra, 2
                  div         t0, s10, t2
                  c.addi4spn  a3, sp, 384
                  divu        a0, s3, s9
                  sltu        a3, t5, a1
                  c.or        a3, a3
                  sltiu       a4, a3, 990
                  srai        t2, s11, 31
                  slli        a7, a2, 7
                  xor         t5, t1, a4
                  auipc       s3, 114682
                  slt         s2, s3, a4
                  c.andi      a3, 19
                  c.nop
                  slli        a5, a5, 1
                  lui         gp, 802675
                  slli        s10, a4, 23
                  c.lui       a7, 8
                  mulhsu      t1, s11, a6
                  c.mv        sp, t4
                  c.addi      s0, 23
                  slti        t3, t1, -1818
                  slt         zero, a1, t3
                  mulhu       s8, zero, a5
                  c.xor       a3, a3
                  lui         tp, 98840
                  sra         a1, s9, tp
                  or          s9, a1, s3
                  sra         s8, s2, s2
                  c.addi16sp  sp, 480
                  c.li        t3, 15
                  c.lui       t5, 6
                  slt         sp, a3, s1
                  c.srli      a3, 2
                  xor         ra, s1, s0
                  slti        t2, s3, 288
                  c.li        s7, 4
                  sltu        t1, t2, a2
                  auipc       a7, 579335
                  auipc       zero, 275202
                  xor         t4, a6, s0
                  srl         a1, t5, s3
                  c.and       a2, a3
                  c.mv        s1, a3
                  mulhsu      s9, s1, s8
                  sra         t4, s3, a3
                  c.addi4spn  a3, sp, 32
                  c.addi16sp  sp, -16
                  srl         gp, s4, tp
                  lui         ra, 741201
                  c.addi      ra, 5
                  c.srli      a0, 31
                  c.addi      s2, 30
                  or          a3, s2, t2
                  c.li        t5, -1
                  c.srli      a3, 30
                  slt         zero, sp, t6
                  c.mv        s4, a3
                  rem         ra, a2, t2
                  c.addi      t1, -1
                  divu        a6, tp, s11
                  li         t5, 0x3235f3ac #start riscv_int_numeric_corner_stream_9
                  li         t4, 0x2880b24c
                  li         t3, 0x0
                  li         t2, 0x1
                  li         s5, 0x0
                  li         a2, 0x47cdbcf1
                  li         a3, 0x0
                  li         s8, 0x0
                  li         tp, 0x2bfc2dee
                  li         s7, 0x0
                  c.addi16sp  sp, 448
                  c.addi4spn  a3, sp, 608
                  nop
                  add         zero, t2, s4
                  c.sub       a3, a3
                  mulhu       a5, s8, a5
                  sub         a0, a7, a6
                  c.sub       s1, a3
                  c.mv        s7, a3
                  c.add       ra, ra
                  c.lui       t2, 20
                  c.li        tp, -1
                  div         a1, t0, s0
                  c.addi4spn  a3, sp, 960
                  c.addi4spn  a3, sp, 576
                  mulh        t4, s11, a5
                  nop
                  div         a3, s2, s1
                  mulhu       a0, a3, a7
                  auipc       t5, 299527
                  add         s8, s7, s0 #end riscv_int_numeric_corner_stream_9
                  mulh        s8, a5, t3
                  srl         zero, sp, tp
                  c.slli      s9, 14
                  nop
                  addi        zero, gp, -438
                  div         s10, s1, s1
                  sll         a6, s5, t3
                  c.xor       a3, a3
                  add         s4, a7, a5
                  mul         sp, s10, s7
                  sltiu       zero, t5, -626
                  rem         s1, tp, a4
                  add         t2, a2, sp
                  c.lui       a7, 15
                  slli        t1, zero, 9
                  divu        zero, s11, t5
                  mulhu       s3, a4, gp
                  auipc       s2, 840177
                  c.slli      s5, 18
                  div         t0, ra, t6
                  divu        sp, s9, a3
                  xori        t0, t0, -1579
                  c.slli      s7, 21
                  sra         s0, s5, a0
                  lui         a3, 751833
                  srl         t2, tp, ra
                  c.and       a3, a3
                  srai        t3, t3, 28
                  addi        zero, a1, -1324
                  c.addi16sp  sp, 32
                  ori         t0, s10, 1042
                  c.and       a5, a3
                  slt         s10, a1, a5
                  auipc       a0, 345943
                  xor         gp, t6, s4
                  srli        ra, s11, 13
                  addi        ra, s10, 1746
                  srai        a4, s10, 22
                  mulhsu      s9, zero, s8
                  slli        s8, a0, 23
                  srli        s3, ra, 12
                  c.add       t4, t0
                  c.mv        ra, a0
                  div         a7, gp, a7
                  c.addi4spn  a0, sp, 944
                  lui         sp, 542476
                  c.xor       a2, a1
                  sltiu       a3, a1, -1712
                  sub         a2, a6, t5
                  slli        s10, t2, 12
                  add         s10, ra, t4
                  xori        t2, s5, -279
                  sll         s3, a3, zero
                  and         t4, a0, t1
                  srli        a4, a1, 23
                  c.slli      t0, 13
                  nop
                  c.addi4spn  a0, sp, 192
                  srli        a4, a5, 15
                  c.li        s4, 4
                  divu        sp, s11, s5
                  srai        s5, s10, 29
                  c.and       a3, a3
                  add         t2, t5, s9
                  srai        tp, t6, 14
                  slti        gp, a3, 2007
                  sra         t2, sp, ra
                  c.and       a3, a5
                  addi        s9, a2, 1767
                  c.add       a0, s10
                  c.and       s1, a3
                  c.xor       a3, a3
                  c.srli      a3, 1
                  srl         t2, zero, t3
                  slli        a1, s6, 23
                  mulhsu      a1, a5, gp
                  c.lui       t2, 17
                  ori         s7, ra, -670
                  c.li        s8, 20
                  sltiu       gp, s8, -977
                  c.lui       tp, 21
                  c.add       sp, s1
                  mul         s7, a6, a7
                  sltu        sp, a1, a5
                  sra         a4, s1, t5
                  rem         t3, s11, a5
                  c.add       s8, t0
                  sltu        s4, s4, a4
                  c.add       s9, tp
                  c.li        a2, 29
                  c.slli      ra, 29
                  srl         s9, t1, s10
                  c.nop
                  slt         sp, a3, s10
                  srai        zero, s7, 9
                  and         a6, t6, s10
                  c.addi4spn  s1, sp, 224
                  mul         t0, s11, a6
                  c.srai      a3, 18
                  c.andi      a3, -1
                  andi        s8, s8, 1826
                  c.mv        s9, a4
                  c.sub       a3, a3
                  c.sub       a3, a3
                  rem         a0, a4, a6
                  c.andi      a3, -1
                  c.sub       a3, a3
                  c.srai      s1, 18
                  mulh        s3, t2, t3
                  c.sub       a3, a3
                  xor         ra, s0, gp
                  slti        t5, a5, -729
                  ori         s10, t4, -671
                  srl         s5, t4, a4
                  c.srli      s0, 27
                  c.addi16sp  sp, -16
                  srli        s7, s10, 16
                  c.add       sp, s9
                  slli        s0, t6, 24
                  c.nop
                  rem         t2, t4, s3
                  c.and       a3, a3
                  sltu        a7, s6, gp
                  add         s8, zero, a3
                  xor         t4, a6, a2
                  c.mv        a2, tp
                  c.addi16sp  sp, -16
                  sltu        s3, tp, s1
                  mulh        t5, s3, ra
                  sll         t2, a2, a5
                  xori        zero, a4, 1306
                  mul         s10, a3, a3
                  slt         tp, tp, s7
                  and         t2, t1, s1
                  auipc       s4, 342264
                  mul         s9, t6, t2
                  add         s7, s1, a1
                  slti        ra, s8, 1622
                  mul         s7, s7, ra
                  c.lui       s10, 6
                  sltiu       a2, s6, -1176
                  slli        s5, t0, 28
                  c.andi      a3, 12
                  mulh        a2, zero, t0
                  c.addi      s8, 22
                  rem         s9, a1, a7
                  c.addi      ra, 21
                  xori        t3, s1, 155
                  slti        zero, s11, 1560
                  srl         zero, a5, a3
                  ori         s9, s1, -1508
                  c.xor       a3, a3
                  c.andi      a3, -1
                  mulhu       a6, gp, a4
                  divu        ra, ra, s7
                  addi        s2, sp, 1063
                  mul         s1, a2, t0
                  addi        t0, s5, 815
                  sltiu       zero, a7, 1636
                  nop
                  andi        ra, a5, -893
                  slt         s9, zero, a2
                  addi        s1, a5, 1970
                  divu        t1, zero, s5
                  or          s10, s0, a7
                  and         a5, s8, t4
                  mulhsu      zero, s2, s4
                  sltu        s0, s10, s3
                  lui         zero, 433490
                  srai        t2, t5, 31
                  c.addi16sp  sp, 96
                  c.addi      s9, 26
                  mulhsu      a2, a2, t6
                  div         a2, a0, a3
                  slti        zero, a2, -1113
                  addi        a1, a1, -1109
                  andi        s0, a6, 1720
                  srl         s8, t5, s1
                  c.add       a5, t2
                  mulh        s8, a0, s6
                  mulh        s10, t5, a1
                  sll         zero, s6, s11
                  c.add       a4, a0
                  nop
                  slt         t2, a7, t2
                  slti        t0, a6, -1061
                  c.add       sp, t6
                  c.srai      a3, 4
                  c.xor       a3, a3
                  c.add       t1, s0
                  andi        ra, a3, 1418
                  c.slli      t0, 13
                  mulhsu      a2, t2, zero
                  or          a4, s8, s8
                  c.and       a3, a3
                  auipc       a1, 870363
                  sub         t3, a2, a4
                  xori        s4, s6, -532
                  sltu        s1, s8, s0
                  c.addi4spn  a3, sp, 320
                  slli        a0, s9, 31
                  sltiu       t0, a6, 300
                  slli        t0, ra, 6
                  c.sub       a3, a3
                  c.addi4spn  a3, sp, 608
                  divu        s4, a2, t0
                  c.add       s9, t2
                  c.sub       a3, a3
                  c.xor       a3, a3
                  slli        a2, s5, 27
                  slli        s1, a3, 26
                  srli        ra, t5, 31
                  c.srai      a3, 14
                  srai        t1, s1, 27
                  nop
                  sra         s1, s2, s8
                  c.lui       s8, 1
                  addi        s5, s1, -1261
                  sub         a0, t0, gp
                  c.nop
                  c.slli      a2, 2
                  auipc       zero, 668658
                  c.and       a3, s0
                  and         a2, gp, t0
                  c.slli      ra, 4
                  div         tp, s8, a7
                  c.mv        s0, t2
                  div         t1, sp, t4
                  c.sub       a3, s1
                  lui         t2, 377072
                  sll         zero, sp, a0
                  c.addi4spn  a3, sp, 832
                  c.srli      a1, 16
                  c.or        a2, a3
                  mul         t3, s5, s5
                  mulhu       s9, t3, sp
                  mul         ra, t2, s4
                  addi        s3, t6, 174
                  srli        s2, s9, 8
                  mulh        s5, tp, a3
                  c.lui       ra, 30
                  c.srli      a3, 20
                  c.addi4spn  a3, sp, 896
                  c.add       t0, t3
                  auipc       s8, 794599
                  addi        a0, a6, 907
                  c.mv        tp, sp
                  c.or        a3, a3
                  sltu        t0, a4, a5
                  c.srli      a4, 7
                  div         s9, tp, s4
                  rem         a5, s9, s0
                  srl         s5, t3, t4
                  divu        zero, a5, s11
                  xor         a0, zero, a6
                  mulh        t5, s2, s3
                  c.nop
                  xori        s5, s0, -113
                  c.slli      s8, 16
                  c.srli      a3, 15
                  c.or        a3, a3
                  c.add       ra, a6
                  sltu        a2, s8, s7
                  c.lui       tp, 1
                  sltiu       s7, s9, 1241
                  sll         s3, a5, s9
                  c.xor       a3, a3
                  xor         s5, s6, s5
                  sltiu       zero, s6, -713
                  ori         a0, s8, -1215
                  c.and       a3, a3
                  c.andi      a5, -1
                  srai        a1, t6, 21
                  and         zero, s0, a2
                  c.sub       a3, a3
                  srl         zero, s2, s3
                  c.and       a3, a3
                  mulhu       t4, ra, sp
                  c.and       a3, a1
                  mul         a1, s0, a3
                  c.addi4spn  a5, sp, 208
                  c.and       a3, a3
                  c.slli      t1, 6
                  xor         t3, a6, gp
                  div         tp, a0, t3
                  mul         t4, s10, t0
                  c.andi      a3, 26
                  c.and       a3, a2
                  nop
                  sltiu       a0, t0, 728
                  srli        t4, sp, 9
                  c.srai      a3, 30
                  slti        a6, s7, 1342
                  c.sub       a3, a3
                  mulh        zero, t4, zero
                  srl         t2, t3, t2
                  c.srli      a3, 19
                  div         s7, t5, tp
                  sltu        gp, t6, t0
                  mulhsu      s0, t2, a5
                  c.li        s4, 2
                  mul         zero, a6, t3
                  nop
                  c.add       a5, t4
                  lui         a4, 644432
                  c.sub       a3, a3
                  add         a3, gp, t6
                  xori        s1, s4, -43
                  c.andi      a1, -1
                  sll         a2, s5, t2
                  c.andi      a3, -1
                  mulhsu      zero, s9, a5
                  sra         s1, s11, s4
                  c.andi      a3, -1
                  c.lui       a4, 13
                  div         t5, a4, a6
                  c.xor       a3, s1
                  andi        zero, a6, -1213
                  srli        s7, t3, 16
                  slli        tp, t0, 8
                  slli        s3, s4, 4
                  sltiu       s9, t0, 398
                  c.add       tp, s11
                  and         sp, t1, t1
                  srl         zero, sp, s6
                  divu        a0, sp, s1
                  c.and       a3, a3
                  auipc       tp, 196788
                  c.slli      s8, 8
                  xori        s7, s1, 1640
                  xori        a2, s1, 296
                  c.andi      a3, 11
                  xori        s3, s8, 975
                  c.mv        ra, s6
                  sra         tp, a6, sp
                  and         s2, a5, s1
                  xori        zero, s4, 1872
                  rem         a4, a3, s0
                  c.xor       s1, a3
                  c.addi4spn  a3, sp, 128
                  slli        t5, a2, 12
                  c.and       a3, a3
                  c.li        t1, -1
                  slti        t0, a6, 738
                  and         s3, t5, t2
                  c.and       a2, a5
                  rem         t5, s3, sp
                  c.slli      t5, 10
                  c.xor       a1, s0
                  sll         s3, s5, ra
                  mulhsu      s1, t4, s0
                  mul         s2, tp, t4
                  srl         t5, a4, s4
                  mulh        t3, t2, s0
                  mul         a0, s4, s3
                  mulhsu      s4, t1, s7
                  c.addi16sp  sp, 80
                  or          s2, a3, s2
                  and         sp, s0, a3
                  c.or        a3, a3
                  srai        ra, s6, 8
                  divu        a0, a6, a2
                  c.sub       s0, a2
                  c.addi4spn  a3, sp, 80
                  and         s3, a4, s10
                  c.addi4spn  a0, sp, 384
                  c.mv        a4, s6
                  c.add       s7, a7
                  ori         a6, a1, 838
                  sub         zero, t5, s9
                  mul         s7, a3, a7
                  c.or        a3, s1
                  mulhsu      s1, a7, t4
                  mulhu       s4, s8, s0
                  add         a0, a4, ra
                  sll         sp, s5, t0
                  c.andi      a3, 20
                  c.addi      s2, 18
                  divu        a1, t5, s7
                  sltu        s9, ra, a2
                  c.lui       t1, 8
                  c.mv        ra, s2
                  sltu        s9, a5, s1
                  srl         zero, s2, t3
                  sltiu       a6, s7, 1207
                  addi        zero, zero, 1095
                  c.addi      s8, -1
                  c.add       t1, a1
                  c.srai      a3, 17
                  c.nop
                  sub         s0, t0, t6
                  c.addi      s1, -1
                  c.and       a3, a4
                  and         gp, t4, t5
                  rem         a6, t4, a2
                  srli        a4, s5, 31
                  sltu        t2, s7, zero
                  c.sub       a3, a2
                  divu        s4, t5, a1
                  mulh        zero, t2, ra
                  slti        t0, s8, 1831
                  or          t5, s11, t5
                  c.xor       a3, a3
                  lui         s7, 937402
                  sll         t1, t2, sp
                  c.and       a3, a3
                  srai        s2, s4, 12
                  c.or        a3, a3
                  lui         s1, 916335
                  c.add       a3, a3
                  xori        s2, a5, 1394
                  sll         a2, a0, sp
                  c.slli      sp, 29
                  srl         sp, s6, a4
                  addi        a0, s7, -118
                  c.lui       s3, 31
                  sub         t3, s6, s10
                  lui         a4, 953880
                  c.sub       a3, a3
                  c.srli      a3, 24
                  srli        s0, tp, 27
                  mulh        tp, t0, a3
                  srli        zero, s2, 7
                  addi        s8, s4, 834
                  sltiu       a7, gp, -430
                  mulhsu      a2, s9, t0
                  c.srli      a3, 2
                  addi        sp, t3, -1776
                  srai        s3, a1, 8
                  c.srai      a3, 18
                  xor         gp, s8, a2
                  and         a4, s3, s10
                  c.andi      a3, -1
                  c.li        t5, 9
                  slt         s9, a7, s9
                  c.li        s10, 21
                  slt         tp, tp, zero
                  div         a2, a1, t1
                  c.srai      a4, 15
                  c.addi16sp  sp, 400
                  mulhsu      s2, tp, t4
                  c.and       a1, a2
                  c.lui       t3, 29
                  sra         s8, s7, a0
                  sra         a0, s2, s8
                  srli        sp, s9, 23
                  c.xor       a5, a4
                  c.addi16sp  sp, 80
                  c.add       tp, s2
                  c.addi4spn  a3, sp, 128
                  divu        a0, s5, s8
                  c.or        a3, s0
                  sltiu       sp, a0, 938
                  add         zero, t3, s2
                  c.add       t3, t2
                  divu        t3, gp, tp
                  slt         t0, s8, a6
                  srli        t0, t6, 19
                  div         t2, a2, a2
                  rem         t5, s11, s4
                  sll         s8, s6, t4
                  add         zero, a3, a7
                  c.addi      t4, -1
                  sub         sp, s8, ra
                  ori         a7, a6, -2020
                  c.sub       a3, a3
                  ori         t1, s8, 1140
                  c.sub       a3, a3
                  c.mv        s2, t6
                  or          zero, a0, t0
                  nop
                  c.mv        s9, s8
                  c.addi4spn  a3, sp, 96
                  or          a0, t0, s3
                  c.sub       a3, a5
                  c.sub       a3, a3
                  sltiu       s7, ra, 1455
                  c.sub       a0, a3
                  rem         s2, t3, a6
                  c.or        a3, a3
                  or          t3, s1, s2
                  xor         a5, s9, t4
                  c.andi      a3, 27
                  c.slli      sp, 11
                  c.nop
                  c.mv        tp, t0
                  lui         s1, 715243
                  c.addi      t3, 9
                  sltu        a1, t4, s1
                  c.addi      s7, -1
                  c.li        t0, 31
                  mulhu       t4, s10, t6
                  div         s0, t4, s2
                  sll         zero, t4, s3
                  or          tp, s9, a6
                  addi        a0, s9, 1118
                  rem         ra, s10, gp
                  addi        s7, s0, -133
                  c.addi16sp  sp, 272
                  c.and       a3, a3
                  c.addi16sp  sp, 256
                  c.addi      sp, 13
                  c.srli      a3, 20
                  divu        t4, sp, s8
                  sub         t5, zero, tp
                  c.li        s5, 22
                  c.xor       a3, a3
                  c.and       a3, a3
                  srai        zero, t3, 29
                  c.addi4spn  a2, sp, 576
                  sll         a6, a5, t2
                  or          gp, a7, t0
                  srai        s9, a5, 18
                  srli        tp, s11, 26
                  mulhsu      tp, a6, s1
                  div         s5, s6, s8
                  xori        a0, a5, 2003
                  srli        t5, a4, 25
                  div         s1, s6, t6
                  or          zero, a3, a7
                  c.mv        t4, t5
                  slt         a1, s2, gp
                  addi        a6, a7, -399
                  c.slli      ra, 8
                  slt         s10, gp, s1
                  mulhu       tp, sp, s6
                  andi        s1, s4, -1367
                  sltu        zero, a6, a3
                  c.mv        sp, s4
                  xor         a2, a0, s7
                  c.and       a3, a3
                  rem         gp, t1, t0
                  srl         a1, s6, zero
                  slt         sp, gp, s6
                  lui         t0, 410214
                  div         a1, a5, t2
                  div         s4, ra, t1
                  slti        t4, a6, 1511
                  sltiu       s10, t5, -1305
                  srl         a4, s7, t1
                  c.addi4spn  a3, sp, 800
                  mul         a6, tp, t0
                  slti        sp, s9, 1033
                  slti        sp, s9, -1955
                  sltiu       a6, t5, -1317
                  divu        t4, a4, s9
                  c.addi16sp  sp, -16
                  c.slli      t4, 10
                  slli        a3, tp, 1
                  slt         s8, s9, tp
                  mul         s3, a1, tp
                  c.andi      a2, -1
                  srl         s7, a6, a0
                  slt         zero, a7, s0
                  sll         a3, s4, s6
                  c.addi4spn  a3, sp, 976
                  lui         a1, 603552
                  and         a2, t3, t3
                  ori         t2, s2, 1472
                  slt         sp, s10, s5
                  nop
                  slt         s8, s7, ra
                  mulhsu      a7, a0, a0
                  c.li        t4, -1
                  c.srai      a2, 30
                  div         a3, t4, t3
                  c.addi      s2, 19
                  c.srli      s1, 16
                  c.lui       ra, 16
                  mulhsu      zero, t1, s10
                  c.add       t4, s8
                  mulhsu      s8, t5, t3
                  c.or        a3, a3
                  c.sub       a3, s1
                  c.addi16sp  sp, -16
                  slli        t4, t4, 16
                  addi        zero, t3, -1091
                  c.andi      s1, -1
                  sltu        zero, a4, t4
                  rem         s5, t1, t4
                  mulhsu      zero, a3, t1
                  c.xor       a3, a3
                  c.lui       s4, 1
                  c.and       a3, a3
                  c.slli      a6, 21
                  li         t4, 0x1 #start riscv_int_numeric_corner_stream_0
                  li         s8, 0x0
                  li         s7, 0x1
                  li         t3, 0x0
                  li         s9, 0x0
                  li         a2, 0x1
                  li         t5, 0x0
                  li         a6, 0x1
                  li         s10, 0x0
                  li         a4, 0x0
                  rem         a5, a6, s2
                  c.addi4spn  a3, sp, 64
                  c.mv        s1, s3
                  div         zero, ra, t5
                  auipc       a5, 444420
                  c.nop
                  c.add       t1, a6
                  mulhu       a5, t1, a3
                  add         s8, t5, gp
                  auipc       s3, 746985
                  c.li        s5, 4
                  c.mv        ra, t6
                  divu        s4, t0, ra
                  mulhu       s0, s3, t2
                  auipc       s3, 1023425
                  c.nop
                  c.addi16sp  sp, -16
                  mulhsu      s1, a6, t0
                  c.nop
                  add         tp, s7, t0
                  c.addi      a1, 19
                  mul         tp, t1, t6
                  c.sub       a4, a3
                  sub         a0, a5, a3
                  c.sub       a1, s1
                  srli        sp, tp, 7
                  slti        zero, s9, 1634
                  mulhu       s8, a7, s8
                  c.add       s9, t0
                  divu        s8, a5, s9
                  c.addi16sp  sp, -16
                  xor         s0, zero, s5
                  and         t1, a1, t0
                  mulhu       a5, s8, t0
                  c.or        a3, a3
                  slti        a1, s2, -1326
                  c.srai      a3, 7
                  rem         zero, t0, t2
                  sub         s1, s11, a1
                  andi        t4, s11, -281
                  mulhu       s10, a1, t0
                  mul         a6, s6, a6
                  auipc       zero, 957150
                  sltu        zero, ra, s7
                  c.xor       a3, a3
                  sub         tp, s1, s11
                  or          a4, a3, a3
                  divu        zero, t0, a3
                  nop
                  rem         s9, gp, a1
                  rem         zero, a5, tp
                  c.and       a3, a5
                  c.sub       s0, a3
                  sll         s7, s6, a4
                  sra         sp, a3, s5
                  mulhsu      s4, a4, s5
                  slti        s3, a4, 1368
                  c.addi      t0, 25
                  sltu        gp, s8, t4
                  and         s7, ra, t6
                  mul         s8, ra, sp
                  slti        sp, t4, 1346
                  mul         sp, t1, a2
                  andi        s7, t6, 1920
                  c.li        s3, 24
                  ori         t2, t3, -1155
                  sub         zero, zero, s6
                  xori        zero, a2, 1319
                  sll         t3, gp, sp
                  c.or        a3, a3
                  c.sub       a3, a3
                  c.addi      a0, 11
                  c.mv        ra, tp
                  c.srai      a3, 1
                  mul         a7, s9, s10
                  div         zero, s3, a5
                  sltiu       zero, zero, -96
                  lui         a0, 203611
                  c.li        gp, 15
                  sltu        s8, s3, t3
                  mulh        s7, a3, s10
                  addi        s2, gp, -1991
                  and         s1, t3, t6
                  sub         s10, t2, a0
                  c.or        a0, s1
                  lui         zero, 676308
                  mulh        zero, s0, t2
                  c.addi4spn  a3, sp, 640
                  li         t4, 0x1 #start riscv_int_numeric_corner_stream_2
                  li         t3, 0x21f776ad
                  li         s4, 0x74931d0
                  li         s8, 0x0
                  li         s0, 0x0
                  li         t5, 0x0
                  li         a2, 0x0
                  li         s10, 0x0
                  li         a1, 0x0
                  li         a4, 0x1
                  c.lui       t4, 20
                  auipc       a3, 673912
                  mulhu       a7, s1, t1
                  c.add       ra, t3
                  rem         a0, s6, s1
                  nop
                  mulhu       zero, a6, s7
                  lui         zero, 582100
                  c.addi      gp, -1
                  c.addi      s7, -1
                  div         s5, s9, a5
                  c.li        gp, 18
                  sub         tp, sp, tp
                  rem         s0, t2, a1
                  nop
                  c.mv        a5, t2
                  div         t3, a4, a0
                  mulh        t0, s3, t1 #end riscv_int_numeric_corner_stream_2
                  sltu        a1, t4, gp
                  mul         a3, t1, s7
                  sltu        t4, s9, s6
                  sra         s0, tp, s5
                  c.slli      ra, 12
                  srai        s9, a4, 20
                  c.and       a3, a3
                  c.srli      a3, 31
                  c.addi16sp  sp, -16
                  c.xor       a3, a3
                  c.li        ra, 20
                  sltiu       s2, ra, -961
                  c.addi16sp  sp, -16
                  sltiu       s1, t5, -1384
                  c.srai      a2, 29
                  c.addi4spn  a3, sp, 896
                  addi        t2, a7, -2013
                  ori         zero, s5, -1190
                  sll         a1, s4, t5
                  nop
                  sltiu       s5, s11, 436
                  srai        s10, s3, 10
                  c.and       a3, a3
                  mulhsu      a3, t6, a1
                  slt         s7, a7, a2
                  c.addi16sp  sp, 272
                  sltiu       zero, s4, 1981
                  c.nop
                  c.lui       s8, 6
                  c.srai      a3, 11
                  srl         zero, s5, s6
                  slti        zero, t6, -222
                  add         t3, s7, a4
                  sltiu       t1, t1, -1559
                  div         a1, s9, sp
                  c.xor       a3, a1
                  c.andi      s0, -1
                  c.and       a3, a3
                  nop
                  or          zero, tp, t3
                  c.li        ra, -1
                  nop
                  xor         t3, s6, a7
                  andi        s10, s8, -578
                  sll         t1, t2, s1
                  xor         t3, t2, a2
                  c.add       a2, s11
                  sltu        a1, t2, s6
                  c.srai      a3, 13
                  c.add       a1, s0
                  c.or        a3, a3
                  nop
                  xori        s9, s6, -957
                  slli        s7, t4, 25
                  c.mv        a0, sp
                  c.srai      a3, 24
                  c.nop
                  mulhsu      s7, a5, sp
                  add         t4, t3, s9
                  div         s0, t3, s11
                  c.or        a3, a3
                  c.andi      a0, -1
                  c.xor       a4, a3
                  andi        t1, t4, -95
                  c.addi4spn  a3, sp, 608
                  sub         a3, s11, s8
                  lui         a2, 306789
                  divu        s3, s0, sp
                  mulhu       s7, s6, a0
                  andi        zero, s5, -1145
                  mul         s4, s1, a2
                  lui         a5, 236133
                  srl         a3, zero, a4
                  div         gp, a0, a6
                  sub         s8, gp, a1
                  slt         s1, s11, a6
                  addi        s1, s0, 462
                  div         s7, t5, a5
                  srl         t3, a5, a2
                  or          a6, t3, a5
                  c.slli      ra, 29
                  ori         s9, s6, 1811
                  srai        a4, gp, 22
                  c.srai      a3, 9
                  srai        zero, t0, 12
                  c.mv        gp, a6
                  c.slli      a0, 2
                  mulhu       t2, a5, s3
                  c.srai      s1, 3
                  auipc       s3, 949213
                  c.addi4spn  a3, sp, 896
                  xori        t0, t5, 1477
                  sltiu       zero, a2, 261
                  xori        s10, tp, -1039
                  add         ra, t3, t3
                  sub         s10, t4, a0
                  c.addi4spn  a3, sp, 864
                  mulhu       s1, t3, a3
                  sub         s8, s4, t1
                  or          s1, a7, s10
                  sub         t4, t3, ra
                  c.nop
                  slti        s9, gp, -1404
                  c.lui       a4, 15
                  slti        s9, s5, 922
                  sltu        a3, s3, zero
                  c.addi      a1, 11
                  c.addi4spn  s1, sp, 64
                  c.andi      a2, 11
                  rem         s3, a0, t5
                  c.addi4spn  a3, sp, 128
                  div         sp, s6, a5
                  xor         sp, s11, zero
                  c.nop
                  xor         s8, sp, gp
                  c.or        a3, s0
                  add         t2, s1, a6
                  add         t5, s3, t4
                  slti        t5, s9, 1278
                  mulhsu      zero, a5, s0
                  nop
                  c.nop
                  c.lui       ra, 13
                  sltu        zero, s11, t3
                  c.srli      a3, 18
                  c.slli      s5, 22
                  nop
                  c.and       a3, a3
                  add         s10, a2, t6
                  mulhsu      s4, s3, a7
                  lui         s2, 674491
                  sub         a2, ra, t2
                  lui         zero, 824412
                  mulh        t2, s0, s2
                  lui         s4, 67335
                  c.or        a3, a3
                  slli        a0, a0, 5
                  auipc       s3, 237020
                  mulh        t1, s0, s2
                  divu        zero, a1, s4
                  c.xor       a3, a3
                  auipc       t3, 546088
                  xori        s8, ra, -788
                  c.andi      a3, 8
                  c.addi16sp  sp, -16
                  slt         a6, s7, a5
                  slli        s10, a6, 1
                  ori         t5, s8, 1549
                  xori        s8, a0, -1998
                  c.addi16sp  sp, -16
                  add         t4, t2, tp
                  xor         t1, a5, tp
                  srl         a5, gp, s2
                  xori        a4, sp, 1814
                  c.mv        a3, s0
                  slt         s1, tp, s11
                  xor         s4, t5, s2
                  mulh        zero, a4, t5
                  or          a0, zero, t3
                  c.slli      sp, 7
                  mulhsu      tp, t2, s6
                  c.andi      a3, 19
                  slt         t2, t4, s7
                  or          s7, a0, s8
                  andi        s2, t2, -661
                  andi        t5, s0, -1485
                  mulh        t4, a0, t5
                  c.addi      ra, -1
                  divu        zero, s9, s10
                  mulh        zero, a2, s8
                  div         s10, s2, t5
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_3
                  li         s1, 0x1
                  li         t3, 0x5546d93a
                  li         s9, 0x1
                  li         t4, 0x1
                  li         a2, 0x1
                  li         ra, 0x0
                  li         a3, 0x0
                  li         a5, 0x0
                  li         t0, 0x40274006
                  divu        s4, t4, t2
                  rem         a2, a0, a4
                  c.li        a3, -1
                  c.add       s8, a0
                  c.mv        t0, s0
                  addi        ra, t6, 441
                  c.nop
                  mul         s9, gp, ra
                  nop
                  mulhsu      a7, t0, s7
                  mul         s2, zero, s11
                  c.add       ra, gp
                  mul         a3, s2, t2
                  c.lui       a5, 21
                  lui         t1, 488183
                  mul         t0, a1, t3
                  mulhu       t5, s3, a5
                  mulhu       gp, zero, s2
                  mul         a2, s0, s5
                  mul         s8, a1, s0 #end riscv_int_numeric_corner_stream_3
                  sub         a2, s0, s8
                  c.or        a3, a3
                  c.lui       ra, 30
                  xori        s5, s4, 148
                  slti        a1, a4, 1872
                  andi        a1, s0, 1293
                  div         s0, ra, s1
                  c.addi4spn  a0, sp, 832
                  mulh        a7, s11, s2
                  sltiu       zero, t4, -1572
                  c.add       a5, a7
                  srl         s4, t3, s8
                  and         s0, s4, s3
                  c.mv        s0, s1
                  c.addi16sp  sp, -16
                  slli        s4, a1, 27
                  add         t3, a0, t1
                  mulhu       s3, t0, s1
                  c.addi4spn  a3, sp, 912
                  nop
                  slti        tp, zero, -905
                  slt         zero, a4, s5
                  c.xor       a3, a3
                  sub         tp, ra, s2
                  c.slli      a7, 9
                  srli        zero, s4, 18
                  mulhsu      s0, a0, t3
                  slti        a0, a6, 810
                  slli        s4, s0, 18
                  lui         t0, 214474
                  sltu        s2, t5, s10
                  c.addi      ra, 18
                  addi        s10, gp, -820
                  mulh        gp, s5, s6
                  c.srli      a3, 21
                  c.and       a3, a3
                  c.or        a3, a3
                  c.addi16sp  sp, 400
                  add         a1, s0, s4
                  srl         s8, s4, s8
                  sra         tp, s9, s0
                  auipc       zero, 415376
                  c.andi      a3, -1
                  c.andi      s1, 30
                  lui         s3, 663875
                  nop
                  c.mv        a5, a0
                  mul         sp, s3, s7
                  sll         s7, t3, s10
                  and         a1, s5, a4
                  c.li        s2, -1
                  add         a5, s2, t3
                  lui         tp, 727859
                  andi        t0, t6, 1244
                  srli        a3, a3, 27
                  ori         gp, zero, -141
                  c.sub       a3, a3
                  nop
                  c.sub       a3, a3
                  c.or        a4, a3
                  mulhu       s0, a2, ra
                  srl         a3, a2, a4
                  addi        s7, s8, 1585
                  c.addi      t5, -1
                  andi        zero, s7, 56
                  mulhsu      s10, a0, s4
                  mulhsu      zero, s5, s11
                  add         s3, t4, gp
                  c.xor       a3, a3
                  c.xor       a3, a3
                  c.nop
                  ori         t3, a6, 1595
                  xor         t2, a5, t0
                  andi        t3, s10, 73
                  c.or        a3, a3
                  c.and       a3, a3
                  sub         a7, s9, s7
                  c.add       a1, a5
                  lui         zero, 172398
                  c.lui       t0, 10
                  srai        a5, a0, 27
                  c.addi4spn  a1, sp, 896
                  c.mv        s8, a2
                  sll         s10, t1, t4
                  srli        s5, a4, 0
                  mulhu       t3, s6, t2
                  slti        gp, sp, -1692
                  c.srai      a3, 27
                  rem         s10, t1, t4
                  nop
                  srai        s1, s4, 8
                  sra         t0, ra, gp
                  sll         s7, sp, zero
                  slt         t1, a0, t3
                  c.addi      t3, 13
                  rem         s9, s0, s0
                  slli        a1, a3, 5
                  slli        s5, s1, 8
                  nop
                  rem         ra, gp, t6
                  c.lui       s2, 8
                  slt         t3, t2, t5
                  ori         s5, s0, 1752
                  and         s5, s3, a6
                  mulh        s3, t6, s9
                  c.or        a3, a1
                  andi        t4, t1, 1852
                  c.andi      a3, -1
                  c.and       a3, a3
                  c.addi      t4, -1
                  slli        t0, a4, 27
                  c.or        a3, a4
                  mulh        s3, s6, a0
                  sltu        zero, s6, s1
                  auipc       a5, 607066
                  c.or        a3, a5
                  sub         a7, t1, t2
                  c.slli      ra, 23
                  c.add       t3, a4
                  or          ra, s8, sp
                  c.addi4spn  a3, sp, 896
                  lui         s8, 723041
                  c.or        a3, a1
                  and         ra, zero, t0
                  sra         t1, a2, a3
                  slli        gp, s11, 11
                  andi        a0, s9, -418
                  c.addi4spn  a3, sp, 304
                  sub         a1, t6, s1
                  or          t2, a3, t1
                  c.addi      t2, 11
                  sltu        s4, a4, sp
                  lui         s8, 867730
                  add         a2, s9, a0
                  div         t2, s3, a7
                  sub         s8, a5, a5
                  c.lui       ra, 20
                  c.addi      a4, -1
                  rem         a6, s10, t6
                  c.addi16sp  sp, 432
                  c.srli      a3, 8
                  c.slli      a1, 6
                  lui         t4, 127199
                  xori        s3, s5, -1856
                  mulhu       zero, s5, s2
                  c.srai      a3, 7
                  xori        a1, a3, 174
                  c.srai      a3, 27
                  c.add       t5, t2
                  srai        t4, t1, 20
                  andi        t4, t5, 1136
                  div         a1, s3, s7
                  c.slli      a7, 16
                  sltiu       s3, s5, -1282
                  rem         a5, a4, a6
                  nop
                  divu        ra, s10, sp
                  slli        zero, a4, 13
                  c.lui       a7, 31
                  slti        a5, s6, 1765
                  c.or        a3, a3
                  mulhu       zero, s10, s10
                  add         zero, ra, s1
                  srl         a5, s9, zero
                  divu        tp, s6, t5
                  c.or        a3, a3
                  c.sub       a3, a3
                  mulhsu      a1, s8, s2
                  sll         s8, s11, a4
                  slli        s4, a0, 24
                  c.lui       a3, 24
                  or          a1, a7, s4
                  sltu        ra, a3, tp
                  and         s3, s8, s7
                  c.and       a3, a3
                  mul         s8, s1, tp
                  c.mv        t1, t0
                  sll         s5, t6, t4
                  rem         zero, a2, tp
                  sltiu       s0, a7, 1314
                  or          t5, t1, t3
                  slt         s2, a6, a7
                  c.li        ra, -1
                  sub         a4, s10, s5
                  mulhu       zero, t3, ra
                  or          a3, a5, t4
                  srli        sp, s8, 27
                  c.srai      a3, 1
                  lui         t1, 338305
                  andi        s2, a0, 501
                  c.or        a3, a3
                  c.slli      a4, 17
                  c.lui       s10, 27
                  c.lui       gp, 6
                  slli        t2, t3, 18
                  or          t1, ra, t1
                  c.li        a6, -1
                  c.addi16sp  sp, -16
                  c.sub       a2, a1
                  mul         zero, s10, a1
                  sub         zero, a2, a5
                  c.andi      a3, -1
                  slti        s1, s10, 1183
                  auipc       a6, 532487
                  slti        t4, s3, 681
                  add         t3, t6, s10
                  c.mv        ra, t1
                  lui         t2, 542168
                  and         t1, a0, a4
                  slt         sp, ra, a5
                  mulh        zero, s4, a2
                  addi        zero, t1, 1356
                  mul         a5, s1, s2
                  divu        t1, t2, gp
                  c.srli      a3, 9
                  mulhsu      t5, sp, a5
                  lui         a0, 98160
                  c.li        sp, 26
                  xor         a1, zero, t1
                  addi        zero, s0, -138
                  c.and       a0, a3
                  mul         sp, s11, s1
                  divu        zero, zero, a7
                  c.mv        gp, s2
                  div         s1, s11, s6
                  c.lui       s0, 28
                  c.lui       a7, 26
                  slti        s10, a6, -660
                  c.srai      a3, 21
                  rem         s8, s2, sp
                  addi        t5, s4, -80
                  slli        t1, a6, 18
                  mul         a5, a3, s11
                  c.nop
                  c.lui       ra, 8
                  mulhsu      a4, a3, tp
                  sll         zero, t4, s10
                  c.li        a3, -1
                  sltu        tp, a1, tp
                  c.add       ra, s8
                  sltiu       zero, s8, 1093
                  ori         a4, a2, -2021
                  c.mv        a6, s0
                  slli        t0, t1, 0
                  and         t5, tp, s9
                  or          s2, zero, a5
                  c.lui       s5, 17
                  addi        s9, s0, 674
                  and         t0, gp, t4
                  auipc       a0, 108291
                  c.addi4spn  a3, sp, 176
                  c.li        gp, 15
                  srli        a7, s10, 15
                  c.and       a3, a5
                  sltiu       a5, s10, 721
                  c.andi      a0, 22
                  c.li        t1, -1
                  slt         sp, s1, ra
                  rem         zero, t1, tp
                  auipc       zero, 110268
                  c.mv        a6, s9
                  xori        a2, a0, 485
                  sltiu       zero, gp, -1419
                  c.andi      a0, -1
                  mulh        s1, t6, a0
                  mulhsu      sp, s8, a5
                  c.andi      a3, -1
                  srai        t4, a0, 12
                  xor         t4, a0, s0
                  xori        ra, s6, -1087
                  srai        s5, sp, 22
                  c.slli      a2, 23
                  mul         a4, a6, zero
                  slli        gp, s8, 9
                  c.srli      a3, 19
                  auipc       sp, 173027
                  rem         zero, t3, t5
                  c.andi      a3, 27
                  c.srai      a3, 3
                  div         t2, s3, s11
                  mulhsu      t2, s2, s5
                  srli        s0, t5, 5
                  srli        a7, sp, 5
                  c.sub       a3, a3
                  mulhsu      s4, t1, t2
                  c.andi      a3, 3
                  c.addi4spn  a3, sp, 640
                  add         a7, s5, s3
                  c.nop
                  c.srli      a3, 28
                  xori        a3, a5, 751
                  c.lui       t4, 11
                  c.lui       t5, 6
                  c.addi4spn  a3, sp, 128
                  lui         tp, 1012962
                  sltu        zero, a3, t3
                  mulhsu      zero, tp, a2
                  slti        a4, s9, -437
                  c.add       ra, t6
                  c.addi4spn  a3, sp, 704
                  c.li        s8, 11
                  c.andi      a3, 30
                  c.srli      a1, 16
                  mulhsu      s9, s0, gp
                  srl         s0, ra, a5
                  mulhu       s1, a5, s6
                  nop
                  c.mv        t2, s2
                  c.li        ra, 17
                  c.slli      s0, 29
                  ori         zero, s4, 1370
                  mul         sp, a7, a2
                  lui         ra, 725604
                  rem         s0, s3, s2
                  xori        a2, gp, 65
                  auipc       s9, 408241
                  srl         a4, t4, a5
                  lui         tp, 157970
                  sltu        a4, a6, s10
                  mulhsu      t0, a0, a4
                  div         t3, a0, gp
                  mulhu       s4, s0, a0
                  sra         s0, a4, t5
                  c.addi4spn  a3, sp, 608
                  sltu        zero, s11, a5
                  mulh        tp, t0, a6
                  mulhu       a6, a7, t6
                  add         a6, s1, t6
                  c.li        a3, 23
                  xor         t3, t1, ra
                  c.or        a3, a4
                  lui         zero, 516328
                  div         t5, a6, t6
                  div         a2, t2, tp
                  and         a7, s6, s7
                  and         a6, t3, a2
                  c.slli      s10, 18
                  andi        s8, s8, 871
                  or          tp, s6, t2
                  rem         zero, a7, s9
                  c.li        s9, -1
                  slti        zero, gp, -1177
                  c.li        a0, 17
                  sub         s4, t3, t3
                  mulhu       t4, s6, t4
                  mulh        s5, a7, a0
                  add         t5, a6, a3
                  sll         t0, a0, s4
                  div         zero, s1, a5
                  srli        t5, gp, 26
                  c.addi      a2, -1
                  mulh        t3, t5, a7
                  c.li        ra, 28
                  c.mv        s10, a3
                  slli        t0, s6, 11
                  srli        a5, t5, 0
                  sltu        s10, s2, t5
                  divu        a3, t6, ra
                  sltu        gp, sp, s1
                  add         a3, tp, a0
                  divu        a1, gp, t4
                  andi        s3, t0, 1783
                  sltiu       a4, a1, -2022
                  c.addi4spn  a3, sp, 320
                  divu        a6, t6, s2
                  mul         a1, s3, a0
                  mulhsu      t0, sp, gp
                  c.addi      s8, -1
                  c.andi      a3, -1
                  addi        a5, gp, 272
                  sub         s8, t6, s2
                  slli        ra, s0, 18
                  sll         s7, zero, a5
                  andi        s9, t4, 1159
                  sltiu       s3, t2, -1511
                  div         zero, s9, s2
                  c.and       a3, a3
                  c.addi16sp  sp, 160
                  divu        a6, t3, s8
                  c.slli      s9, 5
                  c.nop
                  c.lui       a1, 30
                  andi        a6, t0, -692
                  slti        s7, s6, -1313
                  andi        t1, a6, -1374
                  sll         s0, a1, a7
                  srli        s2, tp, 17
                  c.lui       s9, 25
                  sltiu       t1, zero, -1491
                  c.xor       s1, a3
                  c.li        a5, 16
                  add         s0, s2, gp
                  andi        a5, t4, -1209
                  xori        s10, t0, -1910
                  divu        s4, a6, s5
                  sra         s1, gp, s11
                  slli        t5, s3, 18
                  mulhsu      s10, s6, s1
                  c.addi16sp  sp, 480
                  lui         s8, 92968
                  mul         a6, s4, gp
                  c.addi4spn  a3, sp, 576
                  nop
                  slt         s4, a1, a2
                  xor         ra, zero, sp
                  andi        zero, t0, 1776
                  addi        tp, s10, 306
                  c.srli      a3, 5
                  mul         s3, s5, t6
                  c.sub       a3, a3
                  div         a3, s1, a1
                  auipc       t5, 479913
                  c.mv        t4, ra
                  slli        s4, gp, 4
                  auipc       s2, 117401
                  slti        a5, a7, 1771
                  c.andi      a3, 8
                  c.sub       a3, a3
                  nop
                  divu        zero, a1, t0
                  c.and       a1, a3
                  sltu        s3, s3, gp
                  c.xor       a4, a3
                  c.srai      a3, 25
                  c.li        s9, -1
                  c.andi      a3, 17
                  c.xor       a3, a3
                  or          zero, t5, sp
                  or          s4, gp, a0
                  andi        zero, a6, -1472
                  c.addi      ra, -1
                  c.sub       a3, a3
                  c.add       t2, a6
                  c.addi4spn  a3, sp, 112
                  and         a7, gp, s11
                  c.srli      a3, 7
                  sub         t1, s8, s5
                  add         s3, t5, t5
                  and         zero, a4, a6
                  c.and       a3, a3
                  mulhu       a5, t2, s2
                  divu        a2, s0, tp
                  c.slli      ra, 20
                  c.add       a6, t3
                  sll         ra, ra, a5
                  c.xor       a3, a3
                  c.sub       a3, a3
                  slti        t0, ra, -900
                  add         tp, s3, tp
                  sub         s2, s2, t6
                  c.addi16sp  sp, -16
                  mulhu       s7, s8, t6
                  sra         s3, t1, a4
                  lui         zero, 441563
                  c.li        s2, 22
                  divu        s4, t3, gp
                  sra         t4, s2, a4
                  c.lui       s1, 12
                  sra         a5, s0, sp
                  sub         a2, a5, sp
                  sra         tp, a3, a3
                  c.sub       a3, s1
                  lui         a4, 622763
                  xori        zero, t0, -459
                  sra         s0, a4, s7
                  c.xor       a3, a3
                  mulhu       s2, a2, a3
                  c.srli      a2, 26
                  c.andi      a3, 12
                  c.srli      a3, 6
                  slli        a6, a3, 14
                  c.srai      a0, 19
                  c.or        s1, a3
                  mul         a3, sp, t3
                  div         a3, a4, a3
                  mul         t5, t5, a0
                  c.mv        a6, t4
                  sra         s3, t0, s11
                  c.xor       s0, a3
                  c.li        s10, 3
                  nop
                  or          t4, s11, s10
                  xor         s0, a4, a2
                  mulh        a5, a3, t0
                  andi        a6, a3, -77
                  c.srli      a3, 27
                  mul         s5, s7, a5
                  andi        s10, s11, -1144
                  divu        s8, sp, a3
                  c.mv        s0, a1
                  c.lui       t1, 26
                  srai        gp, a4, 25
                  sra         t1, a5, ra
                  c.addi      s4, -1
                  lui         s2, 327757
                  addi        zero, s10, 691
                  sll         t2, a0, s8
                  mul         s8, t1, s1
                  c.addi4spn  a4, sp, 960
                  c.and       a3, a3
                  slt         a1, a5, zero
                  srl         s2, t3, s1
                  c.slli      tp, 19
                  c.sub       a3, a3
                  slli        a5, s11, 4
                  c.addi16sp  sp, 464
                  srai        gp, s2, 2
                  divu        ra, a6, s1
                  sra         s2, t4, s0
                  sll         s8, a5, t3
                  c.addi16sp  sp, 256
                  c.srli      s0, 11
                  sltiu       a7, sp, -1857
                  sra         t0, s10, s7
                  c.or        a3, a3
                  c.li        s4, 29
                  sltu        zero, s1, a1
                  lui         s5, 823062
                  divu        a7, sp, a4
                  sltu        a1, s1, s0
                  c.and       a3, a3
                  mulhu       a6, s11, s3
                  auipc       s8, 156456
                  and         s7, s4, s0
                  mulh        zero, a5, gp
                  addi        sp, s11, -1907
                  addi        t2, tp, -1119
                  slt         a1, s5, t0
                  c.sub       a3, a3
                  slli        s8, s3, 26
                  c.srai      a3, 5
                  rem         s5, s11, t5
                  lui         tp, 551230
                  c.lui       a4, 25
                  nop
                  xori        s8, s3, -1307
                  andi        s1, t6, -201
                  c.nop
                  or          s7, s6, s7
                  slli        s8, t4, 13
                  c.nop
                  sub         ra, ra, s11
                  srli        a3, t4, 22
                  slt         zero, t6, s2
                  xor         s7, sp, a5
                  c.srai      a3, 16
                  sltiu       s1, sp, -1375
                  c.and       a3, a2
                  srli        s4, a0, 23
                  c.nop
                  c.addi16sp  sp, -16
                  c.and       a3, a3
                  c.and       a2, a3
                  mulh        zero, t2, ra
                  c.srai      a3, 8
                  lui         a6, 298693
                  c.sub       a2, a3
                  slli        a2, a3, 17
                  xor         a2, t2, a6
                  and         sp, zero, a7
                  divu        s3, a1, zero
                  c.addi4spn  a3, sp, 832
                  xori        t4, s9, 1436
                  c.and       s1, a2
                  c.li        gp, 6
                  addi        a0, s10, 942
                  srl         t0, s2, s0
                  c.addi      a3, -1
                  ori         s1, a3, 999
                  c.or        a3, s0
                  c.addi16sp  sp, -16
                  c.and       a2, a3
                  c.addi16sp  sp, 144
                  c.nop
                  c.and       a3, a3
                  c.srai      a3, 19
                  andi        t5, a5, 59
                  mul         t4, a5, s7
                  c.addi4spn  a3, sp, 656
                  c.addi16sp  sp, 368
                  sltu        t3, s6, a5
                  c.addi16sp  sp, -16
                  srai        s4, t3, 23
                  rem         s2, s9, s11
                  lui         s4, 630526
                  or          s3, s1, s0
                  divu        t0, a6, s0
                  rem         a6, a4, a3
                  or          zero, s10, s7
                  srai        gp, a6, 8
                  c.andi      a3, -1
                  mulhu       ra, t6, a6
                  srai        s10, s7, 12
                  divu        sp, t2, a4
                  srl         t1, s6, t4
                  or          zero, t0, t5
                  c.srli      a5, 4
                  c.sub       a3, s0
                  srli        t3, s7, 29
                  c.xor       a3, a3
                  c.xor       a3, a3
                  c.add       a4, tp
                  sll         a4, a0, s11
                  addi        a7, ra, 1704
                  srai        a3, s3, 0
                  c.addi16sp  sp, 176
                  c.mv        a4, s10
                  rem         t0, s2, t4
                  c.lui       a6, 18
                  xori        a4, t0, 371
                  add         s10, t3, s8
                  sra         zero, s8, s1
                  div         zero, gp, s1
                  div         zero, s2, s5
                  c.addi      gp, -1
                  c.addi4spn  a3, sp, 128
                  or          a1, tp, a0
                  and         s4, s4, a5
                  and         s3, s11, t6
                  c.xor       s0, a0
                  mul         a6, s4, a6
                  mulh        s7, a0, s2
                  c.andi      a3, 2
                  slli        gp, t6, 1
                  sll         zero, t2, zero
                  ori         a1, s0, -1202
                  sltu        zero, s9, s9
                  xor         a7, a7, a0
                  c.andi      a3, 30
                  c.srli      a1, 29
                  c.and       a3, a1
                  c.addi16sp  sp, 112
                  sll         s3, t1, a6
                  c.nop
                  c.li        s8, 21
                  mul         s9, ra, a0
                  or          s10, s6, s5
                  or          a4, t2, t1
                  addi        a1, s3, -789
                  sltiu       a7, s10, 1460
                  andi        zero, a2, 1033
                  ori         a2, a5, 1356
                  c.add       t5, t3
                  div         a2, s4, s5
                  c.lui       a0, 10
                  slt         s8, ra, a5
                  sub         a1, s11, a0
                  mulh        s7, ra, a3
                  sltiu       a7, s4, 1681
                  div         zero, a0, s1
                  divu        t1, s11, s5
                  div         t2, s1, a4
                  ori         t5, tp, -1464
                  srli        t4, s5, 28
                  andi        tp, t0, 3
                  c.add       ra, s2
                  mul         t5, a1, s8
                  c.srai      a3, 1
                  c.slli      a4, 10
                  c.sub       s1, a3
                  slt         t2, t1, s3
                  slt         a2, t6, ra
                  c.slli      s1, 13
                  sll         s5, t5, s4
                  c.lui       t0, 25
                  mulhsu      t0, s6, a6
                  c.slli      s3, 18
                  sll         s10, a1, s3
                  sub         zero, s3, t2
                  c.li        a3, 12
                  c.sub       a3, a0
                  c.and       s0, a3
                  c.slli      a1, 30
                  sltiu       t1, a4, 1898
                  xor         a0, a1, s4
                  sll         tp, a2, gp
                  sll         s1, t2, s9
                  c.addi4spn  a3, sp, 64
                  c.nop
                  srl         a1, t1, s2
                  c.xor       a3, a3
                  slti        s8, t3, 722
                  mulh        a2, s7, sp
                  slt         gp, s0, s2
                  c.addi4spn  a3, sp, 192
                  and         a7, zero, s8
                  sltiu       s3, s0, -1581
                  srli        gp, t0, 18
                  c.xor       a3, a3
                  lui         t0, 547936
                  auipc       a7, 84997
                  lui         s0, 297784
                  c.nop
                  c.addi4spn  a3, sp, 64
                  mul         t2, ra, s9
                  c.and       a3, a3
                  c.srai      a3, 20
                  xori        t1, ra, -704
                  addi        tp, s0, -1095
                  slt         tp, gp, t1
                  div         a3, a5, s5
                  c.srli      a3, 29
                  mulhsu      zero, s1, zero
                  sll         zero, zero, t2
                  divu        zero, s9, t5
                  c.add       ra, t2
                  c.addi4spn  s0, sp, 832
                  div         s10, a3, t1
                  divu        s0, a3, s11
                  c.addi16sp  sp, -16
                  c.sub       a3, a3
                  nop
                  c.add       a4, s7
                  c.addi16sp  sp, 128
                  div         a5, t2, tp
                  divu        t0, s0, t1
                  mulh        ra, ra, a2
                  srai        a0, t2, 17
                  slli        s4, a7, 8
                  auipc       a3, 635410
                  xori        a5, a5, 386
                  mul         t5, t0, zero
                  div         tp, s9, a7
                  c.srli      a4, 21
                  or          s10, a6, a7
                  and         t0, s11, s5
                  sltiu       s0, t4, -1736
                  c.xor       a3, a3
                  c.slli      ra, 18
                  addi        s0, tp, -1957
                  sub         s0, sp, t2
                  sll         ra, a2, a2
                  div         s2, s6, s11
                  slti        a4, t5, -739
                  c.slli      s10, 8
                  sra         s4, ra, s6
                  c.mv        s3, t4
                  c.mv        a0, s3
                  c.mv        a0, a2
                  sltu        zero, zero, s2
                  sll         zero, ra, t5
                  or          zero, t1, gp
                  c.addi16sp  sp, -16
                  mulhu       s2, t0, s7
                  addi        zero, tp, 868
                  c.li        ra, 19
                  srl         s2, s6, a4
                  c.or        s0, a3
                  add         zero, t5, t2
                  div         s10, t2, s5
                  c.add       t5, s1
                  c.and       s1, a3
                  srl         a2, s7, s4
                  c.nop
                  sub         s7, s1, gp
                  c.srli      a3, 7
                  c.lui       ra, 17
                  c.addi4spn  a3, sp, 608
                  sll         zero, t1, t6
                  mul         s5, s0, s10
                  c.slli      gp, 17
                  c.srai      a3, 16
                  mulh        a3, s7, s6
                  mulhsu      t3, s3, s3
                  sll         a7, s8, s3
                  srli        t2, t1, 0
                  c.lui       tp, 4
                  c.or        a1, a3
                  sra         t5, t3, a3
                  li         s8, 0x36da021a #start riscv_int_numeric_corner_stream_14
                  li         t5, 0x1
                  li         t4, 0xd795b36
                  li         t3, 0x0
                  li         s2, 0x1
                  li         a3, 0x0
                  li         a4, 0x9dd4bd8
                  li         a2, 0x1
                  li         tp, 0x1
                  li         a0, 0x0
                  mul         s4, t3, tp
                  div         a5, ra, s7
                  c.mv        s8, t5
                  div         zero, a6, s5
                  add         ra, a3, s3
                  c.mv        s4, a0
                  divu        tp, s0, gp
                  c.addi4spn  a2, sp, 96
                  mulh        s2, s4, t3
                  mulhu       a3, s7, s4
                  mulhu       a3, s2, gp
                  sub         tp, a0, a5
                  mulh        s0, a1, s3
                  mulh        zero, gp, a0
                  c.add       t2, s7
                  div         s0, a7, s6
                  c.sub       a2, a0
                  mulhsu      s9, a3, sp
                  mulhsu      a3, a3, a3
                  nop
                  c.lui       ra, 16
                  lui         zero, 645206
                  lui         s8, 218363 #end riscv_int_numeric_corner_stream_14
                  c.add       a3, tp
                  mulhu       s9, a5, s0
                  c.addi      a5, -1
                  mul         t2, a2, tp
                  c.slli      s5, 1
                  slti        s0, a4, 1024
                  xori        s2, s6, 1228
                  sltu        t1, t0, s5
                  c.andi      s0, 7
                  ori         t4, t4, -1735
                  c.and       a3, s0
                  srai        zero, a6, 21
                  c.srli      a1, 20
                  lui         a1, 323942
                  c.slli      s9, 1
                  rem         s7, t1, t4
                  c.add       s1, s7
                  c.mv        a1, s11
                  srai        a4, t6, 0
                  c.or        a3, a5
                  ori         a2, zero, -204
                  slti        t1, t0, -1387
                  sltiu       a2, a4, 1818
                  mulh        s8, a5, t6
                  sra         s9, s9, s0
                  divu        a6, a3, a5
                  c.and       a3, s1
                  sra         s0, a5, ra
                  xori        a5, s2, -284
                  c.andi      a3, 11
                  c.addi      a6, -1
                  xor         s0, s1, t0
                  slt         a1, ra, s4
                  c.lui       a1, 31
                  slt         a5, a7, t3
                  andi        a4, a3, -1327
                  sll         s1, a3, s8
                  mulhsu      s0, a0, a5
                  srai        zero, s8, 14
                  c.mv        a3, a4
                  auipc       s2, 690282
                  mul         t5, ra, t3
                  ori         t4, ra, -756
                  sltiu       t2, a3, -635
                  c.mv        s0, a4
                  srli        a2, a5, 23
                  sltu        zero, s9, s3
                  sra         s1, s3, sp
                  mulhsu      tp, a2, sp
                  c.srai      a3, 16
                  c.sub       a0, a2
                  mulhsu      s5, t6, a4
                  or          t1, ra, zero
                  srl         s3, a0, s4
                  c.srai      a3, 27
                  srai        a4, s10, 12
                  add         a6, a3, tp
                  c.and       a3, a3
                  c.srai      a0, 6
                  lui         a6, 998203
                  div         t3, t6, t4
                  mulh        sp, t4, a6
                  c.addi      sp, 17
                  srl         a3, s0, a6
                  sltu        t2, s8, sp
                  slli        sp, t2, 25
                  sltiu       zero, t3, -1868
                  or          zero, s11, a6
                  andi        a6, t1, -204
                  c.sub       a3, a3
                  c.sub       a3, a3
                  c.and       a3, a3
                  sltiu       zero, t6, 858
                  mulhu       t2, s4, t0
                  c.add       s8, s10
                  c.slli      t0, 8
                  auipc       a4, 906940
                  slti        a4, zero, -997
                  divu        a5, a2, t0
                  addi        s7, gp, -873
                  mulhu       zero, t3, s2
                  c.srai      a4, 31
                  sltiu       s7, s0, 1520
                  nop
                  srli        a1, t1, 22
                  c.slli      t3, 3
                  slli        a3, t1, 9
                  srli        a0, t3, 23
                  c.mv        a7, s1
                  c.addi      a7, 23
                  div         s2, zero, a5
                  mulhu       a7, ra, t2
                  c.addi4spn  a4, sp, 192
                  divu        a2, s7, a6
                  andi        a3, s10, 1171
                  xor         sp, a3, s11
                  mul         a5, t6, s1
                  mulhu       t2, s3, s3
                  c.li        t0, -1
                  slti        s2, s2, -1900
                  mulhsu      t0, s7, t4
                  sub         a6, s8, s7
                  sub         zero, t1, sp
                  div         s7, s9, s2
                  xori        zero, s1, 1139
                  or          t2, a2, s5
                  nop
                  mulhu       s10, t4, gp
                  or          ra, a3, s6
                  srl         a1, t4, t3
                  c.li        a3, -1
                  c.and       a2, a3
                  c.sub       a3, a3
                  c.srli      a3, 9
                  c.add       a1, t6
                  andi        zero, zero, -1574
                  c.or        a3, a0
                  xor         s2, a6, s11
                  sub         s4, s9, zero
                  c.mv        a4, s11
                  andi        t4, a0, -1280
                  c.lui       s1, 2
                  andi        s8, s4, 1202
                  rem         s2, s10, t0
                  c.nop
                  c.li        s5, -1
                  c.nop
                  c.sub       s0, a3
                  c.sub       a3, a3
                  c.addi4spn  a3, sp, 192
                  c.or        a4, a3
                  rem         s5, t1, t5
                  c.lui       gp, 1
                  c.slli      a3, 3
                  ori         zero, a2, -720
                  c.addi16sp  sp, -16
                  div         s8, s7, t6
                  c.or        a0, a3
                  c.srli      a3, 20
                  c.sub       a3, a3
                  or          s1, t3, t3
                  c.sub       s0, a3
                  slti        zero, a0, 435
                  andi        s4, s1, -246
                  auipc       zero, 283289
                  xor         gp, s4, a0
                  auipc       t1, 34034
                  c.andi      a3, 25
                  slt         zero, a3, t6
                  c.addi4spn  s1, sp, 64
                  srl         tp, a1, ra
                  sub         a0, a5, s2
                  c.slli      a2, 26
                  slti        sp, s4, 1574
                  mulhu       s1, t4, t3
                  xor         a1, s0, s6
                  c.and       a3, a3
                  mul         s1, s7, a7
                  lui         a3, 436325
                  sub         t0, gp, s2
                  c.mv        a2, a3
                  slt         s9, s4, s10
                  lui         a6, 194592
                  add         gp, a0, a4
                  c.addi4spn  a3, sp, 320
                  c.srai      a3, 1
                  c.andi      a3, -1
                  c.sub       a3, a3
                  nop
                  sltu        a0, gp, a1
                  andi        s0, t3, 1117
                  xor         s9, t0, s2
                  c.addi4spn  a3, sp, 352
                  c.add       sp, s5
                  andi        s10, s4, 1493
                  srl         s4, t1, s7
                  auipc       a4, 161032
                  auipc       t3, 709184
                  c.addi4spn  a3, sp, 64
                  andi        sp, t5, -1669
                  mul         a3, sp, t0
                  c.xor       a3, a2
                  divu        t1, sp, s6
                  sub         s10, sp, s3
                  c.or        a0, a3
                  add         sp, s10, a3
                  c.addi16sp  sp, 112
                  c.and       a3, a3
                  c.sub       a3, a3
                  slti        t0, s8, 1360
                  mul         a7, s6, t6
                  srl         s5, a4, s1
                  c.or        a3, a3
                  sltiu       s0, a1, 282
                  srl         a7, a3, tp
                  ori         ra, s0, -1785
                  addi        s3, s3, 1562
                  c.srai      a3, 29
                  lui         t2, 960163
                  addi        s8, sp, -36
                  or          s4, t3, s9
                  mulh        a6, s2, t4
                  c.and       a3, a3
                  srl         t5, a1, tp
                  c.li        s3, -1
                  mulhu       s9, s0, a2
                  c.li        a3, 25
                  c.nop
                  mulhsu      s5, s11, s4
                  sra         a3, t5, sp
                  c.xor       a3, a3
                  ori         s9, a1, -524
                  mul         a7, s11, ra
                  c.mv        ra, t5
                  lui         a4, 273369
                  mulhu       s3, t1, s11
                  addi        zero, a1, -734
                  slti        a2, s6, 1661
                  slt         a6, s9, s0
                  andi        a0, t5, 788
                  addi        zero, a4, -1449
                  srai        t2, a4, 13
                  sub         s2, a5, s3
                  addi        a3, s6, 453
                  mulh        sp, a4, s9
                  c.srli      s0, 12
                  mulhsu      zero, a6, t4
                  c.xor       a3, s1
                  auipc       zero, 703199
                  mul         tp, a7, s8
                  mulhu       a4, t0, s3
                  nop
                  sltiu       a6, s11, -766
                  andi        a1, zero, -1483
                  auipc       zero, 646630
                  add         a3, s10, s4
                  mulh        s7, s8, s9
                  c.addi4spn  a3, sp, 320
                  c.li        sp, -1
                  slti        a0, a2, 846
                  lui         s7, 382557
                  xori        s5, s4, 1138
                  andi        s7, s0, -1127
                  c.or        a1, a3
                  mulhu       t5, s9, s4
                  srai        s2, ra, 22
                  mulh        s0, t4, a6
                  c.slli      a2, 2
                  c.addi16sp  sp, -16
                  slli        t3, ra, 27
                  ori         s8, s9, -945
                  c.addi16sp  sp, 176
                  xori        a1, s7, -1320
                  and         a4, t5, ra
                  nop
                  sub         s8, s8, gp
                  c.sub       a3, a3
                  c.slli      gp, 20
                  srli        s7, t1, 6
                  nop
                  srai        s0, tp, 23
                  lui         s2, 644040
                  lui         zero, 354652
                  slt         tp, s6, s9
                  mulhsu      t4, s3, a2
                  ori         zero, a2, 1020
                  c.addi16sp  sp, -16
                  sltu        zero, ra, a5
                  c.add       a6, s8
                  c.or        a3, a0
                  c.addi16sp  sp, 128
                  nop
                  xor         s10, s4, s6
                  slt         a5, a2, s5
                  sub         t1, ra, t3
                  mulh        s9, s2, a6
                  andi        a3, s9, -1615
                  srli        zero, gp, 2
                  c.addi4spn  a3, sp, 608
                  c.sub       a5, a3
                  ori         zero, s5, 699
                  slti        tp, s7, -1561
                  c.addi16sp  sp, 192
                  rem         zero, s2, tp
                  c.addi16sp  sp, -16
                  c.lui       a6, 26
                  mul         s7, s5, s8
                  c.and       a3, a3
                  or          s10, tp, t3
                  c.sub       a3, a3
                  mulhsu      a2, t2, s4
                  andi        zero, a3, -915
                  c.lui       s1, 23
                  sltiu       a5, s9, -508
                  ori         s10, a4, -1518
                  mulhu       tp, t6, a7
                  and         a5, a2, s11
                  c.addi16sp  sp, 208
                  sltu        s8, a4, a1
                  slti        zero, s3, -2025
                  c.lui       a2, 22
                  c.nop
                  auipc       s8, 26988
                  c.and       a3, a3
                  and         s4, a7, t5
                  mulh        t1, sp, s7
                  rem         zero, t1, t5
                  rem         t1, s6, s0
                  c.xor       a3, a3
                  c.srai      a3, 11
                  sll         a2, s1, gp
                  mulhu       a4, s3, t3
                  mul         sp, t5, s2
                  mulhu       a5, sp, a5
                  c.sub       a1, a3
                  srai        t1, tp, 5
                  mul         s7, t5, a7
                  sltiu       zero, sp, -780
                  sra         s2, a1, a2
                  c.andi      a3, 7
                  srl         s2, a2, sp
                  ori         t0, s6, 1274
                  c.andi      s0, 23
                  nop
                  add         gp, s11, t2
                  slt         ra, a3, a5
                  c.sub       a3, a1
                  mulhu       s9, t2, zero
                  c.lui       s0, 6
                  and         a2, ra, a3
                  c.or        a3, a3
                  sltu        a3, s1, s1
                  slti        t0, s6, 693
                  lui         t0, 1044955
                  sltiu       s3, a4, -1202
                  c.andi      a3, 22
                  nop
                  c.nop
                  c.andi      a3, 18
                  addi        s1, s4, 866
                  rem         sp, gp, s3
                  mul         zero, s3, sp
                  nop
                  sra         tp, t0, t6
                  and         zero, t4, ra
                  c.srai      a3, 24
                  c.srli      a3, 8
                  mulhsu      s5, s2, tp
                  ori         a1, t4, -689
                  sll         a0, a5, a2
                  divu        s8, gp, s1
                  c.addi4spn  a3, sp, 128
                  c.andi      a5, -1
                  c.sub       a3, a3
                  slt         s5, t2, s4
                  c.sub       a0, a3
                  c.addi4spn  a0, sp, 192
                  mulhsu      a3, s5, s9
                  mulhsu      s8, gp, s6
                  slt         t2, a3, s8
                  c.srli      a0, 11
                  sll         s1, s3, t6
                  or          s4, s8, s5
                  c.addi16sp  sp, 256
                  c.srai      a3, 19
                  slti        a5, t0, -1164
                  c.sub       a5, a3
                  mulh        s4, t2, t1
                  sltiu       s1, s5, 901
                  divu        zero, s4, zero
                  sub         a6, s2, zero
                  andi        zero, a3, 185
                  mulhu       a4, ra, t6
                  nop
                  mulhu       s1, s3, t3
                  slt         a4, a1, a3
                  c.mv        ra, a5
                  sltiu       s0, t1, -1932
                  nop
                  rem         a6, s9, s1
                  c.xor       a3, a3
                  addi        a7, a4, -1251
                  nop
                  auipc       t4, 580155
                  c.addi4spn  a3, sp, 576
                  add         a1, s5, s7
                  c.addi      s9, 11
                  sll         t5, s8, ra
                  c.and       a3, a3
                  c.lui       ra, 2
                  mulh        s3, a7, sp
                  sltiu       a2, s10, 1902
                  or          zero, a7, t0
                  c.addi      t1, -1
                  andi        gp, t3, -1261
                  mul         t0, a1, s0
                  sltu        t5, s6, a3
                  sub         a3, a4, t6
                  c.addi4spn  a3, sp, 640
                  srai        a1, s8, 30
                  c.addi16sp  sp, 112
                  or          zero, a3, tp
                  c.or        a3, a3
                  c.slli      a7, 29
                  sll         zero, s2, s1
                  srai        s10, t4, 20
                  srl         s2, gp, t4
                  xor         a6, ra, a2
                  sll         s7, zero, t4
                  c.xor       a2, a3
                  c.srli      a3, 14
                  srai        a7, t0, 9
                  c.nop
                  nop
                  c.srai      a3, 20
                  add         t5, s3, s6
                  mul         a7, s0, s6
                  c.sub       a0, a3
                  c.srai      a3, 30
                  c.mv        s1, a2
                  add         s1, a3, zero
                  xori        sp, s9, -1726
                  rem         a2, t6, s10
                  ori         t0, a1, 2018
                  srl         s4, tp, a5
                  and         a7, s10, t3
                  rem         t5, s6, a0
                  c.slli      sp, 1
                  or          a7, a6, s0
                  mul         zero, t1, ra
                  sltiu       s4, t3, -868
                  c.add       tp, s3
                  divu        t2, s10, a7
                  c.mv        s8, t1
                  divu        s0, t4, a1
                  lui         gp, 559836
                  mulhsu      a2, s3, t3
                  c.srai      a3, 15
                  xori        zero, tp, -157
                  sll         s8, s4, s1
                  add         t1, a7, s9
                  div         a2, a4, s8
                  addi        t3, a4, 547
                  slti        t2, t1, 587
                  c.addi4spn  a3, sp, 320
                  c.mv        s8, t1
                  mul         s1, s4, a0
                  slli        a0, t6, 18
                  sra         gp, zero, a3
                  c.andi      a3, 11
                  ori         ra, t2, -478
                  lui         s0, 937604
                  srl         a3, s8, sp
                  mul         s5, s3, s8
                  xor         tp, sp, a3
                  srli        a3, s4, 21
                  xor         t2, s8, t1
                  c.sub       a3, a2
                  slli        s8, t0, 4
                  auipc       t3, 704459
                  ori         zero, t3, 641
                  mulhu       t2, a0, t2
                  ori         t3, a6, 1649
                  mul         ra, t3, a1
                  c.or        a3, a3
                  c.or        a3, a3
                  rem         ra, a5, t1
                  xori        s0, s6, -1812
                  mulhsu      a1, a1, s6
                  c.or        a3, a3
                  srli        s4, s5, 30
                  andi        s4, s7, 1556
                  nop
                  xor         t5, s9, a5
                  mul         t1, a7, s3
                  c.and       a0, a3
                  ori         s5, sp, 1343
                  slti        a7, s5, 1953
                  c.andi      a3, 7
                  div         a5, t0, a4
                  ori         zero, t3, 153
                  c.and       a3, a3
                  srl         s1, a5, t0
                  nop
                  c.addi16sp  sp, -16
                  sra         a7, s11, s5
                  ori         s3, s10, -970
                  slti        zero, s4, -1555
                  c.or        a3, a3
                  c.slli      a1, 10
                  c.addi4spn  a3, sp, 832
                  div         s10, s3, a1
                  sltiu       zero, t0, 38
                  c.addi      a6, -1
                  c.add       a6, t3
                  slt         s7, sp, s3
                  c.nop
                  lui         s5, 454188
                  div         a3, t5, s0
                  divu        s9, a3, s6
                  rem         zero, s2, a4
                  rem         s9, t5, a7
                  and         zero, t3, s7
                  slt         t0, a5, a1
                  srai        s1, a4, 7
                  divu        s3, a0, a0
                  srli        s0, s9, 12
                  sltu        s0, a2, s8
                  c.srli      a3, 23
                  slti        t2, s7, -824
                  c.slli      s1, 26
                  mulhsu      gp, t5, a5
                  mulhu       s4, s0, s7
                  rem         gp, a5, ra
                  srli        a4, s4, 31
                  slli        t4, s5, 18
                  sll         s0, s6, t1
                  slt         a7, gp, a4
                  c.addi16sp  sp, 80
                  auipc       t3, 252328
                  addi        a4, t5, 1860
                  slti        zero, s11, -1228
                  c.li        s1, -1
                  and         s8, t5, a1
                  lui         zero, 903416
                  sra         t1, s5, t0
                  divu        a1, s9, a7
                  slt         sp, t6, s11
                  or          s3, a6, t2
                  and         a0, s10, s3
                  c.srai      a3, 16
                  or          s9, t6, t0
                  lui         t4, 830666
                  or          s4, gp, a4
                  c.xor       s0, a3
                  xori        s10, t3, 898
                  mulhsu      a4, s10, t5
                  auipc       s3, 486302
                  and         t4, s10, ra
                  srl         t2, a6, a0
                  sra         t5, t5, s0
                  nop
                  andi        s10, t6, -320
                  sltu        t0, s7, s0
                  nop
                  srai        s5, s1, 26
                  c.andi      a3, -1
                  mulhu       s4, s7, tp
                  c.addi      ra, 1
                  mulh        s10, s8, t0
                  sltiu       a1, a3, -834
                  addi        zero, a3, -685
                  mul         t4, tp, t6
                  div         s0, s11, s2
                  xor         a4, s0, t1
                  c.or        a3, a3
                  add         s4, a2, t5
                  and         s1, a4, t4
                  c.addi4spn  a3, sp, 576
                  mulh        zero, s9, a3
                  auipc       t4, 491908
                  srai        ra, a6, 31
                  nop
                  or          s5, t2, a3
                  andi        t4, a1, -1767
                  or          a4, t3, a0
                  sub         a6, t6, t2
                  sltiu       t3, s3, 964
                  mulhsu      zero, s6, s1
                  c.nop
                  c.xor       a3, a3
                  mulhsu      zero, a5, s3
                  nop
                  c.addi16sp  sp, 160
                  c.addi16sp  sp, 176
                  slli        s2, s0, 23
                  rem         s2, t5, s7
                  lui         s5, 383632
                  or          a2, a4, a5
                  c.andi      a5, -1
                  c.mv        s9, t0
                  c.or        a3, a3
                  rem         tp, s5, a1
                  c.lui       a6, 6
                  c.srai      a3, 6
                  slt         s1, a3, s0
                  xor         a6, a1, t3
                  c.lui       a1, 5
                  and         zero, t6, s5
                  srai        s9, sp, 29
                  c.or        a3, a3
                  c.nop
                  sra         s8, a7, a6
                  addi        s7, t0, 31
                  mul         s0, a3, t3
                  c.mv        s9, sp
                  mulh        t1, s4, a0
                  c.srli      a3, 30
                  div         a3, a2, a1
                  c.li        s5, 16
                  addi        a6, s2, -857
                  sll         t4, s10, s1
                  divu        zero, a0, s3
                  c.slli      a3, 2
                  sub         s3, a1, s11
                  c.li        t3, 4
                  mulhsu      s10, t0, t6
                  nop
                  sltiu       zero, t4, 910
                  sltu        a7, t6, t6
                  c.sub       a3, a0
                  divu        a0, s6, a5
                  mulh        t3, s4, a5
                  c.xor       s0, a3
                  sltu        s7, ra, s3
                  div         a2, a1, s2
                  auipc       tp, 954356
                  sra         s8, s4, s0
                  addi        t4, s2, -1441
                  andi        zero, a1, 455
                  auipc       s4, 149767
                  and         t5, s1, a4
                  c.addi16sp  sp, 128
                  slt         t5, s5, t5
                  mulhsu      s10, sp, s10
                  xori        s7, a1, 1011
                  lui         a7, 531070
                  c.srli      a3, 5
                  sll         a2, t5, s11
                  sub         t4, a0, a0
                  mulh        a0, s3, a3
                  c.add       s3, t6
                  or          t0, a1, s9
                  c.add       s0, a3
                  and         ra, ra, s4
                  c.srli      a3, 13
                  auipc       t3, 18532
                  sltiu       a3, s5, -445
                  c.xor       a3, s0
                  addi        zero, t0, -1915
                  srl         s8, s4, a5
                  divu        a7, s5, a4
                  rem         zero, a4, s0
                  mulhsu      zero, s4, a0
                  mul         a3, s6, t4
                  sra         s5, zero, s11
                  sub         a7, t4, t1
                  addi        s0, s11, -574
                  c.andi      a3, -1
                  nop
                  c.or        a3, a3
                  c.sub       a3, a3
                  and         t2, a4, s9
                  ori         a0, sp, 347
                  andi        a1, s9, -1043
                  mulhu       t3, a2, s10
                  sll         a6, s6, t2
                  c.li        ra, -1
                  c.or        a4, a4
                  sra         t0, s8, zero
                  xor         s10, zero, s6
                  sub         sp, sp, t0
                  sll         s4, s10, a0
                  c.or        a3, a3
                  slti        zero, s10, 135
                  addi        s7, s10, 1426
                  c.addi4spn  a3, sp, 320
                  mul         a3, t4, t0
                  ori         s5, s0, 1388
                  sll         zero, a6, s5
                  c.nop
                  or          zero, t4, s5
                  mulhu       sp, s6, s9
                  c.addi4spn  a3, sp, 384
                  slti        t4, s1, -1646
                  slli        a4, s8, 5
                  c.and       s0, a3
                  mulhu       sp, a3, t6
                  addi        s9, s0, 284
                  divu        zero, t6, a6
                  sub         sp, s7, s9
                  c.sub       a3, a3
                  c.xor       a3, a3
                  mulhu       zero, s8, sp
                  c.li        s9, -1
                  c.addi16sp  sp, 416
                  sll         tp, a5, t0
                  slli        zero, gp, 2
                  srai        s0, s7, 25
                  c.addi4spn  a3, sp, 384
                  andi        a4, t2, -675
                  c.xor       a3, a3
                  sub         t3, a5, a7
                  c.and       a3, a3
                  nop
                  ori         a0, s1, -166
                  c.sub       a3, a3
                  slti        a5, t2, -910
                  c.addi4spn  a2, sp, 928
                  sll         a4, s1, t3
                  xori        s1, s7, 1654
                  c.andi      a3, 22
                  mulhsu      zero, s8, a0
                  c.addi16sp  sp, -16
                  sltiu       s3, s11, -532
                  mul         s7, a1, sp
                  c.nop
                  auipc       s2, 147844
                  c.addi      gp, 31
                  sltiu       s4, s9, 1615
                  xori        t3, s2, 1621
                  c.li        s0, -1
                  c.li        a5, 7
                  or          zero, s3, s11
                  c.and       a4, a3
                  sltiu       a7, gp, 1858
                  srli        a6, s3, 21
                  rem         s9, s1, tp
                  c.slli      s4, 11
                  c.andi      a3, -1
                  slti        t2, s2, -1573
                  add         s3, t0, s7
                  or          a6, s4, gp
                  sltiu       s10, ra, -1262
                  c.srli      a3, 25
                  divu        s0, a1, s9
                  c.srli      a3, 5
                  rem         zero, s6, a2
                  c.sub       a3, a3
                  srli        s7, t2, 17
                  c.lui       s0, 21
                  sub         s7, t4, sp
                  sltu        a7, s2, sp
                  srai        t4, s5, 25
                  c.add       s7, s4
                  nop
                  srai        a1, s2, 20
                  c.srai      a3, 1
                  c.addi4spn  a3, sp, 832
                  nop
                  sltiu       zero, s4, 626
                  mulhu       a0, a2, a1
                  or          t1, a7, ra
                  c.addi4spn  a3, sp, 832
                  divu        t2, a7, t0
                  c.srli      a3, 30
                  c.lui       s2, 16
                  lui         s8, 615701
                  ori         t0, s5, -38
                  c.slli      t0, 29
                  sra         t5, s3, s11
                  c.xor       a3, a4
                  andi        s5, a0, -1934
                  c.mv        t3, a7
                  rem         a4, s10, s5
                  xor         s10, a2, ra
                  mulhu       s1, ra, gp
                  c.sub       a4, a3
                  andi        gp, tp, -1323
                  c.andi      a3, -1
                  rem         a2, a6, sp
                  xor         t2, t1, ra
                  srli        a5, s11, 29
                  c.nop
                  c.addi16sp  sp, -16
                  sltu        a2, s2, s8
                  nop
                  div         zero, s2, t5
                  c.addi      s0, 25
                  addi        zero, a6, 1262
                  c.add       tp, t3
                  sltu        t4, t3, gp
                  mulhu       a1, t6, s1
                  lui         zero, 416483
                  c.addi      a7, -1
                  rem         sp, a3, a6
                  c.lui       a2, 12
                  divu        s7, a4, ra
                  c.mv        s9, s5
                  c.sub       a3, a3
                  slt         s8, a0, sp
                  mulh        gp, a5, s3
                  c.xor       a3, a3
                  c.or        a3, a3
                  rem         a3, s8, a3
                  xori        tp, s1, -946
                  rem         s7, a0, t2
                  srli        t3, t0, 28
                  divu        a6, a1, tp
                  sub         s10, s8, t6
                  sltiu       s2, s4, -1765
                  srli        s5, zero, 30
                  c.slli      t0, 1
                  sltu        s2, s3, t3
                  div         zero, s8, s4
                  addi        zero, s0, 298
                  c.mv        ra, t0
                  c.li        a6, -1
                  sub         a4, s5, t6
                  rem         s10, s4, s0
                  c.nop
                  ori         a3, t3, -1665
                  c.andi      a3, 6
                  srl         s3, tp, s8
                  mulhu       a2, s3, sp
                  sltiu       s8, s6, -207
                  c.addi4spn  a3, sp, 896
                  mulh        t4, s5, a1
                  c.srai      a3, 9
                  slt         a4, t2, s0
                  sltu        a6, a4, sp
                  mulh        s8, s1, a3
                  c.li        tp, -1
                  c.xor       a3, a3
                  lui         s9, 903783
                  c.srai      a3, 16
                  c.slli      a7, 7
                  c.srli      a3, 31
                  div         zero, s0, a5
                  slti        t4, a7, 1037
                  divu        t1, s2, s3
                  c.nop
                  slti        a4, t4, -1550
                  c.srai      a3, 2
                  c.slli      s3, 25
                  addi        s3, t2, -1878
                  srl         t5, gp, s4
                  c.srli      a3, 19
                  addi        a1, a7, -80
                  c.sub       a3, a3
                  nop
                  mulh        s0, s8, s4
                  c.addi4spn  s0, sp, 960
                  sub         a1, a6, t5
                  c.mv        s8, t6
                  slli        s10, tp, 20
                  c.and       a3, a3
                  addi        a3, t3, -1363
                  sub         a5, a5, s3
                  sltu        a5, t4, t2
                  or          a3, tp, gp
                  and         t0, s10, t0
                  srli        t0, s10, 28
                  sltiu       t5, a6, 1966
                  srli        a0, a5, 13
                  c.slli      s0, 17
                  c.addi16sp  sp, 272
                  xori        tp, a0, 1477
                  addi        a6, sp, 551
                  c.add       t5, s8
                  mulhsu      t2, a7, ra
                  sltu        s3, s5, tp
                  slli        s5, s0, 0
                  divu        zero, a4, s10
                  slti        s0, tp, -1869
                  divu        s9, s7, t2
                  c.nop
                  rem         s1, a7, t1
                  addi        t1, s4, -1636
                  divu        s2, t4, zero
                  nop
                  c.andi      a3, 5
                  c.andi      a3, 30
                  addi        a2, gp, 455
                  c.addi      t4, -1
                  srl         s10, zero, t1
                  c.sub       a3, a3
                  slti        tp, s4, -1513
                  c.and       a3, a3
                  mulhu       a1, tp, tp
                  c.lui       ra, 25
                  auipc       a7, 941052
                  c.srli      a3, 28
                  sll         a3, s9, s9
                  c.andi      a3, -1
                  c.sub       a3, a3
                  srl         t0, gp, s1
                  srli        s0, a7, 10
                  lui         s10, 205479
                  lui         t0, 668547
                  srai        t5, s2, 15
                  c.and       s1, a3
                  c.and       a3, s1
                  andi        t1, a6, 288
                  rem         s7, t2, a4
                  c.andi      a2, 14
                  sltiu       t0, a4, -1592
                  c.li        a2, 22
                  xori        t2, a2, 113
                  c.andi      a3, 9
                  sll         a4, t3, s1
                  and         s1, s6, s6
                  nop
                  c.andi      a3, 15
                  nop
                  slli        a1, s0, 22
                  slt         zero, gp, t4
                  auipc       zero, 415618
                  c.add       a7, a6
                  c.addi16sp  sp, 480
                  slt         t5, a5, s8
                  slti        zero, t5, -1164
                  slt         a3, sp, t3
                  sub         a6, a7, s7
                  srl         tp, s2, t5
                  srli        t4, t6, 17
                  and         sp, s11, s10
                  ori         s3, t0, -806
                  c.andi      a2, -1
                  sltiu       tp, tp, 585
                  mulh        s8, zero, t1
                  nop
                  c.and       a3, a3
                  c.add       a1, ra
                  sltu        t4, s8, t6
                  addi        zero, t6, -686
                  mulhu       t3, ra, t1
                  slti        ra, a5, 685
                  c.lui       t2, 13
                  xori        s0, t6, -1371
                  nop
                  c.nop
                  or          zero, a5, gp
                  c.slli      sp, 11
                  or          s9, s6, s9
                  c.nop
                  c.addi16sp  sp, -16
                  divu        a5, gp, t5
                  srai        a6, sp, 20
                  addi        zero, s10, -1969
                  slli        zero, a5, 17
                  mulhsu      s10, s9, ra
                  auipc       tp, 154605
                  slli        a7, a0, 18
                  add         a5, ra, a7
                  andi        gp, s1, -1451
                  mulhsu      s1, a5, t4
                  c.srli      a3, 23
                  lui         tp, 786038
                  c.addi16sp  sp, 320
                  c.addi      ra, -1
                  c.or        s1, a3
                  divu        zero, t2, s3
                  add         s8, s9, s5
                  divu        ra, a7, t6
                  slti        t4, t3, -953
                  sll         t0, s3, t4
                  c.or        a1, s1
                  c.srai      a3, 8
                  slti        gp, sp, 1742
                  c.mv        t5, ra
                  sub         s9, t3, zero
                  c.addi4spn  a3, sp, 960
                  sltu        a1, a6, tp
                  c.li        s3, 2
                  xori        a6, t3, 1058
                  c.slli      s10, 19
                  sub         a3, a1, t0
                  c.addi16sp  sp, 304
                  c.xor       a3, a3
                  c.slli      s9, 16
                  c.and       a3, a3
                  c.xor       a1, a3
                  add         a1, s3, tp
                  rem         s1, s6, s11
                  c.nop
                  srli        t0, a5, 5
                  c.srli      a2, 24
                  and         s0, a0, a0
                  andi        a3, zero, -1918
                  sltu        sp, sp, a7
                  c.slli      a6, 27
                  ori         s0, tp, 734
                  c.sub       a1, a3
                  c.andi      a3, -1
                  c.add       sp, gp
                  mulhsu      t5, s11, a0
                  mulhu       a0, t2, t4
                  nop
                  divu        s9, a4, s1
                  srl         ra, gp, zero
                  sll         t1, a1, t1
                  c.slli      a3, 24
                  c.srli      a4, 21
                  or          t1, a7, t5
                  c.or        a3, a4
                  auipc       t0, 698490
                  sll         s7, s0, ra
                  or          zero, t3, a6
                  li         t5, 0x0 #start riscv_int_numeric_corner_stream_1
                  li         t4, 0x0
                  li         t0, 0x0
                  li         t3, 0x3dabc8d0
                  li         s4, 0x68441e24
                  li         a2, 0x0
                  li         s10, 0x150c9b9c
                  li         a1, 0x0
                  li         a3, 0x0
                  li         s9, 0x5ec60c35
                  c.mv        s5, s6
                  c.lui       t5, 24
                  c.addi      a1, -1
                  c.add       a4, a6
                  divu        s2, a3, t4
                  mulhu       zero, s6, t4
                  add         s8, t1, sp
                  lui         t2, 876360
                  addi        t1, a0, -725
                  c.mv        ra, s10
                  sub         s9, a0, a4
                  addi        s0, s2, 1130
                  c.nop
                  mulh        a2, gp, s7
                  mul         a2, s9, a5
                  c.addi16sp  sp, -16
                  mulhsu      s9, s5, a3
                  divu        s8, t4, a1
                  mulhsu      tp, a2, s6
                  c.li        a3, -1
                  c.addi4spn  a3, sp, 896
                  mul         a7, a2, s6
                  divu        gp, s2, a1
                  addi        zero, t1, 779
                  c.addi4spn  a3, sp, 448
                  c.add       a5, s4
                  mulhu       a4, a5, t2
                  or          zero, t0, s10
                  c.mv        t0, s3
                  addi        a7, s1, 36
                  addi        sp, a6, -1575
                  ori         s9, t2, 143
                  c.addi      a0, 4
                  srli        tp, s11, 0
                  div         t2, tp, t1
                  rem         s2, s0, s8
                  mulhu       zero, ra, t1
                  xor         s9, s1, t1
                  c.addi      ra, 15
                  slti        zero, a7, 1687
                  ori         zero, a2, 1035
                  srl         zero, s3, t1
                  sra         s5, a2, t5
                  and         s5, s10, s1
                  auipc       a2, 464748
                  c.srli      a3, 14
                  c.andi      a3, 4
                  auipc       s10, 226313
                  mul         a6, t0, s9
                  nop
                  xori        s5, a0, -107
                  div         gp, s11, t6
                  slti        a4, t5, -2020
                  c.mv        ra, s8
                  slti        zero, s10, -800
                  c.addi16sp  sp, 304
                  c.addi16sp  sp, -16
                  sub         a5, zero, zero
                  c.li        s8, -1
                  c.and       a3, a3
                  or          t0, t2, s6
                  c.or        a3, a3
                  div         t0, a4, a2
                  sll         a7, t3, s2
                  sub         a4, s9, a5
                  addi        s7, s0, -1283
                  c.add       s0, a0
                  xori        t0, s11, -675
                  sll         zero, sp, t5
                  c.add       t2, sp
                  srli        s5, t0, 14
                  and         zero, a5, sp
                  slt         s7, gp, a0
                  c.add       s9, a4
                  c.sub       a2, a3
                  c.mv        s2, s0
                  rem         t2, s7, t1
                  or          t5, a0, s4
                  div         t4, s7, s8
                  slti        a0, a3, -389
                  c.slli      sp, 18
                  c.li        t5, 0
                  andi        sp, s9, -1668
                  srli        s9, t1, 13
                  c.and       a3, a3
                  sltu        s1, s6, a6
                  slti        s8, a7, -474
                  sll         s10, a7, sp
                  sub         t5, ra, s0
                  nop
                  c.mv        ra, s10
                  add         a5, a1, a5
                  sub         s5, a2, a7
                  c.slli      s8, 25
                  slti        s2, s4, -1306
                  divu        a1, a2, zero
                  c.li        sp, 31
                  sll         s5, s5, t2
                  slli        a6, s2, 3
                  and         s7, s2, ra
                  c.nop
                  slt         zero, zero, s0
                  c.xor       a3, a4
                  c.mv        gp, ra
                  c.addi      a7, 10
                  c.mv        t5, t5
                  slt         a6, s0, s9
                  mul         s8, s7, t4
                  c.slli      a1, 23
                  c.nop
                  c.add       s5, s8
                  nop
                  slt         a1, t0, a6
                  slti        a1, s6, 1312
                  srli        s10, t2, 25
                  c.add       ra, t5
                  auipc       t0, 762153
                  c.mv        t3, s3
                  c.or        a2, s1
                  xori        s0, t3, -567
                  srli        a3, s0, 15
                  mul         a7, s1, s7
                  mulhu       gp, s7, s3
                  rem         sp, s4, gp
                  li         tp, 0x1 #start riscv_int_numeric_corner_stream_10
                  li         t5, 0x1
                  li         t4, 0x0
                  li         gp, 0x0
                  li         t3, 0x0
                  li         s9, 0x4f054ce4
                  li         s10, 0x1
                  li         a2, 0x663251b3
                  li         a3, 0x1
                  li         ra, 0x19fa184
                  auipc       t2, 983451
                  c.addi      t1, -1
                  mulhu       t1, s4, t0
                  c.addi      ra, 1
                  auipc       s0, 116226
                  sub         zero, s7, gp
                  c.nop
                  addi        a5, t4, -1672
                  c.li        ra, -1
                  c.li        s9, 17
                  mul         s3, t4, tp
                  sub         s3, tp, zero
                  c.addi16sp  sp, 352
                  c.sub       a3, a3
                  mul         ra, s1, s11
                  c.addi16sp  sp, -16
                  auipc       s4, 840733
                  mulhu       a5, a7, s6
                  c.addi16sp  sp, -16
                  c.addi16sp  sp, -16
                  addi        s1, a6, -1713
                  c.addi      ra, -1
                  c.nop
                  c.sub       a3, a3
                  mulhu       s9, t4, t5
                  sltiu       a6, s8, -630
                  slt         zero, s7, a2
                  rem         t3, s3, s5
                  c.add       t3, s3
                  srli        sp, t4, 10
                  sll         s7, t0, sp
                  sra         sp, t2, s9
                  ori         s4, t6, 1386
                  c.and       a4, s1
                  add         t4, a6, s11
                  and         s4, s0, t0
                  nop
                  mul         s3, t1, a0
                  c.srai      a3, 18
                  addi        s10, s3, 1471
                  c.xor       a3, a3
                  divu        tp, a3, a0
                  and         s9, tp, t6
                  c.mv        tp, s8
                  auipc       zero, 1023242
                  sub         t1, gp, a6
                  c.addi4spn  a3, sp, 832
                  c.and       a3, a3
                  nop
                  c.sub       a4, a3
                  c.nop
                  sll         s7, s7, tp
                  xori        zero, ra, 306
                  sra         t0, s0, a0
                  c.or        a3, a3
                  addi        ra, s8, -1173
                  div         t2, t2, tp
                  sltu        a4, sp, a5
                  c.addi4spn  a3, sp, 336
                  c.and       a3, s1
                  c.and       a3, a3
                  c.srai      a4, 14
                  add         zero, a5, a0
                  c.nop
                  c.or        a3, a3
                  add         t3, s8, t5
                  xori        zero, t1, -595
                  c.slli      s2, 12
                  sub         a6, s6, sp
                  mulh        t3, a0, t3
                  div         s1, a5, s1
                  xor         t4, a4, s6
                  slt         s5, a5, s4
                  mulhsu      s7, t6, zero
                  mulhsu      s7, a0, t6
                  div         t4, t6, t6
                  addi        t3, a5, 289
                  c.srli      a2, 16
                  divu        s7, a2, a4
                  sll         s1, s3, s5
                  c.add       ra, t5
                  rem         t2, t0, tp
                  xori        t4, s10, -1374
                  sra         s5, ra, a6
                  c.and       a1, s1
                  xori        a7, s7, -539
                  andi        s1, t4, -550
                  and         a0, t4, sp
                  div         zero, a6, t2
                  slti        s9, a6, -1811
                  c.slli      a4, 6
                  nop
                  slti        zero, s10, 105
                  slti        s0, a4, -1817
                  c.xor       a0, a3
                  addi        zero, t6, -1305
                  srai        t4, s11, 7
                  mulhsu      s3, s7, a0
                  c.add       ra, ra
                  sltiu       s2, s3, 1159
                  mul         a5, a3, a3
                  c.mv        a6, ra
                  c.slli      s8, 26
                  nop
                  srl         sp, a4, t6
                  nop
                  divu        tp, t6, s6
                  lui         ra, 813726
                  slt         s0, t2, a3
                  xori        s3, a7, 860
                  c.or        a3, a5
                  xor         zero, zero, t3
                  slli        s4, a4, 31
                  slt         zero, t6, a3
                  ori         s4, s10, 507
                  xori        s3, s11, -831
                  srl         a1, s9, t1
                  c.mv        a7, s11
                  slti        a6, ra, 1198
                  sltu        s3, tp, tp
                  ori         s2, s11, -523
                  rem         t2, a6, s10
                  c.srli      a5, 11
                  div         t5, s9, a4
                  c.srai      a3, 20
                  c.andi      a3, -1
                  or          a3, zero, s8
                  c.lui       a2, 25
                  c.addi      t3, 5
                  c.srai      a3, 4
                  ori         s10, s9, -1589
                  srli        a1, s8, 27
                  andi        a7, s10, -241
                  c.andi      a2, -1
                  xori        a1, t5, -57
                  add         s0, s4, a1
                  xori        zero, a7, 63
                  sltu        s9, t2, s8
                  lui         s1, 796427
                  slti        zero, a1, -729
                  srl         s3, a5, s2
                  and         a7, ra, s5
                  c.addi      s3, -1
                  sltiu       t1, s1, -842
                  c.andi      a3, -1
                  sra         zero, s2, s3
                  c.and       a3, a3
                  mul         t0, tp, s6
                  div         s7, zero, a0
                  add         t5, t5, a2
                  andi        ra, t6, -1515
                  mulhsu      s2, s10, s8
                  srl         s9, s1, gp
                  add         a6, s3, s9
                  c.and       a0, a4
                  div         zero, s11, s6
                  or          t0, a6, s9
                  c.andi      a3, 9
                  nop
                  div         s7, a0, a1
                  ori         tp, a0, -1338
                  c.xor       a3, a2
                  c.xor       a3, a1
                  slti        a2, s1, 439
                  xor         a6, a0, s9
                  c.srli      a3, 20
                  c.srai      a3, 7
                  c.slli      a1, 6
                  c.addi      ra, -1
                  xori        a2, t3, -279
                  divu        a0, t5, t1
                  addi        s5, t6, 988
                  c.lui       t3, 27
                  and         s9, t0, a7
                  xor         s8, a2, s11
                  rem         a4, t2, s1
                  c.and       a3, a1
                  div         tp, ra, s9
                  c.addi16sp  sp, -16
                  c.nop
                  add         tp, a0, a4
                  c.li        a5, 11
                  c.mv        s7, s10
                  xori        s10, a6, -1497
                  slli        zero, a3, 4
                  c.li        s4, 23
                  divu        zero, t6, s3
                  c.and       a3, a3
                  slt         sp, t4, a3
                  slli        a5, t4, 9
                  sltiu       a0, s6, 925
                  c.or        a3, a3
                  ori         s0, s1, 1145
                  ori         s0, t2, 963
                  c.addi16sp  sp, 288
                  c.lui       t2, 24
                  divu        zero, s1, s10
                  andi        a4, sp, -1309
                  c.srai      a3, 22
                  srl         s0, t0, s7
                  nop
                  sub         a2, s10, s7
                  sub         a5, s3, t2
                  slt         s4, t1, s2
                  mulh        t5, s8, sp
                  auipc       a0, 306012
                  c.lui       s3, 10
                  slli        a3, a0, 26
                  add         s2, s11, s1
                  xori        t0, sp, -30
                  and         s1, t4, s6
                  and         s2, s4, t5
                  c.addi      t0, 30
                  nop
                  c.srai      a3, 27
                  c.addi4spn  a3, sp, 576
                  c.sub       a3, a3
                  mulhu       a2, a2, ra
                  c.sub       a3, a3
                  sll         a7, a4, s9
                  c.addi4spn  a3, sp, 128
                  slli        a4, a1, 30
                  c.or        a3, a1
                  c.li        a1, 5
                  c.sub       a0, a2
                  c.sub       a3, a2
                  c.addi4spn  a3, sp, 64
                  sra         t0, a3, a0
                  c.addi4spn  a3, sp, 352
                  nop
                  srai        sp, s5, 30
                  sub         t2, a0, t4
                  mulhu       s1, s3, s4
                  ori         a1, t2, 1994
                  rem         t0, a0, gp
                  and         t3, t5, s7
                  c.addi      s0, -1
                  or          sp, a3, zero
                  slt         a3, a2, t1
                  mulh        s1, s4, t4
                  mulh        s4, a6, s8
                  mulhu       s8, s1, a5
                  mul         s7, sp, s0
                  mul         a7, s1, a1
                  c.and       a2, a1
                  c.nop
                  divu        a2, t1, gp
                  xori        s2, s5, -1903
                  c.and       a3, a3
                  c.nop
                  slli        zero, s4, 28
                  add         a5, s3, a5
                  auipc       a4, 319774
                  or          t3, s3, t4
                  or          a3, s0, sp
                  c.li        s8, 3
                  srl         a3, a1, a4
                  and         gp, s3, s4
                  addi        zero, s6, -1553
                  slti        s2, a1, 232
                  srli        a0, s7, 24
                  c.sub       a4, a0
                  sub         zero, ra, a0
                  sub         s9, t0, t5
                  srl         gp, a6, s8
                  sltiu       s7, a5, 802
                  c.and       a3, a3
                  mulh        t2, t0, s1
                  lui         t1, 909576
                  srai        a2, s5, 2
                  add         s10, t2, sp
                  c.lui       a1, 30
                  mul         s2, tp, sp
                  and         a4, s5, t2
                  c.addi16sp  sp, 16
                  nop
                  c.srai      a3, 11
                  divu        zero, t6, a6
                  c.srli      a3, 20
                  sltiu       ra, s7, -1836
                  c.lui       t4, 13
                  c.slli      t0, 4
                  auipc       a2, 194711
                  c.and       a3, a3
                  xor         s9, t1, t3
                  srl         s9, s6, s6
                  mulh        a0, s6, s4
                  srl         s8, t2, s10
                  lui         t1, 779554
                  mulhsu      s1, t6, a4
                  c.lui       tp, 28
                  slli        s10, s7, 29
                  c.xor       a0, a3
                  mulhu       s9, t2, s8
                  slt         s8, a2, s5
                  sub         s10, a0, s11
                  c.andi      a1, -1
                  srli        s10, tp, 13
                  xori        s7, t2, 1087
                  srl         s5, a6, a4
                  mulhu       a5, gp, s0
                  c.addi16sp  sp, -16
                  sltu        zero, s8, gp
                  sra         a6, a2, s5
                  add         zero, t1, ra
                  sltiu       s5, t3, 291
                  c.li        a2, 26
                  c.addi16sp  sp, 48
                  lui         s5, 753460
                  xori        s2, s4, 505
                  sltu        s7, t5, sp
                  srai        s3, ra, 6
                  srl         s10, t0, tp
                  or          ra, s8, a5
                  sub         t0, a6, a2
                  c.addi4spn  a3, sp, 848
                  c.srli      a3, 3
                  rem         t1, s7, t2
                  xor         t1, a6, t3
                  c.nop
                  c.xor       a3, a3
                  mulhu       s9, gp, s2
                  mul         s7, tp, t0
                  xori        ra, t0, 889
                  divu        s3, s8, tp
                  sltu        zero, sp, a4
                  addi        s1, t4, 926
                  xor         s10, tp, s9
                  divu        s2, a3, t2
                  c.srli      a3, 29
                  addi        sp, a3, -530
                  srli        s2, s6, 30
                  mulh        s5, ra, t6
                  srai        a4, sp, 17
                  sltu        s2, t2, s9
                  c.li        t3, -1
                  srli        t1, s4, 17
                  div         a6, a0, t0
                  c.srli      a3, 21
                  c.sub       a3, a3
                  auipc       zero, 866179
                  c.lui       ra, 23
                  mulh        s9, a6, a6
                  xori        a1, s4, 1293
                  and         a3, a2, s8
                  ori         t2, t5, 2014
                  c.srli      a1, 25
                  srl         a0, s7, t6
                  and         s0, s10, t0
                  c.lui       ra, 23
                  andi        a1, s8, -359
                  slt         a1, s8, gp
                  mulh        s7, gp, s0
                  c.addi4spn  a3, sp, 128
                  sra         a0, a3, s7
                  slti        tp, gp, -1164
                  c.xor       a3, a0
                  c.addi16sp  sp, 240
                  c.add       t3, a1
                  c.xor       a1, a3
                  mulhsu      t5, s0, tp
                  mulhu       t3, s5, t5
                  slti        a2, s10, 230
                  addi        s4, t1, -837
                  c.addi      t3, -1
                  mulhsu      t3, s0, a1
                  slli        sp, s5, 3
                  slt         t4, s10, zero
                  add         s2, t0, s10
                  add         a2, s3, s4
                  c.addi4spn  a3, sp, 128
                  sra         zero, s11, s10
                  mulh        t2, s2, zero
                  srl         a4, a3, s4
                  c.lui       ra, 1
                  sltiu       s10, a1, -1317
                  xori        t5, a6, -208
                  c.slli      s7, 20
                  rem         s10, s10, a4
                  c.addi4spn  a3, sp, 576
                  mulh        zero, a1, tp
                  srai        s5, t3, 13
                  sub         gp, s3, t1
                  c.xor       a3, a3
                  c.mv        a7, ra
                  c.srli      a0, 20
                  sub         sp, s8, a6
                  ori         a0, tp, -746
                  srl         a1, t4, t3
                  srai        t3, a4, 25
                  auipc       s8, 676631
                  rem         a6, s11, t4
                  mulh        s7, a0, t4
                  c.andi      a3, 30
                  slli        s5, s3, 1
                  mulhsu      t3, ra, a1
                  c.or        a3, a3
                  add         a7, s1, s6
                  or          sp, a2, t1
                  c.slli      sp, 17
                  sltiu       a0, s6, 1698
                  and         t0, t5, t5
                  slli        t2, t1, 3
                  c.xor       a2, s0
                  or          t0, s5, t3
                  c.nop
                  andi        a0, t2, -1882
                  sltiu       t4, a1, -881
                  div         a1, a4, t2
                  c.nop
                  sltu        s7, s4, a4
                  c.xor       a3, a3
                  xor         t4, s1, a3
                  srli        s9, sp, 16
                  c.or        a3, a3
                  sub         a3, t2, t4
                  slti        zero, a3, -2037
                  srl         s8, s9, sp
                  c.addi4spn  a3, sp, 640
                  sltu        gp, t5, s7
                  c.nop
                  c.srli      a3, 22
                  lui         t1, 979212
                  c.andi      a3, 5
                  mulh        sp, t0, s11
                  srl         zero, s11, a1
                  slli        t5, s4, 17
                  mul         s2, s8, a2
                  c.addi4spn  a0, sp, 128
                  mul         t2, t1, s1
                  c.addi4spn  a3, sp, 608
                  c.sub       a3, s0
                  sub         a7, tp, s11
                  c.andi      a3, -1
                  c.lui       t4, 21
                  or          s4, a5, tp
                  srl         s7, t6, s1
                  mulhu       a6, a4, s7
                  sltiu       a6, a1, 621
                  srli        zero, a1, 14
                  c.and       s1, a3
                  addi        s4, zero, -1734
                  mul         gp, s11, s3
                  or          a0, s9, t6
                  rem         t3, a0, a1
                  lui         t1, 521457
                  slti        t4, s6, 1652
                  c.srai      a3, 21
                  c.add       s5, a5
                  sll         s1, t1, tp
                  c.lui       t2, 16
                  div         a2, t6, a1
                  srl         t3, a4, t3
                  lui         s2, 154245
                  c.andi      a3, -1
                  sub         s5, s7, a3
                  sltu        zero, gp, t3
                  mulh        a0, t4, s0
                  c.srli      a1, 17
                  and         s0, s9, t2
                  sll         s4, s6, t2
                  c.lui       s7, 14
                  mul         a7, s2, a7
                  c.addi16sp  sp, -16
                  c.nop
                  c.andi      a3, 23
                  nop
                  auipc       t5, 664998
                  sltu        a4, gp, s5
                  mulhsu      s2, t0, s2
                  sltu        s10, a6, t0
                  c.li        s3, -1
                  c.or        a3, a3
                  c.add       ra, s4
                  mulhu       s3, t5, zero
                  c.andi      a3, -1
                  srli        t5, t3, 15
                  c.lui       s3, 15
                  c.srli      a3, 21
                  slt         a0, a5, s9
                  sll         a4, ra, a0
                  and         sp, s0, t5
                  srl         a2, s0, s0
                  div         s7, a1, s4
                  sll         a2, gp, gp
                  sub         a5, s2, a5
                  slli        t1, t3, 28
                  divu        s5, t1, s2
                  add         t4, a7, gp
                  sltiu       a1, s6, 1667
                  ori         zero, a0, -1897
                  sub         s7, s2, t1
                  c.lui       ra, 7
                  divu        zero, s6, s6
                  c.lui       ra, 4
                  sub         a2, t3, a2
                  sra         sp, t6, ra
                  c.nop
                  srai        s7, s8, 14
                  rem         s9, a4, a4
                  mul         sp, s4, a4
                  c.addi4spn  a3, sp, 704
                  rem         s1, a5, gp
                  nop
                  c.lui       s1, 4
                  slt         s9, s2, tp
                  c.srai      a4, 13
                  divu        s9, t3, s8
                  c.sub       a3, a3
                  add         t2, a2, t4
                  lui         a1, 712849
                  mul         s2, t4, s11
                  c.srai      a3, 21
                  and         a5, a7, t4
                  mulh        t2, s6, s10
                  nop
                  sra         s1, s4, s1
                  c.add       a6, s3
                  rem         gp, tp, a7
                  add         ra, a1, a4
                  slli        s2, s4, 11
                  c.lui       ra, 15
                  c.andi      a3, -1
                  addi        s9, s6, -497
                  c.addi16sp  sp, -16
                  c.addi16sp  sp, -16
                  srli        a4, ra, 14
                  mulhsu      t3, a7, t6
                  c.mv        s8, t4
                  c.xor       a3, a3
                  slt         zero, a1, s2
                  c.mv        t2, t4
                  c.andi      a3, 5
                  c.or        a2, a3
                  lui         zero, 558755
                  c.srai      a1, 1
                  add         t0, tp, s9
                  c.lui       a4, 16
                  c.add       a5, s11
                  c.srai      a3, 24
                  srl         a3, s8, s6
                  c.addi      t5, -1
                  nop
                  add         s5, a7, s8
                  sra         zero, a3, t3
                  lui         a0, 301102
                  c.li        a2, 7
                  sltu        s3, t1, s11
                  slti        s9, s8, -2037
                  mulhu       s8, zero, s8
                  div         a1, a2, s9
                  c.li        sp, -1
                  c.addi16sp  sp, -16
                  xor         a7, t5, t2
                  c.addi4spn  a3, sp, 832
                  mulh        t2, a3, gp
                  divu        t1, t3, t2
                  mulhu       s0, t3, s8
                  c.mv        t5, a7
                  c.srai      a3, 22
                  ori         t5, t2, -1938
                  srai        a1, s7, 4
                  or          s0, s10, s4
                  slli        tp, t1, 12
                  srli        s0, s9, 4
                  slli        a1, s6, 16
                  c.xor       a3, a1
                  c.addi      tp, 19
                  c.li        t3, -1
                  c.lui       s5, 28
                  c.addi4spn  a3, sp, 64
                  or          s4, sp, s11
                  auipc       zero, 86602
                  lui         a1, 214425
                  c.addi4spn  s1, sp, 64
                  add         a2, s0, gp
                  c.add       s9, sp
                  c.srai      a3, 19
                  div         zero, t2, s2
                  mulhu       a4, s11, t2
                  c.andi      a3, 11
                  sub         sp, a7, s10
                  ori         a7, a5, 1842
                  c.andi      a3, 24
                  c.andi      a3, -1
                  c.andi      a3, 16
                  and         gp, a3, t2
                  c.srli      a3, 27
                  c.lui       a4, 12
                  mulh        a5, t1, a2
                  c.srli      a3, 19
                  slli        sp, t1, 8
                  sltiu       zero, sp, 1799
                  addi        s3, t3, 185
                  mul         t0, t6, s10
                  sub         s0, a3, s7
                  c.slli      a7, 14
                  c.addi4spn  a3, sp, 704
                  c.addi4spn  a3, sp, 384
                  or          sp, sp, s8
                  div         s9, a6, a0
                  c.add       s2, s4
                  srli        ra, a6, 28
                  nop
                  c.li        t2, -1
                  andi        s5, t4, -192
                  srl         s10, tp, t6
                  c.and       a3, a3
                  sub         zero, a1, sp
                  c.addi4spn  s0, sp, 896
                  slli        s3, a4, 16
                  mul         s2, s4, t4
                  srl         s2, sp, s3
                  c.srli      a3, 2
                  sltu        s9, zero, s1
                  c.srli      a3, 31
                  c.srli      a0, 10
                  sub         zero, a7, a5
                  c.srai      a3, 5
                  addi        s9, s11, -1871
                  xori        t4, t0, -1160
                  c.mv        a5, s9
                  c.xor       a3, a3
                  sra         tp, s8, s0
                  xori        a4, sp, -1440
                  div         zero, s11, a4
                  lui         s7, 625634
                  mulhsu      s9, ra, tp
                  slli        a4, a3, 30
                  or          t1, zero, ra
                  auipc       t1, 532167
                  divu        t1, t6, a2
                  c.lui       a0, 2
                  mulhu       a5, t1, s0
                  rem         zero, tp, s5
                  c.mv        ra, a6
                  c.srai      a3, 27
                  ori         gp, a3, 1818
                  sub         t0, a3, t3
                  mulhu       t0, s10, s2
                  lui         s5, 389319
                  mulhsu      s3, s4, t5
                  mulhu       t1, s9, s2
                  add         a7, t2, s2
                  or          a4, a5, s4
                  ori         a6, a4, -43
                  div         zero, s4, s0
                  addi        t4, t2, 777
                  srai        t0, t6, 26
                  c.xor       a3, a3
                  c.srli      a3, 20
                  or          t4, t5, a2
                  add         zero, s0, s10
                  ori         t5, s10, 1838
                  sltiu       ra, s9, 418
                  srl         a5, zero, s6
                  slli        zero, s1, 14
                  xori        t0, s7, 254
                  or          zero, ra, s7
                  c.addi4spn  a3, sp, 576
                  ori         s4, t3, -1303
                  mulhu       zero, s2, gp
                  xori        a2, zero, -29
                  c.slli      t1, 1
                  divu        t0, a1, s5
                  c.sub       a3, a2
                  srl         t2, t4, t0
                  c.xor       a3, a2
                  or          s4, t5, zero
                  lui         s7, 326756
                  sltu        s4, t5, s4
                  and         zero, s9, s10
                  c.nop
                  srl         zero, s5, a0
                  c.mv        t5, s2
                  c.lui       ra, 1
                  slli        zero, tp, 4
                  sltu        tp, a7, zero
                  rem         s8, t4, sp
                  sll         a4, t6, a3
                  srli        t1, s10, 29
                  mulh        a4, sp, t1
                  or          s9, t5, ra
                  c.xor       a3, a3
                  slli        t0, s5, 30
                  slt         s9, a7, a3
                  mulh        s2, t4, s5
                  ori         t1, t4, -83
                  srl         t2, t4, s0
                  c.mv        a5, s1
                  c.sub       a3, a3
                  mul         sp, zero, s4
                  c.lui       t5, 21
                  c.addi4spn  a3, sp, 576
                  lui         s4, 700430
                  mul         ra, a6, s2
                  add         t3, s3, gp
                  c.and       a3, a3
                  divu        t5, sp, t6
                  c.srai      a3, 3
                  xori        t3, a4, 1237
                  sub         s3, a1, s2
                  c.li        t2, -1
                  sltiu       a5, s3, -719
                  sltu        zero, s7, t2
                  slli        zero, s10, 7
                  sltiu       s5, t6, 882
                  mulhu       a4, s1, ra
                  sltu        a3, s3, gp
                  c.or        a1, a3
                  sra         s9, t1, t6
                  andi        a1, a5, -219
                  sub         a0, s3, s1
                  slli        a7, s5, 2
                  slt         t1, s2, t1
                  ori         a3, s10, 879
                  c.nop
                  xori        a1, s2, 1521
                  andi        a7, s9, -251
                  c.mv        s9, s4
                  andi        ra, tp, 160
                  lui         a6, 172330
                  mulhsu      zero, a2, s10
                  ori         s5, a2, -40
                  slti        a2, t2, 1718
                  div         zero, t4, s3
                  c.andi      a3, -1
                  xori        gp, s4, -169
                  c.addi16sp  sp, -16
                  mul         ra, s11, a1
                  c.xor       a3, a0
                  mulhsu      s10, zero, zero
                  nop
                  c.addi      t5, 22
                  c.sub       a3, a3
                  c.lui       t2, 18
                  c.add       t1, s5
                  slti        s0, s4, 36
                  sll         tp, a0, s5
                  and         t4, a3, t0
                  or          a0, s10, s0
                  mulhu       t3, s4, t4
                  auipc       zero, 909431
                  slt         zero, s11, zero
                  c.and       a3, a3
                  or          sp, s6, t5
                  c.li        ra, -1
                  xor         s7, ra, s3
                  c.li        ra, 7
                  c.sub       a3, a3
                  sll         sp, a6, s10
                  c.addi16sp  sp, -16
                  c.andi      a5, 9
                  and         s9, a5, s8
                  c.add       t4, a4
                  sltiu       zero, tp, 1393
                  auipc       s8, 7527
                  and         t1, a2, s5
                  c.nop
                  rem         s1, t6, s7
                  mul         t2, s11, s10
                  and         zero, a1, t6
                  mulhu       a0, t3, a1
                  srl         s5, s7, s8
                  lui         t2, 192485
                  c.xor       a0, a3
                  andi        a4, a7, 939
                  c.addi4spn  s1, sp, 896
                  c.sub       s0, a3
                  slti        a3, a4, 170
                  c.addi      ra, 18
                  or          zero, zero, t0
                  c.addi      t2, 25
                  c.andi      a3, -1
                  sra         zero, s2, s8
                  sra         a4, s8, t3
                  c.addi      s8, -1
                  c.sub       a3, a0
                  mulh        zero, s10, t6
                  xor         a3, ra, s1
                  sll         a5, t1, t6
                  sltu        s0, sp, t1
                  c.sub       s1, a4
                  c.srai      a3, 12
                  xor         t2, s6, s5
                  c.addi16sp  sp, -16
                  srai        t2, s3, 16
                  sra         s10, a3, s2
                  srai        s2, s11, 31
                  c.add       t2, tp
                  or          a3, t0, tp
                  mul         s10, a1, a2
                  nop
                  div         tp, t1, a7
                  mul         zero, a1, t6
                  sll         t4, s1, t2
                  or          sp, gp, tp
                  c.srai      a3, 8
                  c.addi      t1, 4
                  c.add       t5, s8
                  c.nop
                  c.xor       a1, a3
                  c.srai      a3, 28
                  c.addi      ra, -1
                  sll         zero, a7, s6
                  auipc       zero, 1007555
                  c.xor       a3, a3
                  sub         a7, a4, s2
                  add         t5, s11, t5
                  mulh        t3, s4, ra
                  c.or        a3, a3
                  slt         t1, tp, t0
                  mulh        a4, t4, s6
                  mulhu       zero, s5, t2
                  c.mv        s5, t4
                  xori        s1, t4, -370
                  sltiu       a2, s9, -1949
                  xor         sp, gp, t3
                  c.andi      a3, 19
                  andi        s7, gp, 1464
                  sltu        sp, s0, t0
                  c.sub       a3, s0
                  lui         a3, 554436
                  or          s2, t6, s3
                  c.nop
                  add         a1, zero, t3
                  mulhsu      t4, a5, a3
                  xori        ra, s3, 1208
                  c.srai      a3, 25
                  rem         zero, ra, ra
                  c.addi      s2, 11
                  slli        a3, a2, 5
                  c.addi4spn  a4, sp, 352
                  mulh        a6, t2, zero
                  srai        t1, s7, 8
                  nop
                  lui         ra, 32128
                  c.andi      a3, 18
                  lui         gp, 552443
                  c.li        a1, -1
                  nop
                  andi        zero, a2, 1912
                  c.sub       a3, a3
                  c.li        t0, -1
                  sltiu       t3, a5, -576
                  sub         s0, s10, t0
                  mulhu       s3, ra, s11
                  c.nop
                  srli        s2, t6, 19
                  c.or        a5, a3
                  srl         t1, a5, t2
                  sra         zero, s6, s11
                  c.xor       a3, a0
                  c.andi      a3, 8
                  sltiu       s4, a0, -1713
                  c.addi      t0, -1
                  c.andi      a3, 7
                  slt         a4, t2, a1
                  slt         t4, t2, s6
                  sub         s7, a1, a4
                  addi        zero, t5, 1671
                  c.add       s1, s4
                  lui         tp, 659366
                  c.andi      s1, -1
                  sltiu       a3, s11, -1625
                  ori         s2, a1, 1608
                  c.mv        s0, s10
                  srli        s10, t4, 9
                  and         t4, a6, t6
                  auipc       zero, 1018298
                  xori        t5, s5, 477
                  sltiu       a1, t5, -1645
                  c.nop
                  c.or        a3, a3
                  and         s0, tp, a5
                  slli        t1, s7, 27
                  divu        ra, ra, tp
                  srl         a5, t2, s2
                  add         s7, t4, zero
                  srli        t4, s8, 5
                  c.srli      a3, 28
                  nop
                  auipc       t5, 1014970
                  slli        t4, ra, 8
                  c.addi4spn  a3, sp, 896
                  sltu        a5, s0, tp
                  and         s4, s7, gp
                  c.andi      a3, 19
                  srl         s0, s10, s1
                  ori         t5, t2, 744
                  ori         zero, a0, -793
                  c.and       a3, a3
                  sltiu       a0, s9, 615
                  c.lui       ra, 30
                  mulhsu      a6, s10, t5
                  sltu        a6, gp, a0
                  c.li        t0, -1
                  sra         gp, a6, s3
                  c.xor       s0, s1
                  c.mv        tp, s3
                  c.xor       s0, a3
                  sltiu       a6, a2, 853
                  srli        ra, s11, 20
                  addi        a7, s8, 1759
                  c.xor       s0, a3
                  slli        zero, t1, 29
                  xor         t5, s7, t5
                  sub         a1, s8, a6
                  c.addi16sp  sp, 16
                  c.srli      a3, 23
                  nop
                  or          t2, t5, s8
                  c.xor       a3, a4
                  andi        s7, a3, 1806
                  c.addi      ra, 8
                  slli        tp, s5, 0
                  addi        s5, s2, 1093
                  add         a7, t5, s7
                  add         a0, a6, gp
                  div         a0, t2, t5
                  c.lui       ra, 22
                  c.addi4spn  a3, sp, 640
                  c.or        a3, a3
                  rem         t2, s2, gp
                  div         t0, t5, s11
                  sltu        a1, t4, s11
                  div         gp, a7, ra
                  c.xor       a0, a3
                  c.srai      a3, 19
                  addi        a6, a4, -310
                  xor         a1, a2, t0
                  sltu        t2, s4, tp
                  and         s0, s3, a5
                  c.li        s9, -1
                  c.or        a3, a3
                  c.addi4spn  a3, sp, 64
                  sra         s2, a2, s4
                  xori        s8, s9, 1271
                  xori        a3, s6, -1954
                  ori         s3, s7, -1404
                  mulhsu      tp, s6, s10
                  sltu        s9, t3, s6
                  sub         a6, t6, gp
                  xori        t5, s1, -46
                  add         zero, a1, a3
                  addi        zero, sp, 1012
                  c.andi      a3, -1
                  slt         t5, tp, gp
                  mulhsu      s10, s9, s10
                  srai        s4, a4, 0
                  c.addi4spn  a3, sp, 608
                  srl         ra, a2, s6
                  auipc       s10, 76000
                  addi        zero, s8, -970
                  srl         gp, a7, t6
                  c.mv        a1, s11
                  slt         tp, t5, t1
                  c.or        a4, a3
                  c.addi16sp  sp, -16
                  c.nop
                  sub         t0, gp, s1
                  mulhu       s8, t3, sp
                  sll         a4, a7, ra
                  lui         s0, 438694
                  c.xor       a3, a3
                  c.addi4spn  a3, sp, 928
                  c.sub       a3, a3
                  srai        t0, s3, 27
                  lui         zero, 1046678
                  andi        s8, zero, 1198
                  addi        s2, t4, 1156
                  sltu        s5, a4, s7
                  sub         zero, s3, ra
                  mulh        ra, s4, t2
                  c.or        a3, a3
                  c.add       s4, s3
                  c.addi4spn  a3, sp, 896
                  lui         a4, 10631
                  or          s2, t3, s0
                  c.addi16sp  sp, -16
                  sltu        a5, s1, t5
                  or          a4, ra, t4
                  c.nop
                  mulh        a2, tp, tp
                  sub         s5, t0, a1
                  c.lui       t3, 26
                  c.addi4spn  a3, sp, 320
                  c.add       t1, t2
                  mulhsu      s1, t4, t5
                  mul         tp, tp, s0
                  divu        a2, s11, a5
                  c.or        a3, a2
                  mulhu       sp, s1, zero
                  c.slli      a5, 30
                  mulhsu      zero, a4, s3
                  lui         a6, 413175
                  nop
                  c.addi16sp  sp, 16
                  nop
                  c.addi4spn  a3, sp, 96
                  sltiu       s9, s1, 228
                  sltu        s1, a3, sp
                  c.lui       t2, 27
                  c.addi16sp  sp, 416
                  ori         s0, s3, 1443
                  mulhsu      a0, zero, ra
                  rem         s9, t2, t3
                  sltiu       a0, s10, -571
                  li         t5, 0x1 #start riscv_int_numeric_corner_stream_15
                  li         s10, 0x0
                  li         s3, 0x0
                  li         t4, 0x0
                  li         t3, 0x0
                  li         a1, 0x1
                  li         a2, 0x1
                  li         a5, 0x0
                  li         a3, 0x1
                  li         s0, 0x1
                  nop
                  mulhsu      a6, gp, t5
                  add         t5, zero, t4
                  addi        s2, zero, -211
                  c.lui       gp, 18
                  mul         a4, s6, s2
                  div         s4, gp, gp
                  add         a0, t3, s0
                  c.addi      a5, -1
                  c.sub       a3, a3
                  div         a0, s4, s2
                  mulh        t3, a6, a7
                  c.li        a7, 26
                  addi        s3, sp, 1586
                  div         t3, s7, s3
                  sub         t0, a4, a6
                  mulhsu      s2, sp, sp
                  auipc       ra, 8519 #end riscv_int_numeric_corner_stream_15
                  c.or        a3, a3
                  c.addi      s10, 1
                  c.and       a3, a3
                  c.li        gp, -1
                  c.addi16sp  sp, -16
                  nop
                  c.srli      a3, 14
                  c.addi      t4, -1
                  addi        s3, a1, 1346
                  c.addi4spn  a3, sp, 640
                  lui         zero, 787282
                  mulh        t0, t0, s0
                  sra         t2, zero, a6
                  add         t5, a7, s9
                  nop
                  div         a6, ra, s4
                  c.slli      t3, 20
                  srai        a4, a2, 14
                  c.addi4spn  a3, sp, 576
                  c.or        a3, a5
                  c.lui       a0, 31
                  lui         a7, 345328
                  divu        s5, a0, t6
                  nop
                  add         t5, s2, t2
                  ori         t0, t3, 356
                  addi        a0, s11, -381
                  andi        zero, t2, 1213
                  c.add       s7, ra
                  mulhu       t3, gp, s1
                  srli        s5, t3, 31
                  add         zero, a7, a2
                  c.sub       a3, a4
                  c.addi16sp  sp, -16
                  c.addi      t2, -1
                  slli        a6, a1, 19
                  c.and       a3, s1
                  c.srli      a5, 6
                  c.srai      a3, 9
                  c.addi      a0, -1
                  sltu        a0, s9, a1
                  sub         a3, a7, s6
                  lui         t0, 71238
                  xor         a5, s6, ra
                  sll         s4, t5, a7
                  c.xor       a3, a3
                  c.nop
                  addi        t5, t3, -1831
                  slti        s2, t0, -1160
                  c.add       t4, s6
                  slti        s8, s6, 1038
                  nop
                  c.nop
                  srl         a4, a2, s1
                  or          tp, s8, gp
                  xor         s8, t3, tp
                  ori         zero, a6, 21
                  lui         s10, 973373
                  slli        s3, ra, 10
                  c.srai      a3, 21
                  slti        a4, zero, 1820
                  nop
                  srl         zero, s0, t6
                  sltiu       zero, s2, -1163
                  add         s4, t3, a5
                  c.addi16sp  sp, -16
                  mulhu       a5, s11, s5
                  mul         t5, s11, s2
                  c.li        ra, 19
                  sltiu       a3, s7, -1028
                  xori        a0, s1, 1319
                  c.slli      s7, 22
                  sltu        a2, t2, s4
                  c.nop
                  c.and       a3, a3
                  c.addi      a2, -1
                  slli        s3, s10, 7
                  rem         s10, s3, s3
                  mul         a7, s8, s4
                  c.add       t1, ra
                  c.or        a3, a3
                  srai        s2, t2, 23
                  and         a7, t1, a7
                  c.srli      a3, 26
                  slt         a0, zero, t5
                  srli        a0, s9, 12
                  or          s1, t0, a5
                  c.addi4spn  a3, sp, 320
                  rem         s1, ra, sp
                  sll         t4, gp, t5
                  c.addi4spn  a3, sp, 320
                  auipc       t5, 589762
                  c.nop
                  srli        s1, s5, 21
                  div         t1, tp, t5
                  srli        a7, s6, 4
                  c.and       a3, s1
                  slli        a2, a3, 31
                  add         a6, t3, ra
                  sra         s5, a1, s9
                  c.add       a1, a3
                  c.srai      a3, 30
                  add         t0, a6, s9
                  sra         ra, gp, a5
                  addi        tp, s10, -1977
                  c.addi4spn  a3, sp, 320
                  add         a1, gp, s5
                  sltiu       gp, t3, -787
                  c.add       a5, t5
                  slt         s2, sp, a1
                  sltu        t5, zero, s3
                  divu        t4, a7, s1
                  xor         a1, zero, gp
                  sra         s5, a5, s4
                  mulhsu      s9, a1, a1
                  sra         s10, t1, s11
                  mulh        a2, s10, s4
                  slli        ra, a3, 0
                  xori        s0, t1, 1832
                  xori        a3, tp, -668
                  sra         s1, a7, t1
                  c.mv        t2, s3
                  srl         zero, s8, s5
                  xori        a6, s11, 931
                  srli        t0, a1, 16
                  c.andi      a3, -1
                  divu        s3, t2, s5
                  srli        tp, sp, 3
                  slli        s7, a6, 4
                  srl         t1, a0, s7
                  c.and       a2, a3
                  c.mv        s4, a4
                  nop
                  or          t1, a1, a7
                  lui         t3, 322566
                  mul         a2, s7, s11
                  slti        t4, t2, 373
                  c.and       a3, a3
                  divu        a1, t0, s7
                  sra         s4, s8, a4
                  addi        sp, s7, 579
                  sra         a7, a6, a1
                  c.and       s1, a3
                  c.sub       a3, a3
                  add         s2, s0, a7
                  sll         s0, sp, t3
                  c.or        a3, a5
                  c.addi4spn  a3, sp, 64
                  c.srai      a3, 6
                  mulhu       zero, s7, t2
                  addi        a4, t3, 155
                  c.lui       s2, 23
                  slti        t4, t4, 773
                  c.andi      a3, -1
                  c.addi      tp, -1
                  srl         zero, a3, s10
                  xori        a1, s0, -1716
                  c.li        a5, 19
                  sub         s10, s3, t0
                  c.srli      a3, 8
                  c.srai      a3, 25
                  div         t5, a7, t1
                  c.andi      a3, 11
                  mulhsu      a6, t6, s9
                  srl         a3, t5, s7
                  c.srai      a3, 1
                  slti        zero, a0, 1178
                  c.srai      a0, 1
                  sltu        a6, t3, zero
                  sltiu       sp, zero, -292
                  c.srai      a5, 8
                  c.addi      s3, -1
                  lui         zero, 570981
                  c.nop
                  c.sub       a3, a5
                  divu        s1, gp, t2
                  c.srli      a3, 1
                  lui         zero, 426675
                  divu        tp, a4, a5
                  sltiu       t1, s4, 24
                  rem         a3, t6, s9
                  sub         a0, a6, sp
                  mulhsu      t5, a1, a5
                  c.xor       a3, a3
                  c.slli      a4, 10
                  sra         s3, s5, t2
                  c.mv        s5, a0
                  sll         a1, s2, s4
                  c.mv        s4, s11
                  sub         s9, s9, ra
                  divu        s7, zero, t3
                  c.addi4spn  a3, sp, 896
                  srli        zero, s7, 18
                  c.nop
                  divu        s0, sp, ra
                  div         t4, ra, s4
                  mulhsu      zero, s1, s2
                  nop
                  lui         s8, 891672
                  auipc       a1, 238372
                  ori         t3, t3, 1625
                  xor         s10, s6, s6
                  mulhu       t5, t5, t0
                  mulh        s2, ra, a1
                  c.mv        s1, a1
                  lui         s2, 815053
                  slt         s9, s7, sp
                  auipc       zero, 784223
                  c.srli      a3, 17
                  auipc       a4, 534325
                  or          zero, s0, s10
                  c.li        s10, 9
                  and         ra, s8, t6
                  auipc       tp, 133979
                  c.slli      a7, 5
                  c.xor       a3, a3
                  mulhu       zero, s3, t1
                  lui         a7, 415666
                  c.addi16sp  sp, -16
                  srl         sp, a6, a1
                  c.andi      a3, 16
                  ori         zero, tp, 494
                  c.mv        ra, t0
                  nop
                  c.add       s8, t0
                  c.srai      a3, 13
                  slti        a7, a0, 190
                  div         a6, s10, a4
                  sra         gp, zero, a4
                  and         a5, a5, ra
                  c.andi      a3, 24
                  c.addi16sp  sp, -16
                  c.sub       a3, a3
                  slti        a1, s5, -1921
                  lui         zero, 350437
                  c.or        a3, a3
                  li         t5, 0x15a0b728 #start riscv_int_numeric_corner_stream_5
                  li         t4, 0x0
                  li         t3, 0x0
                  li         t2, 0x0
                  li         s4, 0x1
                  li         a3, 0x265fb983
                  li         gp, 0x0
                  li         s9, 0x1
                  li         a2, 0x0
                  li         a5, 0x0
                  mulh        s9, s0, a7
                  auipc       a0, 158399
                  c.add       s3, a0
                  auipc       t0, 746074
                  c.mv        sp, s2
                  sub         s1, a4, a4
                  c.addi      ra, 3
                  addi        s1, t3, 1761
                  auipc       s0, 961112
                  mulhu       a3, a6, t6
                  add         s2, s3, a3
                  divu        s5, s11, s5
                  mulhu       s7, sp, s11
                  c.add       a3, a7
                  c.mv        t3, a4
                  mulh        a0, s6, s5 #end riscv_int_numeric_corner_stream_5
                  andi        zero, s1, 218
                  srai        t5, a3, 11
                  c.mv        s9, a4
                  sll         a6, t5, a5
                  sltu        tp, s9, gp
                  c.addi4spn  a4, sp, 176
                  mulhu       s4, t0, s1
                  addi        zero, zero, -1191
                  lui         a5, 877708
                  mul         zero, sp, s1
                  or          zero, s0, t5
                  slti        s3, s4, 290
                  mul         s5, a4, s5
                  c.xor       a3, a3
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
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_2:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_3:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_4:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_5:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_6:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_7:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_8:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_9:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_10:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_11:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_12:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_13:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_14:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
                  j mmode_intr_handler
                  1: la x31, test_done
                  jalr x0, x31, 0

mmode_intr_vector_15:
                  csrrw x27, 0x340, x27
                  add x27, x22, zero
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
                  csrr x14, 0x342 # MCAUSE
                  srli x14, x14, 0x1f
                  beqz x14, 1f
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
                  add x27, x22, zero
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
                  csrr x14, 0x341 # MEPC
                  csrr x14, 0x342 # MCAUSE
                  li x23, 0xb # ECALL_MMODE
                  beq x14, x23, ecall_handler
                  li x23, 0x2 # ILLEGAL_INSTRUCTION
                  beq x14, x23, illegal_instr_handler
                  csrr x23, 0x343 # MTVAL
                  1: la x31, test_done
                  jalr x1, x31, 0

ecall_handler:    
                  la x14, _start
                  sw x0, 0(x14)
                  sw x1, 4(x14)
                  sw x2, 8(x14)
                  sw x3, 12(x14)
                  sw x4, 16(x14)
                  sw x5, 20(x14)
                  sw x6, 24(x14)
                  sw x7, 28(x14)
                  sw x8, 32(x14)
                  sw x9, 36(x14)
                  sw x10, 40(x14)
                  sw x11, 44(x14)
                  sw x12, 48(x14)
                  sw x13, 52(x14)
                  sw x14, 56(x14)
                  sw x15, 60(x14)
                  sw x16, 64(x14)
                  sw x17, 68(x14)
                  sw x18, 72(x14)
                  sw x19, 76(x14)
                  sw x20, 80(x14)
                  sw x21, 84(x14)
                  sw x22, 88(x14)
                  sw x23, 92(x14)
                  sw x24, 96(x14)
                  sw x25, 100(x14)
                  sw x26, 104(x14)
                  sw x27, 108(x14)
                  sw x28, 112(x14)
                  sw x29, 116(x14)
                  sw x30, 120(x14)
                  sw x31, 124(x14)
                  la x31, write_tohost
                  jalr x0, x31, 0

illegal_instr_handler:
                  csrr  x14, 0x341
                  addi  x14, x14, 4
                  csrw  0x341, x14
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
                  add x22, x27, zero
                  csrrw x27, 0x340, x27
                  mret

pt_fault_handler: 

.align 2
mmode_intr_handler:
                  csrr  x14, 0x300 # MSTATUS;
                  csrr  x14, 0x304 # MIE;
                  csrr  x14, 0x344 # MIP;
                  csrrc x14, 0x344, x14 # MIP;
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
                  add x22, x27, zero
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
