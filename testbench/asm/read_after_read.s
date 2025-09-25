#include "defines.h"

.set    mfdc, 0x7f9

.section .text
.align 4
.global main
main:
    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    li t0, 0x5A555555
    csrw 0x7c0, t0

    li  t0, 4
    fence.i
    csrw    mfdc, t0     // disable store merging
    fence.i

    la  a0, scratchpad
    la  s6, scratchpad
    lw  zero, 304(a0)
    lw  a0, 24(s6) // 0x18
    lw  a1, 20(s6) // 0x14
    sw  a0, 28(sp)
    sw  a1, 24(sp)
    lw  a0, 16(s6) // 0x10
    lw  a1, 12(s6) // 0x_C
    lw  s3, 4(s6)  // 0x_4
    lw  s8, 8(s6)  // 0x_8
    sw  a0, 20(sp)
    sw  a1, 16(sp)
    sw  s3, 12(sp)
    sw  s8, 8(sp)
    li  a0, 1
    lw  a1, 28(sp)
    li  t0, 6
    bne a1, t0, failed
    lw  a1, 24(sp)
    li  t0, 5
    bne a1, t0, failed
    lw  a1, 20(sp)
    li  t0, 4
    bne a1, t0, failed
    lw  a1, 16(sp)
    li  t0, 3
    bne a1, t0, failed
    lw  a1, 12(sp)
    li  t0, 1
    bne a1, t0, failed
    lw  a1, 8(sp)
    li  t0, 2
    bne a1, t0, failed
    lw  a1, 4(sp)
    li  t0, 0
    bne a1, t0, failed
    li  a0, 0
.global failed
failed:
    ret

.section .data
.global scratchpad
scratchpad:
.4byte  0
.4byte  1
.4byte  2
.4byte  3
.4byte  4
.4byte  5
.4byte  6
.4byte  7
.4byte  8
.4byte  9
.4byte  10
.4byte  11
.4byte  12
.4byte  13
.4byte  14
.4byte  15
.4byte  16
.4byte  17
.4byte  18
.4byte  19
.4byte  20
.4byte  21
.4byte  22
.4byte  23
.4byte  24
.4byte  25
.4byte  26
.4byte  27
.4byte  28
.4byte  29
.4byte  30
.4byte  31
.4byte  32
.4byte  33
.4byte  34
.4byte  35
.4byte  36
.4byte  37
.4byte  38
.4byte  39
.4byte  40
.4byte  41
.4byte  42
.4byte  43
.4byte  44
.4byte  45
.4byte  46
.4byte  47
.4byte  48
.4byte  49
.4byte  50
.4byte  51
.4byte  52
.4byte  53
.4byte  54
.4byte  55
.4byte  56
.4byte  57
.4byte  58
.4byte  59
.4byte  60
.4byte  61
.4byte  62
.4byte  63
.4byte  64
.4byte  65
.4byte  66
.4byte  67
.4byte  68
.4byte  69
.4byte  70
.4byte  71
.4byte  72
.4byte  73
.4byte  74
.4byte  75
.4byte  76
