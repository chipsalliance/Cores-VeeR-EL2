MEICPCT = 0xBCA
MEIVT = 0xBC8
# MTSEL (R/W)
# [1:0] : Trigger select : 00, 01, 10 are data/address triggers. 11 is inst count
MTSEL = 0x7A0

# MTDATA1 (R/W)
# [31:0] : Trigger Data 1
MTDATA1 = 0x7A1

# MTDATA2 (R/W)
# [31:0] : Trigger Data 2
MTDATA2 = 0x7A2

# performance counters
MHPMC3 = 0xB03
MHPMC3H = 0xB83
MHPMC4 = 0xB04
MHPMC4H = 0xB84
MHPMC5 = 0xB05
MHPMC5H = 0xB85
MHPMC6 = 0xB06
MHPMC6H = 0xB86
MINSTRETL = 0xB02
MINSTRETH = 0xB82
MCYCLEL = 0xB00
MCYCLEH = 0xB80

MICECT = 0x7F0
MICCMECT = 0x7F1
MDCCMECT = 0x7F2

# debug mode CSRs
DICAD0 = 0x7C9
DICAD0H = 0x7CC
DICAD1 = 0x7CA
DICAWICS = 0x7C8
DPC = 0x7B1
DCSR = 0x7B0  # upper 4 bits hardcoded to 0x4
