from collections.abc import Callable


class CSR(int):
    def __new__(cls, addr: int, out: Callable[[int], int] = lambda x: x):
        c = super(CSR, cls).__new__(cls, addr)
        c.out = out
        return c


def get_bit(value, i):
    return (value >> i) & 1


def _prevent_11_pairs(value):
    new_value = 0
    for i in reversed(range(0, 31, 2)):
        new_value = new_value << 2
        b0 = get_bit(value, i)
        b1 = get_bit(value, i + 1)
        new_value |= (b1 << 1) | (b0 & (not b1))
    return new_value


def _mhpme_zero_event(value):
    return (
        (value > 516)
        | ((value < 512) & (value > 56))
        | ((value < 54) & (value > 50))
        | (value == 29)
        | (value == 33)
    )


def _m_ect(value):
    if ((value >> 27) & 0x1F) > 26:
        value = value & 0x07FFFFFF
        value = value | (26 << 27)
    return value


def _dicawics(value):
    value = value & 0x1FFFFFF
    value = value & ~(1 << 23)
    value = value & ~(1 << 22)
    value = value & ~(1 << 19)
    value = value & ~(1 << 18)
    value = value & ~(1 << 17)
    value = value & ~(1 << 2)
    value = value & ~(1 << 1)
    value = value & ~(1 << 0)
    return value


def _dcsr(value):
    value = (value & 0xFFFF) | (0x4 << 28)
    value = (value & 0xFFFFFFFC) | 0x3
    value = value & ~(1 << 14)  # reserved
    value = value & ~(1 << 13)  # ebreaks (0 for VeeR-EL2)
    value = value & ~(1 << 12)  # ebreaku (0 for VeeR-EL2)
    value = value & ~(1 << 9)  # stoptime (0 for VeeR-EL2)
    value = value & ~(1 << 8)  # reserved
    value = (value & ~(1 << 7)) | (1 << 7)
    value = (value & ~(1 << 6)) | (1 << 6)
    value = value & ~(1 << 5)  # reserved
    value = value & ~(1 << 4)  # reserved
    value = value & ~(1 << 3)  # reserved
    return value


# Dbus Error Address Unlock register
MDEAU = CSR(0xBC0)
# Dbus Store Error Address Capture register
MDSEAC = CSR(0xFC0)

MEICPCT = CSR(0xBCA)
MEIVT = CSR(0xBC8)
# MTSEL (R/W)
# [1:0] : Trigger select : 00, 01, 10 are data/address triggers. 11 is inst count
MTSEL = CSR(0x7A0)

# MTDATA1 (R/W)
# [31:0] : Trigger Data 1
MTDATA1 = CSR(0x7A1)

# MTDATA2 (R/W)
# [31:0] : Trigger Data 2
MTDATA2 = CSR(0x7A2)

# External Interrupt Priority Threshold
MEIPT = CSR(0xBC9, lambda _: _ & 0xF)
# [31:2] BASE : Trap vector base address
# [1] - Reserved, not implemented, reads zero
# [0]  MODE : 0 = Direct, 1 = Asyncs
MTVEC = CSR(0x305, lambda _: _ & 0xFFFFFFFD)
# Region Access Control Register, 16 regions
MRAC = CSR(0x7C0, _prevent_11_pairs)
MCOUNTINHIBIT = CSR(0x320, lambda _: _ & 0x7D)
MFDHT = CSR(0x7CE, lambda _: _ & 0x3F)
MEICURPL = CSR(0xBCC, lambda _: _ & 0xF)
MFDC = CSR(0xBCC, lambda _: _ & 0x71FBF)
# performance counters
MHPMC3 = CSR(0xB03)
MHPMC3H = CSR(0xB83)
MHPMC4 = CSR(0xB04)
MHPMC4H = CSR(0xB84)
MHPMC5 = CSR(0xB05)
MHPMC5H = CSR(0xB85)
MHPMC6 = CSR(0xB06)
MHPMC6H = CSR(0xB86)
MINSTRETL = CSR(0xB02)
MINSTRETH = CSR(0xB82)
MCYCLEL = CSR(0xB00)
MCYCLEH = CSR(0xB80)

# hardware performance monitors
MHPME3 = CSR(0x323, lambda x: 0 if _mhpme_zero_event(x) else x)
MHPME4 = CSR(0x324, lambda x: 0 if _mhpme_zero_event(x) else x)
MHPME5 = CSR(0x325, lambda x: 0 if _mhpme_zero_event(x) else x)
MHPME6 = CSR(0x326, lambda x: 0 if _mhpme_zero_event(x) else x)

MICECT = CSR(0x7F0, _m_ect)
MICCMECT = CSR(0x7F1, _m_ect)
MDCCMECT = CSR(0x7F2, _m_ect)

# debug mode CSRs
DICAD0 = CSR(0x7C9)
DICAD0H = CSR(0x7CC)
DICAD1 = CSR(0x7CA)
DICAWICS = CSR(0x7C8, _dicawics)
DPC = CSR(0x7B1, lambda _: _ & ~(0x1))
DCSR = CSR(0x7B0, _dcsr)  # upper 4 bits hardcoded to 0x4

MEICIDPL = CSR(0xBCB, lambda _: _ & 0xF)
