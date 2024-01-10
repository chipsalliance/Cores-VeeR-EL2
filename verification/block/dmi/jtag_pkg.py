from enum import IntEnum

from cocotb.types import LogicArray, Range


class JTAGDefaults:
    IDLE = LogicArray(0, Range(1, "downto", 0))
    DMI_STAT = LogicArray(0, Range(1, "downto", 0))
    VERSION = LogicArray(1, Range(3, "downto", 0))
    RD_STATUS = LogicArray(0, Range(1, "downto", 0))


class JTAGInstructions:
    DEVICE_ID_SEL = LogicArray(0b00001, Range(4, "downto", 0))
    DR_EN_0 = LogicArray(0b10000, Range(4, "downto", 0))
    DR_EN_1 = LogicArray(0b10001, Range(4, "downto", 0))


class JTAGStates(IntEnum):
    TEST_LOGIC_RESET_STATE = 0
    RUN_TEST_IDLE_STATE = 1
    SELECT_DR_SCAN_STATE = 2
    CAPTURE_DR_STATE = 3
    SHIFT_DR_STATE = 4
    EXIT1_DR_STATE = 5
    PAUSE_DR_STATE = 6
    EXIT2_DR_STATE = 7
    UPDATE_DR_STATE = 8
    SELECT_IR_SCAN_STATE = 9
    CAPTURE_IR_STATE = 10
    SHIFT_IR_STATE = 11
    EXIT1_IR_STATE = 12
    PAUSE_IR_STATE = 13
    EXIT2_IR_STATE = 14
    UPDATE_IR_STATE = 15
