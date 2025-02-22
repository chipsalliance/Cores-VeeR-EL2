import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

# TAP State Constants (renamed to *_STATE format)
TEST_LOGIC_RESET_STATE = 0x0
RUN_TEST_IDLE_STATE = 0x1
SELECT_DR_SCAN_STATE = 0x2
CAPTURE_DR_STATE = 0x3
SHIFT_DR_STATE = 0x4
EXIT1_DR_STATE = 0x5
PAUSE_DR_STATE = 0x6
EXIT2_DR_STATE = 0x7
UPDATE_DR_STATE = 0x8
SELECT_IR_SCAN_STATE = 0x9
CAPTURE_IR_STATE = 0xA
SHIFT_IR_STATE = 0xB
EXIT1_IR_STATE = 0xC
PAUSE_IR_STATE = 0xD
EXIT2_IR_STATE = 0xE
UPDATE_IR_STATE = 0xF

# Define the TAP state transition table
TAP_TRANSITIONS = {
    (TEST_LOGIC_RESET_STATE, TEST_LOGIC_RESET_STATE): 1,
    (TEST_LOGIC_RESET_STATE, RUN_TEST_IDLE_STATE): 0,
    (RUN_TEST_IDLE_STATE, SELECT_DR_SCAN_STATE): 1,
    (RUN_TEST_IDLE_STATE, RUN_TEST_IDLE_STATE): 0,
    (SELECT_DR_SCAN_STATE, SELECT_IR_SCAN_STATE): 1,
    (SELECT_DR_SCAN_STATE, CAPTURE_DR_STATE): 0,
    (CAPTURE_DR_STATE, EXIT1_DR_STATE): 1,
    (CAPTURE_DR_STATE, SHIFT_DR_STATE): 0,
    (SHIFT_DR_STATE, EXIT1_DR_STATE): 1,
    (SHIFT_DR_STATE, SHIFT_DR_STATE): 0,
    (EXIT1_DR_STATE, UPDATE_DR_STATE): 1,
    (EXIT1_DR_STATE, PAUSE_DR_STATE): 0,
    (PAUSE_DR_STATE, EXIT2_DR_STATE): 1,
    (PAUSE_DR_STATE, PAUSE_DR_STATE): 0,
    (EXIT2_DR_STATE, UPDATE_DR_STATE): 1,
    (EXIT2_DR_STATE, SHIFT_DR_STATE): 0,
    (UPDATE_DR_STATE, SELECT_DR_SCAN_STATE): 1,
    (UPDATE_DR_STATE, RUN_TEST_IDLE_STATE): 0,
    (SELECT_IR_SCAN_STATE, TEST_LOGIC_RESET_STATE): 1,
    (SELECT_IR_SCAN_STATE, CAPTURE_IR_STATE): 0,
    (CAPTURE_IR_STATE, EXIT1_IR_STATE): 1,
    (CAPTURE_IR_STATE, SHIFT_IR_STATE): 0,
    (SHIFT_IR_STATE, EXIT1_IR_STATE): 1,
    (SHIFT_IR_STATE, SHIFT_IR_STATE): 0,
    (EXIT1_IR_STATE, UPDATE_IR_STATE): 1,
    (EXIT1_IR_STATE, PAUSE_IR_STATE): 0,
    (PAUSE_IR_STATE, EXIT2_IR_STATE): 1,
    (PAUSE_IR_STATE, PAUSE_IR_STATE): 0,
    (EXIT2_IR_STATE, UPDATE_IR_STATE): 1,
    (EXIT2_IR_STATE, SHIFT_IR_STATE): 0,
    (UPDATE_IR_STATE, SELECT_DR_SCAN_STATE): 1,
    (UPDATE_IR_STATE, RUN_TEST_IDLE_STATE): 0,
}

# Traverse each possible transition
TEST_PATH = [
    TEST_LOGIC_RESET_STATE,
    TEST_LOGIC_RESET_STATE,
    RUN_TEST_IDLE_STATE,
    RUN_TEST_IDLE_STATE,
    SELECT_DR_SCAN_STATE,
    CAPTURE_DR_STATE,
    SHIFT_DR_STATE,
    SHIFT_DR_STATE,
    EXIT1_DR_STATE,
    PAUSE_DR_STATE,
    PAUSE_DR_STATE,
    EXIT2_DR_STATE,
    UPDATE_DR_STATE,
    SELECT_DR_SCAN_STATE,
    CAPTURE_DR_STATE,
    EXIT1_DR_STATE,
    PAUSE_DR_STATE,
    EXIT2_DR_STATE,
    UPDATE_DR_STATE,
    RUN_TEST_IDLE_STATE,
    SELECT_DR_SCAN_STATE,
    CAPTURE_DR_STATE,
    EXIT1_DR_STATE,
    PAUSE_DR_STATE,
    EXIT2_DR_STATE,
    SHIFT_DR_STATE,
    EXIT1_DR_STATE,
    UPDATE_DR_STATE,
    RUN_TEST_IDLE_STATE,
    SELECT_DR_SCAN_STATE,
    SELECT_IR_SCAN_STATE,
    CAPTURE_IR_STATE,
    SHIFT_IR_STATE,
    SHIFT_IR_STATE,
    EXIT1_IR_STATE,
    PAUSE_IR_STATE,
    PAUSE_IR_STATE,
    EXIT2_IR_STATE,
    SHIFT_IR_STATE,
    EXIT1_IR_STATE,
    PAUSE_IR_STATE,
    EXIT2_IR_STATE,
    UPDATE_IR_STATE,
    SELECT_DR_SCAN_STATE,
    SELECT_IR_SCAN_STATE,
    TEST_LOGIC_RESET_STATE,
    RUN_TEST_IDLE_STATE,
    SELECT_DR_SCAN_STATE,
    SELECT_IR_SCAN_STATE,
    CAPTURE_IR_STATE,
    EXIT1_IR_STATE,
    UPDATE_IR_STATE,
]


@cocotb.test()
async def test_full_tap_fsm(dut):
    """Exercise all possible TAP FSM states via TMS and TCK."""
    clock = Clock(dut.tck, 10, units="ns")  # 100 MHz clock
    cocotb.start_soon(clock.start())  # Start the clock

    # Assert tms to ensure entering the test with `TEST_LOGIC_RESET_STATE`
    dut.tms.value = 1

    # Apply reset (active-low)
    dut.trst_n.value = 0
    await Timer(20, units="ns")
    dut.trst_n.value = 1
    await RisingEdge(dut.tck)

    # Ensure FSM starts in Test-Logic-Reset
    assert (
        dut.wrapper.i_jtag_tap.state.value == TEST_LOGIC_RESET_STATE
    ), f"Expected state TEST_LOGIC_RESET_STATE, got {dut.wrapper.i_jtag_tap.state.value}"

    assert (
        dut.wrapper.i_jtag_tap.state.value == TEST_LOGIC_RESET_STATE
    ), f"Expected state TEST_LOGIC_RESET_STATE after reset, got {dut.wrapper.i_jtag_tap.state.value}"

    # Iterate through all valid state transitions
    for i in range(len(TEST_PATH) - 1):
        s0, s1 = TEST_PATH[i], TEST_PATH[i + 1]
        tms_value = TAP_TRANSITIONS[(s0, s1)]

        # Apply TMS value
        dut.tms.value = tms_value
        await RisingEdge(dut.tck)

        assert (
            dut.wrapper.i_jtag_tap.state.value == s0 and dut.wrapper.i_jtag_tap.nstate.value == s1
        ), f"Expected state {s0}, got {dut.wrapper.i_jtag_tap.state.value}"

    # Apply reset (active-low)
    dut.trst_n.value = 0
    await RisingEdge(dut.tck)

    assert (
        dut.wrapper.i_jtag_tap.state.value == TEST_LOGIC_RESET_STATE
    ), f"Expected state TEST_LOGIC_RESET_STATE after reset, got {dut.wrapper.i_jtag_tap.state.value}"
