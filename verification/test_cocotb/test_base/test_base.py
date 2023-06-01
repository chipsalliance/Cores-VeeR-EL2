import cocotb
from .common import Harness


@cocotb.test()
async def test_basic(dut):
    harness = Harness(dut, 100)

    # Clock starts when instancing harness.
    # Reset is being held by testbench for 5 clock cycles

    print("JTAG ID: ", hex(dut.jtag_id.value))

    # Wait until program reports success or failure via mailbox
    # or timeouts (cycle limit).
    # You can pass file object `write()`` function or compatible
    # via `asciioutput` optional argument.
    cocotb.start_soon(harness.cycle_monitor())
    exec_result = await harness.mailbox_monitor()

    # Simulation is paused after raising test result in cocotb,
    # so we read cycle counter here.
    harness.finish(exec_result)
