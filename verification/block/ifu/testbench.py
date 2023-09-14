import os

from cocotb.triggers import Timer
from cocotb.binary import BinaryValue

import pyuvm
from pyuvm import *


def decompress(nop):
    # TODO: Actually decompress instructions into BinaryValue type
    return BinaryValue(value="00000000000000000000000000010011")


def collect_signals(signals, uut, obj, uut_prefix="", obj_prefix=""):
    """
    Collects signal objects from UUT and attaches them to the given object.
    Optionally UUT signals can be prefixed with the uut_prefix and object
    signals with the obj_prefix
    """

    for sig in signals:
        uut_sig = uut_prefix + sig
        obj_sig = obj_prefix + sig
        if hasattr(uut, uut_sig):
            s = getattr(uut, uut_sig)

        else:
            s = None
            logging.error(
                "Module {} does not have a signal '{}'".format(str(uut), sig)
            )

        setattr(obj, obj_sig, s)


class DecompressorItem(uvm_sequence_item):
    """
    A generic instruction-input stimulus
    """
    def __init__(self, din, dout):
        super().__init__("InstructionItem")
        """
        Records a state of decompressor's pins
        """

        self.din = din
        self.dout = dout


class CompressedInstructionItem(uvm_sequence_item):
    """
    A generic compressed instruction-input stimulus
    """
    def __init__(self):
        super().__init__("CompressedInstructionItem")
        """
        Creates a 16-bit instruction
        """

        # TODO: Create a random compressed instruction
        self.instr = int(("0" * 15) + "1")


class CompressedSequence(uvm_sequence):
    """
    A sequencer that generates random RISC-V compressed instructions
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        for j in range(50):
            # Create a compressed instruction
            item = CompressedInstructionItem()
            await self.start_item(item)
            await self.finish_item(item)


class DecompressorDriver(uvm_driver):
    """
    A driver for the IFU instruction decompressor
    """

    SIGNALS = ["din", "dout"]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]
        super().__init__(*args, **kwargs)
        
        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

    async def write(self, instr):
        """
        Pushes instruction to the decompressor
        """

        self.din.value = instr
        await Timer(10, "us")

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()
            if isinstance(it, CompressedInstructionItem):
                await self.write(it.instr)
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))
            self.seq_item_port.item_done()


class DecompressorMonitor(uvm_component):
    """
    A monitor for the IFU instruction decompressor
    """

    SIGNALS = ["din", "dout"]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            await Timer(10, "us")
            it = DecompressorItem(self.din, self.dout)
            self.ap.write(it)


class Scoreboard(uvm_component):
    """
    Checks if all decompressed instructions have the expected value
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):

        # Process items
        while self.port.can_get():

            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # Got a decompressed instruction which is incorrect
            if isinstance(item, DecompressorItem):
                if item.dout != decompress(item.din):
                    self.logger.debug(
                        "Instruction decompressed incorrectly: 0x%v -> 0x%v".format(
                        item.din,
                        item.dout
                    ))
                    self.passed = False


    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

        # Sequencers
        self.dcm_seqr = uvm_sequencer("dcm_seqr", self)

        self.dcm_drv = DecompressorDriver("dcm_drv", self, uut=cocotb.top)

        self.dcm_mon = DecompressorMonitor("dcm_mon", self, uut=cocotb.top)

    def connect_phase(self):
        self.dcm_drv.seq_item_port.connect(self.dcm_seqr.seq_item_export)
        self.dcm_mon.ap.connect(self.scoreboard.fifo.analysis_export)


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    async def run_phase(self):
        self.raise_objection()
        await self.run()
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()

