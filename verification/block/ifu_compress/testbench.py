import os
import random
import subprocess
import textwrap
from queue import Queue

import pyuvm
from cocotb.binary import BinaryValue
from cocotb.triggers import Timer
from pyuvm import *


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
            logging.error("Module {} does not have a signal '{}'".format(str(uut), sig))

        setattr(obj, obj_sig, s)


def get_opcode(asm_line, ext="rv32i", size=32):
    """
    Generates binary opcode string based on a line of assembly
    """

    cmd = f"echo '{asm_line}' | riscv64-unknown-elf-as -march={ext} -o /dev/null -al | tail -n 1"

    # Take instruction hex (3rd column) and change its endianess
    out = subprocess.check_output([cmd], shell=True).decode().split()[2]
    out = "".join(textwrap.wrap(out, 2)[::-1])

    assert len(out) == size // 4, f"instruction '{asm_line}' assembled to unexpected width"

    # Convert hex to bin
    opcode = f"{int(out, 16):0{size}b}"

    return opcode


def generate_assembly_pair():
    """
    Generates random assembly instruction that can be compressed
    """

    # For most compressed instructions only x8--x15 are allowed
    dreg = random.randrange(8, 16)
    sreg = random.randrange(8, 16)

    imm = random.randrange(2**11)
    sgn = random.choice(["-", ""])

    # In f-strings below:
    # {imm%width} -- when the immediate's magnitude has a limited width
    # {imm or 1}  -- when the immediate cannot be 0
    # {sgn}{imm}  -- when the immediate is signed
    return random.choice(
        [
            (f"c.add x{dreg}, x{sreg}", f"add x{dreg}, x{dreg}, x{sreg}"),
            (f"c.or x{dreg}, x{sreg}", f"or x{dreg}, x{dreg}, x{sreg}"),
            (f"c.xor x{dreg}, x{sreg}", f"xor x{dreg}, x{dreg}, x{sreg}"),
            (f"c.sub x{dreg}, x{sreg}", f"sub x{dreg}, x{dreg}, x{sreg}"),
            (f"c.mv x{dreg}, x{sreg}", f"add x{dreg}, x0, x{sreg}"),
            (f"c.andi x{dreg}, {sgn}{imm % 5}", f"andi x{dreg}, x{dreg}, {sgn}{imm % 5}"),
            (f"c.addi x{dreg}, {sgn}{imm % 5}", f"addi x{dreg}, x{dreg}, {sgn}{imm % 5}"),
            (f"c.srli x{dreg}, {imm % 5 or 1}", f"srli x{dreg}, x{dreg}, {imm % 5 or 1}"),
            (f"c.srai x{dreg}, {imm % 5 or 1}", f"srai x{dreg}, x{dreg}, {imm % 5 or 1}"),
            (f"c.slli x{dreg}, {imm % 5 or 1}", f"slli x{dreg}, x{dreg}, {imm % 5 or 1}"),
            ("c.ebreak", "ebreak"),
        ]
    )


class CompressedGenerator:
    """
    Generates compressed instructions and caches their expected
    decompressed counterpart to allow fast checks
    """

    lookup = {}

    @classmethod
    def get(self):
        """
        Generates compressed/decompressed instruction pair
        """

        asm_com, asm_dec = generate_assembly_pair()

        com = get_opcode(asm_com, ext="rv32ic", size=16)
        dec = get_opcode(asm_dec, ext="rv32i", size=32)

        self.lookup[com] = dec

        return com

    @classmethod
    def check(self, com, dec):
        """
        Checks if a previously generated instruction corresponds to the
        decompressed one given
        """

        assert com in self.lookup, f"instruction 0b{com} not generated before"
        return self.lookup[com] == dec


class InstructionPairItem(uvm_sequence_item):
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

        instr = CompressedGenerator.get()
        self.instr = BinaryValue(value=instr, bigEndian=False)


class CompressedSequence(uvm_sequence):
    """
    A sequencer that generates random RISC-V compressed instructions
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for j in range(count):
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
            it = InstructionPairItem(self.din, self.dout)
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
            if isinstance(item, InstructionPairItem):
                if not CompressedGenerator.check(str(item.din.value), str(item.dout.value)):
                    self.logger.debug(
                        "Instruction decompressed incorrectly: 0b{} -> 0b{}".format(
                            item.din, item.dout
                        )
                    )
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
        # Config
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 500)

        # Sequencers
        self.dcm_seqr = uvm_sequencer("dcm_seqr", self)

        # Driver
        self.dcm_drv = DecompressorDriver("dcm_drv", self, uut=cocotb.top)

        # Monitor
        self.dcm_mon = DecompressorMonitor("dcm_mon", self, uut=cocotb.top)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

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
