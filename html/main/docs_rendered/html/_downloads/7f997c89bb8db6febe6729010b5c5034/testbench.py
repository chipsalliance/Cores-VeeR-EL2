#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import *

# ==============================================================================


ACCESS_TYPE = {
    0b001: "R",
    0b010: "W",
    0b100: "X",
}


class RegisterMap:
    def __init__(self, pmp_entries):
        self.reg = dict()
        for i in range(pmp_entries):
            name = "pmpcfg{}".format(i)
            self.reg[name] = BinaryValue(value=0, bigEndian=False, n_bits=8)

            name = "pmpaddr{}".format(i)
            self.reg[name] = BinaryValue(value=0, bigEndian=False, n_bits=32)


def getDecodedEntryCfg(regs, index, range_only=False):
    """ """
    pmpcfg = regs.reg["pmpcfg{}".format(index)]
    pmpaddr = regs.reg["pmpaddr{}".format(index)]

    # bits 0-2, (R, W, X)
    permissions = {"R": pmpcfg[0].integer, "W": pmpcfg[1].integer, "X": pmpcfg[2].integer}
    address_matching = pmpcfg[4:3].integer
    locked = pmpcfg[7].integer

    if index:
        start_address = regs.reg["pmpaddr{}".format(index - 1)].integer << 2
    else:
        start_address = 0

    if address_matching == 0:  # Entry diabled
        if range_only:
            end_address = pmpaddr.integer << 2
            return start_address, end_address
        else:
            return None
    elif address_matching == 1:  # Top of range
        end_address = pmpaddr.integer << 2
        if start_address > end_address:
            if range_only:
                return start_address, end_address
            else:
                return None
    elif address_matching == 2:  # Naturally aligned four-byte region
        end_address = (pmpaddr.integer << 2) + 4
    elif address_matching == 3:  # Naturally aligned power-of-two region, >=8 bytes
        napot = 3
        start_address = pmpaddr
        for i in range(len(pmpaddr)):
            if pmpaddr[i].integer == 1:
                start_address[i].value = 0
                napot += 1
            else:
                continue

        start_address = start_address.integer << 2
        end_address = start_address + 2**napot

    # PMP upper address bundary is non-inclusive
    end_address -= 1

    if range_only:
        return start_address, end_address
    else:
        return start_address, end_address, permissions, locked


# ==============================================================================


class PMPWriteCfgCSRItem(uvm_sequence_item):
    def __init__(self, index, pmpcfg):
        super().__init__("PMPWriteCfgCSRItem")
        self.index = index
        self.pmpcfg = pmpcfg


class PMPWriteAddrCSRItem(uvm_sequence_item):
    def __init__(self, index, pmpaddr):
        super().__init__("PMPWriteAddrCSRItem")
        self.index = index
        self.pmpaddr = pmpaddr


class PMPCheckItem(uvm_sequence_item):
    def __init__(self, channel, addr, type, err=None):
        super().__init__("PMPCheckItem")
        self.channel = channel
        self.addr = addr
        self.type = type
        self.err = err


# ==============================================================================


def collect_signals(signals, uut, obj):
    """
    Collects signal objects from UUT and attaches them to the given object
    """

    for sig in signals:
        if hasattr(uut, sig):
            s = getattr(uut, sig)

        else:
            s = None
            logging.error("Module {} does not have a signal '{}'".format(str(uut), sig))

        setattr(obj, sig, s)


# ==============================================================================


class PMPDriver(uvm_driver):
    SIGNALS = [
        "clk",
        # CSRs
        "pmp_pmpcfg",
        "pmp_pmpaddr",
        # PMP logic
        "pmp_chan_addr",
        "pmp_chan_type",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]
        super().__init__(*args, **kwargs)
        self.regs = ConfigDB().get(None, "", "PMP_CSRS")

        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, PMPWriteAddrCSRItem):
                self.pmp_pmpaddr[it.index].value = it.pmpaddr
                self.regs.reg["pmpaddr{}".format(it.index)].integer = it.pmpaddr
            elif isinstance(it, PMPWriteCfgCSRItem):
                self.pmp_pmpcfg[it.index].value = it.pmpcfg
                self.regs.reg["pmpcfg{}".format(it.index)].integer = it.pmpcfg
            elif isinstance(it, PMPCheckItem):
                self.pmp_chan_addr[it.channel].value = it.addr
                self.pmp_chan_type[it.channel].value = it.type
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            await ClockCycles(self.clk, 1)
            self.seq_item_port.item_done()


class PMPMonitor(uvm_component):
    SIGNALS = [
        "clk",
        # CSRs
        "pmp_pmpcfg",
        "pmp_pmpaddr",
        # PMP logic
        "pmp_chan_addr",
        "pmp_chan_type",
        "pmp_chan_err",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.pmp_channels = ConfigDB().get(None, "", "PMP_CHANNELS")
        self.pmp_entries = ConfigDB().get(None, "", "PMP_ENTRIES")

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            await RisingEdge(self.clk)

            # Check all PMP channels
            for i in range(self.pmp_channels):
                access_addr = int(self.pmp_chan_addr[i].value)
                access_type = int(self.pmp_chan_type[i].value)
                access_err = int(self.pmp_chan_err.value[i])

                self.ap.write(PMPCheckItem(i, access_addr, access_type, access_err))


# ==============================================================================


class Scoreboard(uvm_component):
    def build_phase(self):
        self.passed = True
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)
        self.regs = ConfigDB().get(None, "", "PMP_CSRS")

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        while self.port.can_get():
            _, item = self.port.try_get()

            if isinstance(item, PMPCheckItem):
                addr = item.addr
                type = item.type
                chan = item.channel
                err = item.err
                type_str = ACCESS_TYPE.get(type, "UNKNOWN ({})".format(type))

                if type_str not in ACCESS_TYPE.values():
                    self.logger.debug(
                        "Unknown access type ({}), probably checking channel that doesn't request access.".format(
                            type
                        )
                    )
                    continue

                # Check if address range can be matched to any PMP entry
                entry_permissions = None
                for i in range(len(self.regs.reg) // 2):
                    entry = getDecodedEntryCfg(self.regs, i)
                    if entry is not None:
                        pmp_start_addr, pmp_end_addr, permissions, locked = entry
                    else:
                        continue

                    # Check if entry address range matches channel address
                    if addr in range(pmp_start_addr, pmp_end_addr):
                        if locked:  # If entry is locked, save it for permission checks
                            entry_permissions = permissions
                        break

                log_msg = "PMPCheckItem: Validating access 0x{:08x}, type={} ({}), channel={}, error={}".format(
                    addr, type, type_str, chan, err
                )
                if entry_permissions is None:
                    # If address range was not matched, ensure that error is not raised
                    if err:
                        self.logger.error("Error asserted when no entry was matched!")
                        self.logger.debug(log_msg)
                        self.passed = False
                else:
                    # If address range was matched, compare permissions to the command type
                    for op in ACCESS_TYPE.values():
                        if type_str == op and not (entry_permissions[op] ^ err):
                            self.logger.error("Unexpected error state on access request!")
                            self.logger.debug(log_msg)
                            self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        pmp_entries = 16
        ConfigDB().set(None, "*", "PMP_ENTRIES", pmp_entries)
        ConfigDB().set(None, "*", "PMP_CHANNELS", 3)
        ConfigDB().set(None, "*", "PMP_GRANULARITY", 0)

        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 100)

        # PMP Registers
        self.regs = RegisterMap(pmp_entries)
        ConfigDB().set(None, "*", "PMP_CSRS", self.regs)

        # Sequencers
        self.pmp_seqr = uvm_sequencer("pmp_seqr", self)

        # PMP interface
        self.pmp_drv = PMPDriver("pmp_drv", self, uut=cocotb.top)
        self.pmp_mon = PMPMonitor("pmp_mon", self, uut=cocotb.top)

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

        ConfigDB().set(None, "*", "PMP_SEQR", self.pmp_seqr)

    def connect_phase(self):
        self.pmp_drv.seq_item_port.connect(self.pmp_seqr.seq_item_export)
        self.pmp_mon.ap.connect(self.scoreboard.fifo.analysis_export)


# ==============================================================================


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

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def run_phase(self):
        self.raise_objection()

        cocotb.top.scan_mode.value = 0
        cocotb.top.pmp_chan_addr.value = [0, 0, 0]
        cocotb.top.pmp_chan_type.value = [0, 0, 0]

        self.start_clock("clk")
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1
        await self.run()
        await ClockCycles(cocotb.top.clk, 2)
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
