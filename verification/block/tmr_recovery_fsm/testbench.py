#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import cocotb
from cocotb.clock import Clock
from cocotb.handle import ModifiableObject
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, ReadWrite, RisingEdge
from cocotb.utils import get_sim_time
from pyuvm import *

from common import ClockDomain

# ==============================================================================

# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue = 0b10

# ==============================================================================

# CSRs available in M-mode only
MCSR = [
    0x300,
    0x301,
    0x304,
    0x305,
    0x320,
    0x323,
    0x324,
    0x325,
    0x326,
    0x340,
    0x341,
    0x342,
    0x343,
    0x344,
    0x3A0,
    0x3A1,
    0x3A2,
    0x3A3,
    0x3A4,
    0x3A5,
    0x3A6,
    0x3A7,
    0x3A8,
    0x3A9,
    0x3AA,
    0x3AB,
    0x3AC,
    0x3AD,
    0x3AE,
    0x3AF,
    0x3B0,
    0x3B1,
    0x3B2,
    0x3B3,
    0x3B4,
    0x3B5,
    0x3B6,
    0x3B7,
    0x3B8,
    0x3B9,
    0x3BA,
    0x3BB,
    0x3BC,
    0x3BD,
    0x3BE,
    0x3BF,
    0x3C0,
    0x3C1,
    0x3C2,
    0x3C3,
    0x3C4,
    0x3C5,
    0x3C6,
    0x3C7,
    0x3C8,
    0x3C9,
    0x3CA,
    0x3CB,
    0x3CC,
    0x3CD,
    0x3CE,
    0x3CF,
    0x3D0,
    0x3D1,
    0x3D2,
    0x3D3,
    0x3D4,
    0x3D5,
    0x3D6,
    0x3D7,
    0x3D8,
    0x3D9,
    0x3DA,
    0x3DB,
    0x3DC,
    0x3DD,
    0x3DE,
    0x3DF,
    0x3E0,
    0x3E1,
    0x3E2,
    0x3E3,
    0x3E4,
    0x3E5,
    0x3E6,
    0x3E7,
    0x3E8,
    0x3E9,
    0x3EA,
    0x3EB,
    0x3EC,
    0x3ED,
    0x3EE,
    0x3EF,
    0x7A0,
    0x7A1,
    0x7A2,
    0x7B0,
    0x7B1,
    0x7C0,
    0x7C2,
    0x7C4,
    0x7C6,
    0x7C8,
    0x7C9,
    0x7CA,
    0x7CB,
    0x7CC,
    0x7CE,
    0x7CF,
    0x7D2,
    0x7D3,
    0x7D4,
    0x7D5,
    0x7D6,
    0x7D7,
    0x7F0,
    0x7F1,
    0x7F2,
    0x7F8,
    0x7F9,
    0x7FF,
    0xB00,
    0xB02,
    0xB03,
    0xB04,
    0xB05,
    0xB06,
    0xB80,
    0xB82,
    0xB83,
    0xB84,
    0xB85,
    0xB86,
    0xBC0,
    0xBC8,
    0xBC9,
    0xBCA,
    0xBCB,
    0xBCC,
    0xF11,
    0xF12,
    0xF13,
    0xF14,
    0xFC0,
    0xFC8,
]

# CSRs available in both U and M modes
UCSR = [
    0x300,
    0x301,
    0x304,
    0x305,
    0x306,
    0x30A,
    0x31A,
    0x320,
    0x323,
    0x324,
    0x325,
    0x326,
    0x340,
    0x341,
    0x342,
    0x343,
    0x344,
    0x3A0,
    0x3A1,
    0x3A2,
    0x3A3,
    0x3A4,
    0x3A5,
    0x3A6,
    0x3A7,
    0x3A8,
    0x3A9,
    0x3AA,
    0x3AB,
    0x3AC,
    0x3AD,
    0x3AE,
    0x3AF,
    0x3B0,
    0x3B1,
    0x3B2,
    0x3B3,
    0x3B4,
    0x3B5,
    0x3B6,
    0x3B7,
    0x3B8,
    0x3B9,
    0x3BA,
    0x3BB,
    0x3BC,
    0x3BD,
    0x3BE,
    0x3BF,
    0x3C0,
    0x3C1,
    0x3C2,
    0x3C3,
    0x3C4,
    0x3C5,
    0x3C6,
    0x3C7,
    0x3C8,
    0x3C9,
    0x3CA,
    0x3CB,
    0x3CC,
    0x3CD,
    0x3CE,
    0x3CF,
    0x3D0,
    0x3D1,
    0x3D2,
    0x3D3,
    0x3D4,
    0x3D5,
    0x3D6,
    0x3D7,
    0x3D8,
    0x3D9,
    0x3DA,
    0x3DB,
    0x3DC,
    0x3DD,
    0x3DE,
    0x3DF,
    0x3E0,
    0x3E1,
    0x3E2,
    0x3E3,
    0x3E4,
    0x3E5,
    0x3E6,
    0x3E7,
    0x3E8,
    0x3E9,
    0x3EA,
    0x3EB,
    0x3EC,
    0x3ED,
    0x3EE,
    0x3EF,
    0x747,
    0x757,
    0x7A0,
    0x7A1,
    0x7A2,
    0x7B0,
    0x7B1,
    0x7C0,
    0x7C2,
    0x7C4,
    0x7C6,
    0x7C8,
    0x7C9,
    0x7CA,
    0x7CB,
    0x7CC,
    0x7CE,
    0x7CF,
    0x7D2,
    0x7D3,
    0x7D4,
    0x7D5,
    0x7D6,
    0x7D7,
    0x7F0,
    0x7F1,
    0x7F2,
    0x7F8,
    0x7F9,
    0x7FF,
    0xB00,
    0xB02,
    0xB03,
    0xB04,
    0xB05,
    0xB06,
    0xB80,
    0xB82,
    0xB83,
    0xB84,
    0xB85,
    0xB86,
    0xBC0,
    0xBC8,
    0xBC9,
    0xBCA,
    0xBCB,
    0xBCC,
    0xC00,
    0xC02,
    0xC03,
    0xC04,
    0xC05,
    0xC06,
    0xC80,
    0xC82,
    0xC83,
    0xC84,
    0xC85,
    0xC86,
    0xF11,
    0xF12,
    0xF13,
    0xF14,
    0xFC0,
    0xFC8,
]


class RegBusItem(uvm_sequence_item):

    def __init__(self, name="RegBusItem"):
        super().__init__(name)
        self.timestamp = 0
        self.rdaddr = 0
        self.rddata = 0
        self.write = 0
        self.wraddr = 0
        self.wrdata = 0
        self.en = 0
        self.reset = 0
        self.wait_enable = False
        self.sample_bus = False
        self.drive_rddata = False
        self.noop = False

    def __str__(self):
        return (
            f"RegBusItem(timestamp={self.timestamp}, en={self.en}, reset={self.reset}, "
            + f"rdaddr={self.rdaddr}, rddata={self.rddata}, "
            + f"wraddr={self.wraddr}, wrdata={self.wrdata}, "
            + f"write={self.write}, wait_enable={self.wait_enable}, "
            + f"sample_bus={self.sample_bus}, drive_rddata={self.drive_rddata}, noop={self.noop}"
            + ")"
        )


class ExtFlagsItem(uvm_sequence_item):

    def __init__(self, name="ExtFlagsItem"):
        super().__init__(name)
        self.ext = MuBiFalse
        self.faulty_core = [MuBiFalse for _ in range(3)]
        self.clr = MuBiFalse
        self.drive_ext = False
        self.wait_for_clr = False
        self.timestamp = 0

    def __str__(self):
        return (
            f"ExtFlagsItem(timestamp={self.timestamp}, "
            + f"ext={self.ext}, faulty_core={self.faulty_core}, clr={self.clr}, "
            + f"drive_ext={self.drive_ext}, wait_for_clr={self.wait_for_clr}"
            + ")"
        )


class CPUCtrlStatusItem(uvm_sequence_item):

    def __init__(self, name="CPUCtrlStatusItem"):
        super().__init__(name)
        self.mpc_debug_halt_req = 0
        self.mpc_debug_halt_ack = 0
        self.mpc_debug_run_req = 0
        self.mpc_debug_run_ack = 0
        self.mpc_reset_run_req = 0
        self.reset = 0
        self.hard_reset = 0
        self.drive_ext = False
        self.wait_req = False
        self.wait_ack = False
        self.sample = False
        self.noop = False
        self.timestamp = 0

    def __eq__(self, other):
        if not isinstance(other, CPUCtrlStatusItem):
            return False
        return (
            self.mpc_debug_halt_req == other.mpc_debug_halt_req
            and self.mpc_debug_halt_ack == other.mpc_debug_halt_ack
            and self.mpc_debug_run_req == other.mpc_debug_run_req
            and self.mpc_debug_run_ack == other.mpc_debug_run_ack
            and self.mpc_reset_run_req == other.mpc_reset_run_req
            and self.reset == other.reset
            and self.hard_reset == other.hard_reset
        )

    def __str__(self):
        return (
            f"CPUCtrlStatusItem(timestamp={self.timestamp}, "
            + f"mpc_debug_halt_req={self.mpc_debug_halt_req}, mpc_debug_halt_ack={self.mpc_debug_halt_ack}, "
            + f"mpc_debug_run_req={self.mpc_debug_run_req}, mpc_debug_run_ack={self.mpc_debug_run_ack}, "
            + f"mpc_reset_run_req={self.mpc_reset_run_req}, reset={self.reset}, hard_reset={self.hard_reset}, "
            + f"drive_ext={self.drive_ext}, wait_req={self.wait_req}, "
            + f"wait_ack={self.wait_ack}, sample={self.sample}, noop={self.noop}"
            + ")"
        )


class FatalStatusItem(uvm_sequence_item):

    def __init__(self, name="FatalStatusItem"):
        super().__init__(name)
        self.fatal = 0
        self.timestamp = 0

    def __str__(self):
        return f"FatalStatusItem(timestamp={self.timestamp}, fatal_err={self.fatal})"


class ResetStatusItem(uvm_sequence_item):

    def __init__(self, name="ResetStatusItem"):
        super().__init__(name)
        self.sync_rst_l = 0
        self.gate = MuBiFalse
        self.timestamp = 0

    def __str__(self):
        return (
            f"HardResetStatusItem(timestamp={self.timestamp}, "
            + f"sync_rst_l={self.sync_rst_l}, gate={self.gate}"
            + ")"
        )


class HardResetStatusItem(uvm_sequence_item):

    def __init__(self, name="HardResetStatusItem"):
        super().__init__(name)
        self.reset = 0
        self.timestamp = 0

    def __str__(self):
        return f"HardResetStatusItem(timestamp={self.timestamp}, rst_l={self.reset})"


# ==============================================================================


class RegBusMonitor(uvm_monitor):
    """
    Monitors the register bus
    """

    sig_names = ["en", "wen", "wraddr", "wrdata", "rdaddr", "rddata"]

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("read_ap", self)

    async def run_phase(self):
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()
            if self.signals["en"].value == MuBiTrue:
                item = RegBusItem()
                item.timestamp = get_sim_time(units="ps")
                item.rdaddr = self.signals["rdaddr"].value
                item.rddata = self.signals["rddata"].value
                item.write = self.signals["wen"].value
                item.wraddr = self.signals["wraddr"].value
                item.wrdata = self.signals["wrdata"].value
                item.reset = self.signals["reset"].value == 0
                self.logger.debug(f"RegBus: {str(item)}")
                self.ap.write(item)


class RegBusDriver(uvm_driver):
    """
    Drives the regsiter bus as subordinate
    """

    sig_names = ["en", "wen", "wraddr", "wrdata", "rdaddr", "rddata"]

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            assert isinstance(it, RegBusItem)
            await ReadWrite()
            if it.wait_enable:
                while self.signals["en"].value != MuBiTrue and self.signals["reset"].value != 0:
                    await RisingEdge(self.clock_domain.clk)
                    await ReadWrite()
                self.seq_item_port.item_done()
            elif it.sample_bus:
                ans = RegBusItem()
                ans.en = self.signals["en"].value
                ans.rdaddr = self.signals["rdaddr"].value
                ans.write = self.signals["wen"].value
                ans.wraddr = self.signals["wraddr"].value
                ans.wrdata = self.signals["wrdata"].value
                ans.reset = self.signals["reset"].value == 0
                self.seq_item_port.item_done(rsp=ans)
            elif it.drive_rddata:
                self.signals["rddata"].value = it.rddata
                await RisingEdge(self.clock_domain.clk)
                await ReadWrite()
                self.seq_item_port.item_done()
            elif it.noop:
                await RisingEdge(self.clock_domain.clk)
                self.seq_item_port.item_done()


class ExternalFlagMonitor(uvm_monitor):
    """
    Monitors the external flag interface
    """

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_flags = None
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()

            curr_flags = {i: self.signals[i].value for i in ["ext", "clr"]}
            curr_flags["faulty_core"] = [sig.value for sig in self.signals["faulty_core"]]

            if prev_flags is None:
                prev_flags = curr_flags

            if prev_flags != curr_flags:
                item = ExtFlagsItem()
                item.timestamp = get_sim_time(units="ps")
                item.ext = curr_flags["ext"]
                item.clr = curr_flags["clr"]
                item.faulty_core = curr_flags["faulty_core"]
                self.logger.debug(f"External flags: {str(item)}")

                self.ap.write(item)
                prev_flags = curr_flags


class ExternalFlagDriver(uvm_driver):
    """
    Drives the external flag interface
    """

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            self.logger.debug(f"Received item {it}")
            assert isinstance(it, ExtFlagsItem)
            await ReadWrite()
            ans = ExtFlagsItem()
            ans.clr = self.signals["clr"].value
            if it.drive_ext:
                self.logger.debug(f"Driving ext with {it.ext}")
                self.signals["ext"].value = it.ext
                for sig, value in zip(self.signals["faulty_core"], it.faulty_core):
                    sig.value = value
                await RisingEdge(self.clock_domain.clk)
            elif it.wait_for_clr:
                while self.signals["clr"].value != MuBiTrue:
                    await RisingEdge(self.clock_domain.clk)
                    await ReadWrite()
                ans.clr = self.signals["clr"].value
            self.seq_item_port.item_done(rsp=ans)


class CPUCtrlStatusMonitor(uvm_monitor):
    """
    Monitors the CPU control interface
    """

    sig_names = [
        "mpc_debug_halt_req",
        "mpc_debug_halt_ack",
        "mpc_debug_run_req",
        "mpc_debug_run_ack",
        "mpc_reset_run_req",
    ]

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]
        self.cpu_side = kwargs["cpu_side"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        del kwargs["cpu_side"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_cpu_state = None
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()

            curr_cpu_state = {i: self.signals[i].value for i in self.sig_names}

            if prev_cpu_state is None:
                prev_cpu_state = curr_cpu_state

            if prev_cpu_state != curr_cpu_state:
                item = CPUCtrlStatusItem()
                item.timestamp = get_sim_time(units="ps")
                for key, value in curr_cpu_state.items():
                    setattr(item, key, value)
                self.logger.debug(f"CPU State: {str(item)}")

                self.ap.write(item)
                prev_cpu_state = curr_cpu_state


class CPUCtrlStatusDriver(uvm_driver):
    """
    Drives the CPU control interface
    """

    sig_names = [
        "mpc_debug_halt_req",
        "mpc_debug_halt_ack",
        "mpc_debug_run_req",
        "mpc_debug_run_ack",
        "mpc_reset_run_req",
    ]

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]
        self.cpu_side = kwargs["cpu_side"]

        del kwargs["signals"]
        del kwargs["clock_domain"]
        del kwargs["cpu_side"]
        super().__init__(*args, **kwargs)

    async def run_cpu_side(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            assert isinstance(it, CPUCtrlStatusItem)
            await ReadWrite()
            if it.drive_ext:
                self.signals["mpc_debug_halt_ack"].value = it.mpc_debug_halt_ack
                self.signals["mpc_debug_run_ack"].value = it.mpc_debug_run_ack
                await RisingEdge(self.clock_domain.clk)
                self.seq_item_port.item_done()
            elif it.wait_req:
                while (
                    self.signals["mpc_debug_halt_req"].value == 0
                    and self.signals["mpc_debug_run_req"].value == 0
                    and self.signals["reset"] == 1
                    and self.signals["hard_reset"] == 1
                ):
                    await RisingEdge(self.clock_domain.clk)
                    await ReadWrite()
                self.seq_item_port.item_done()
            elif it.sample:
                ans = CPUCtrlStatusItem()
                ans.mpc_debug_halt_req = self.signals["mpc_debug_halt_req"].value
                ans.mpc_debug_run_req = self.signals["mpc_debug_run_req"].value
                ans.mpc_reset_run_req = self.signals["mpc_reset_run_req"].value
                ans.reset = self.signals["reset"].value == 0
                ans.hard_reset = self.signals["hard_reset"].value == 0
                self.seq_item_port.item_done(rsp=ans)
            elif it.noop:
                await RisingEdge(self.clock_domain.clk)
                await ReadWrite()
                self.seq_item_port.item_done()
            else:
                assert False, f"{it}"

    async def run_soc_side(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            assert isinstance(it, CPUCtrlStatusItem)
            self.logger.debug(f"SoC Drive: {str(it)}")
            await ReadWrite()
            if it.drive_ext:
                self.signals["mpc_debug_halt_req"].value = it.mpc_debug_halt_req
                self.signals["mpc_debug_run_req"].value = it.mpc_debug_run_req
                self.signals["mpc_reset_run_req"].value = it.mpc_reset_run_req
                await RisingEdge(self.clock_domain.clk)
                self.seq_item_port.item_done()
            elif it.wait_ack:
                while (
                    self.signals["mpc_debug_halt_ack"].value == 0
                    and self.signals["mpc_debug_run_ack"].value == 0
                ):
                    await RisingEdge(self.clock_domain.clk)
                    await ReadWrite()
                self.seq_item_port.item_done()
            elif it.sample:
                ans = CPUCtrlStatusItem()
                ans.mpc_debug_halt_ack = self.signals["mpc_debug_halt_ack"].value
                ans.mpc_debug_run_ack = self.signals["mpc_debug_run_ack"].value
                self.seq_item_port.item_done(rsp=ans)
            elif it.noop:
                await RisingEdge(self.clock_domain.clk)
                await ReadWrite()
                self.seq_item_port.item_done()
            else:
                assert False, f"{it}"

    async def run_phase(self):
        if self.cpu_side:
            await self.run_cpu_side()
        await self.run_soc_side()


class FatalSignalMonitor(uvm_monitor):
    """
    Monitors the fatal_err flag
    """

    def __init__(self, *args, **kwargs):
        self.signal = kwargs["signal"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signal"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_fatal_err = None
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()

            curr_fatal_err = self.signal.value

            if prev_fatal_err is None:
                prev_fatal_err = curr_fatal_err

            if prev_fatal_err != curr_fatal_err:
                item = FatalStatusItem()
                item.timestamp = get_sim_time(units="ps")
                item.fatal = curr_fatal_err
                self.logger.debug(f"Fatal State: {str(item)}")

                self.ap.write(item)
                prev_fatal_err = curr_fatal_err


class ResetStatusMonitor(uvm_monitor):
    """
    Monitors reset and gate signals
    """

    def __init__(self, *args, **kwargs):
        self.sync_rst_l = kwargs["sync_rst_l"]
        self.gate = kwargs["gate"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["sync_rst_l"]
        del kwargs["gate"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_reset = None
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()

            curr_reset = {"sync_rst_l": self.sync_rst_l.value, "gate": self.gate.value}

            if prev_reset is None:
                prev_reset = curr_reset

            if prev_reset != curr_reset:
                item = ResetStatusItem()
                item.timestamp = get_sim_time(units="ps")
                item.sync_rst_l = curr_reset["sync_rst_l"]
                item.gate = curr_reset["gate"]
                self.logger.debug(f"Reset State: {str(item)}")

                self.ap.write(item)
                prev_reset = curr_reset


class HardResetSignalMonitor(uvm_monitor):
    """
    Monitors the FSM hard reset signal
    """

    def __init__(self, *args, **kwargs):
        self.signal = kwargs["signal"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signal"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_rst = None
        while True:
            await RisingEdge(self.clock_domain.clk)
            await ReadOnly()

            curr_rst = self.signal.value

            if prev_rst is None:
                prev_rst = curr_rst

            if prev_rst != curr_rst:
                item = HardResetStatusItem()
                item.timestamp = get_sim_time(units="ps")
                item.reset = curr_rst

                self.ap.write(item)
                prev_rst = curr_rst


# ==============================================================================


class BaseScoreboard(uvm_component):

    def build_phase(self):
        self.logger.setLevel(logging.INFO)
        self.passed = False

        # Register access
        self.recovery_gpr_fifos = [
            uvm_tlm_analysis_fifo(f"recovery_gpr_fifo[{i}]", self) for i in range(3)
        ]
        self.recovery_gpr_ports = [uvm_get_port(f"recovery_gpr_port[{i}]", self) for i in range(3)]

        self.recovery_csr_fifos = [
            uvm_tlm_analysis_fifo(f"recovery_csr_fifo[{i}]", self) for i in range(3)
        ]
        self.recovery_csr_ports = [uvm_get_port(f"recovery_csr_port[{i}]", self) for i in range(3)]

        # CPU Ctrl
        self.external_cpu_ctrl_fifos = [
            uvm_tlm_analysis_fifo(f"external_cpu_ctrl_fifo[{i}]", self) for i in range(3)
        ]
        self.external_cpu_ctrl_ports = [
            uvm_get_port(f"external_cpu_ctrl_port[{i}]", self) for i in range(3)
        ]
        self.internal_cpu_ctrl_fifos = [
            uvm_tlm_analysis_fifo(f"internal_cpu_ctrl_fifo[{i}]", self) for i in range(3)
        ]
        self.internal_cpu_ctrl_ports = [
            uvm_get_port(f"interanl_cpu_ctrl_port[{i}]", self) for i in range(3)
        ]

        # External flag
        self.external_flag_fifo = uvm_tlm_analysis_fifo("external_flag_fifo", self)
        self.external_flag_port = uvm_get_port("external_flag_port", self)

        # Fatal err
        self.fatal_err_fifo = uvm_tlm_analysis_fifo("fatal_err_fifo", self)
        self.fatal_err_port = uvm_get_peek_port("fatal_err_port", self)

        # Sync reset interface
        self.sync_rst_fifo = uvm_tlm_analysis_fifo("sync_rst_fifo", self)
        self.sync_rst_port = uvm_get_peek_port("sync_rst_port", self)

        # Hard FSM reset
        self.hard_rst_fifo = uvm_tlm_analysis_fifo("hard_rst_fifo", self)
        self.hard_rst_port = uvm_get_port("hard_rst_port", self)

    def connect_phase(self):
        # Register access
        for port, fifo in zip(self.recovery_gpr_ports, self.recovery_gpr_fifos):
            port.connect(fifo.get_export)

        for port, fifo in zip(self.recovery_csr_ports, self.recovery_csr_fifos):
            port.connect(fifo.get_export)

        # CPU Ctrl
        for port, fifo in zip(self.external_cpu_ctrl_ports, self.external_cpu_ctrl_fifos):
            port.connect(fifo.get_export)
        for port, fifo in zip(self.internal_cpu_ctrl_ports, self.internal_cpu_ctrl_fifos):
            port.connect(fifo.get_export)

        # External flag
        self.external_flag_port.connect(self.external_flag_fifo.get_export)

        # Fatal err
        self.fatal_err_port.connect(self.fatal_err_fifo.get_peek_export)

        # Sync reset interface
        self.sync_rst_port.connect(self.sync_rst_fifo.get_peek_export)

        # Hard FSM reset
        self.hard_rst_port.connect(self.hard_rst_fifo.get_export)

    def check_phase(self):
        raise NotImplementedError()

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def __init__(self, name, parent, scb_class):
        super().__init__(name, parent)
        self.scb_class = scb_class
        self.clock_domain = parent.clock_domain

    def build_phase(self):

        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 100)
        ConfigDB().set(None, "*", "USER_MODE", 0)

        # Drivers
        # Recovery monitor
        for bus in ["gpr", "csr"]:
            setattr(self, f"{bus}_driver", [])
            for i in range(3):
                getattr(self, f"{bus}_driver").append(
                    RegBusDriver(
                        f"{bus}[{i}]_driver",
                        self,
                        clock_domain=self.clock_domain,
                        signals={
                            sig: getattr(cocotb.top, f"recovery_{bus}_{sig}_veer")[i]
                            for sig in RegBusDriver.sig_names
                        }
                        | {"reset": cocotb.top.sync_rst_l},
                    )
                )
        # CPU control bus
        self.cpu_driver = []
        for i in range(3):
            self.cpu_driver.append(
                CPUCtrlStatusDriver(
                    f"cpu_ctrl[{i}]_cpu_driver",
                    self,
                    clock_domain=self.clock_domain,
                    cpu_side=True,
                    signals={
                        sig: getattr(cocotb.top, f"{sig}_veer")[i]
                        for sig in CPUCtrlStatusDriver.sig_names
                    }
                    | {"reset": cocotb.top.sync_rst_l, "hard_reset": cocotb.top.rst_l},
                )
            )
        self.soc_driver = []
        for i in range(3):
            self.soc_driver.append(
                CPUCtrlStatusDriver(
                    f"cpu_ctrl[{i}]_soc_driver",
                    self,
                    clock_domain=self.clock_domain,
                    cpu_side=False,
                    signals={
                        sig: getattr(cocotb.top, f"ext_{sig}_veer")[i]
                        for sig in CPUCtrlStatusDriver.sig_names
                    }
                    | {"reset": cocotb.top.sync_rst_l},
                )
            )

        # External flag
        self.external_flag_driver = ExternalFlagDriver(
            "external_flag_driver",
            self,
            clock_domain=self.clock_domain,
            signals={
                "ext": getattr(cocotb.top, "external_flag"),
                "clr": getattr(cocotb.top, "clear_external_flag"),
                "faulty_core": getattr(cocotb.top, "faulty_core"),
            },
        )

        # Sequencers
        # Recovery monitor
        for bus in ["gpr", "csr"]:
            setattr(self, f"{bus}_seqr", [])
            for i in range(3):
                getattr(self, f"{bus}_seqr").append(uvm_sequencer(f"{bus}[{i}]_sequencer", self))
        # CPU control bus
        self.cpu_seqr = []
        for i in range(3):
            self.cpu_seqr.append(uvm_sequencer(f"cpu_ctrl[{i}]_cpu_seqr", self))
        self.soc_seqr = []
        for i in range(3):
            self.soc_seqr.append(uvm_sequencer(f"cpu_ctrl[{i}]_soc_seqr", self))

        # External flag
        self.external_flag_seqr = uvm_sequencer("external_flag_seqr", self)

        for i in range(3):
            for bus in ["gpr", "csr"]:
                ConfigDB().set(None, "*", f"{bus.upper()}{i}_SEQ", getattr(self, f"{bus}_seqr")[i])
            ConfigDB().set(None, "*", f"CPU_CTRL{i}_CPU_SEQ", self.cpu_seqr[i])
            ConfigDB().set(None, "*", f"CPU_CTRL{i}_SOC_SEQ", self.soc_seqr[i])
        ConfigDB().set(None, "*", "EXT_FLAG_SEQ", self.external_flag_seqr)

        # Monitors
        # Recovery monitor
        for bus in ["gpr", "csr"]:
            setattr(self, f"{bus}_mon", [])
            for i in range(3):
                getattr(self, f"{bus}_mon").append(
                    RegBusMonitor(
                        f"{bus}[{i}]_mon",
                        self,
                        clock_domain=self.clock_domain,
                        signals={
                            sig: getattr(cocotb.top, f"recovery_{bus}_{sig}_veer")[i]
                            for sig in RegBusMonitor.sig_names
                        }
                        | {"reset": cocotb.top.sync_rst_l},
                    )
                )

        # CPU control bus
        self.cpu_mon = []
        for i in range(3):
            self.cpu_mon.append(
                CPUCtrlStatusMonitor(
                    f"cpu_ctrl[{i}]_cpu_mon",
                    self,
                    clock_domain=self.clock_domain,
                    cpu_side=True,
                    signals={
                        sig: getattr(cocotb.top, f"{sig}_veer")[i]
                        for sig in CPUCtrlStatusMonitor.sig_names
                    }
                    | {"reset": cocotb.top.sync_rst_l},
                )
            )
        self.soc_mon = []
        for i in range(3):
            self.soc_mon.append(
                CPUCtrlStatusMonitor(
                    f"cpu_ctrl[{i}]_soc_mon",
                    self,
                    clock_domain=self.clock_domain,
                    cpu_side=False,
                    signals={
                        sig: getattr(cocotb.top, f"ext_{sig}_veer")[i]
                        for sig in CPUCtrlStatusMonitor.sig_names
                    }
                    | {"reset": cocotb.top.sync_rst_l},
                )
            )

        # External flag
        self.external_flag_mon = ExternalFlagMonitor(
            "external_flag_mon",
            self,
            clock_domain=self.clock_domain,
            signals={
                "ext": getattr(cocotb.top, "external_flag"),
                "clr": getattr(cocotb.top, "clear_external_flag"),
                "faulty_core": getattr(cocotb.top, "faulty_core"),
            },
        )

        # Misc signals
        self.fatal_err_mon = FatalSignalMonitor(
            "fatal_err_mon",
            self,
            clock_domain=self.clock_domain,
            signal=getattr(cocotb.top, "fatal_err"),
        )

        self.reset_mon = ResetStatusMonitor(
            "reset_mon",
            self,
            clock_domain=self.clock_domain,
            sync_rst_l=cocotb.top.sync_rst_l,
            gate=cocotb.top.gate_outputs,
        )

        self.hard_rst_mon = HardResetSignalMonitor(
            "hard_rst_mon",
            self,
            clock_domain=self.clock_domain,
            signal=getattr(cocotb.top, "rst_l"),
        )

        # Scoreboard(s)
        self.scoreboard = None
        if self.scb_class is not None:
            self.scoreboard = self.scb_class("scoreboard", self)

    def connect_phase(self):
        for driver, seqr in zip(self.gpr_driver, self.gpr_seqr):
            driver.seq_item_port.connect(seqr.seq_item_export)
        for driver, seqr in zip(self.csr_driver, self.csr_seqr):
            driver.seq_item_port.connect(seqr.seq_item_export)
        for driver, seqr in zip(self.cpu_driver, self.cpu_seqr):
            driver.seq_item_port.connect(seqr.seq_item_export)
        for driver, seqr in zip(self.soc_driver, self.soc_seqr):
            driver.seq_item_port.connect(seqr.seq_item_export)
        self.external_flag_driver.seq_item_port.connect(self.external_flag_seqr.seq_item_export)

        if self.scoreboard:
            for i, mon in enumerate(self.gpr_mon):
                mon.ap.connect(self.scoreboard.recovery_gpr_fifos[i].analysis_export)
            for i, mon in enumerate(self.csr_mon):
                mon.ap.connect(self.scoreboard.recovery_csr_fifos[i].analysis_export)
            for i, mon in enumerate(self.cpu_mon):
                mon.ap.connect(self.scoreboard.internal_cpu_ctrl_fifos[i].analysis_export)
            for i, mon in enumerate(self.soc_mon):
                mon.ap.connect(self.scoreboard.external_cpu_ctrl_fifos[i].analysis_export)

            self.external_flag_mon.ap.connect(self.scoreboard.external_flag_fifo.analysis_export)
            self.hard_rst_mon.ap.connect(self.scoreboard.hard_rst_fifo.analysis_export)
            self.reset_mon.ap.connect(self.scoreboard.sync_rst_fifo.analysis_export)
            self.fatal_err_mon.ap.connect(self.scoreboard.fatal_err_fifo.analysis_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, scb_class=None):
        super().__init__(name, parent)
        self.scb_class = scb_class
        self.clock_domain = ClockDomain("clk", "rst_l")

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = BaseEnv("env", self, self.scb_class)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def reset(self):

        # Wait, assert reset
        await ClockCycles(cocotb.top.clk, 3)
        cocotb.top.rst_l.value = 0

        cocotb.top.external_flag.value = MuBiFalse
        cocotb.top.scan_mode.value = 0
        for sig in cocotb.top.recovery_gpr_rddata_veer:
            sig.value = 0
        for sig in cocotb.top.recovery_csr_rddata_veer:
            sig.value = 0

        for sig in cocotb.top.mpc_debug_halt_ack_veer:
            sig.value = 0
        for sig in cocotb.top.mpc_debug_run_ack_veer:
            sig.value = 0

        for sig in cocotb.top.ext_mpc_debug_halt_req_veer:
            sig.value = 0
        for sig in cocotb.top.ext_mpc_debug_run_req_veer:
            sig.value = 0
        for sig in cocotb.top.ext_mpc_reset_run_req_veer:
            sig.value = 1

        for sig in cocotb.top.faulty_core:
            sig.value = MuBiFalse

        await ClockCycles(cocotb.top.clk, 2)
        cocotb.top.rst_l.value = 1
        await ClockCycles(cocotb.top.clk, 3)

    async def run_phase(self):
        self.raise_objection()

        # Initialize signals
        cocotb.top.rst_l.value = 1

        # Start clock
        self.start_clock("clk")
        await ClockCycles(cocotb.top.clk, 2)

        # Reset
        await self.reset()

        # Run the test
        await self.run()
        await ClockCycles(cocotb.top.clk, 2)
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
