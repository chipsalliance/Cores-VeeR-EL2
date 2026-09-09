# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import copy
import random

from pyuvm import ConfigDB, uvm_sequence
from testbench import (
    BaseScoreboard,
    CPUCtrlStatusItem,
    ExtFlagsItem,
    MuBiFalse,
    MuBiTrue,
    RegBusItem,
)


class RegBusScoreboard(BaseScoreboard):

    def build_phase(self):
        super().build_phase()
        self.passed = True
        self.fatal_err_ts = None
        self.hard_rst_ts = None
        period_ps = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        self.period_ns = period_ps * 1000

        self.reg_reads = {
            "gpr": [{}, {}, {}],
            "csr": [{}, {}, {}],
        }
        self.tx_buf = {
            "gpr": [None for _ in range(3)],
            "csr": [None for _ in range(3)],
        }
        self.recovery_ports = {
            "gpr": self.recovery_gpr_ports,
            "csr": self.recovery_csr_ports,
        }

    def load_next_xfer_batch(self, if_name):
        """
        Loads next transaction batch (one for each core in TMR) from the registers bus queue to
        the global variables for later use.
        """
        assert if_name in ["gpr", "csr"]

        if (
            self.recovery_ports[if_name][0].can_get()
            and self.recovery_ports[if_name][1].can_get()
            and self.recovery_ports[if_name][2].can_get()
        ):
            for i in range(3):
                _, self.tx_buf[if_name][i] = self.recovery_ports[if_name][i].try_get()

            setattr(self, f"{if_name}_ts", self.tx_buf[if_name][0].timestamp)
            return True
        # No data in ports
        return False

    def majority_vote(self, val1, val2, val3):
        """
        Vote for the correct value based on 3 inputs. If not possible to pick the winner, return None.
        """
        if val1 == val2:
            return val1
        elif val2 == val3:
            return val2
        elif val1 == val3:
            return val3
        else:
            return None

    def get_rst_after_fatal_err(self):
        """
        Retrieve timestamp of the first hard reset after detected fatal error.
        """
        got_reset = False
        while self.hard_rst_port.can_get():
            got_reset = True
            _, hard_rst_event = self.hard_rst_port.try_get()

            if self.fatal_err_ts > hard_rst_event.timestamp:
                self.logger.debug(
                    f"Skipping hard reset at {hard_rst_event.timestamp}, fatal error was at {self.fatal_err_ts}"
                )
                continue

            if hard_rst_event.reset != 0:
                self.logger.error(
                    f"[{hard_rst_event.timestamp}] Reset deasserted after fatal error! No assertion detected."
                )
                self.passed = False

            # This is first reset after fatal error, leave the loop
            self.hard_rst_ts = hard_rst_event.timestamp
            self.logger.debug(f"[{self.hard_rst_ts}] Found reset after fatal error")

            # Drop fatal_err transition at hard reset from the queue
            if self.fatal_err_port.can_peek():
                _, fatal_err_event = self.fatal_err_port.try_peek()
                if fatal_err_event.timestamp == self.hard_rst_ts:
                    self.fatal_err_port.try_get()

            # Drop reset deassert from the queue
            self.hard_rst_port.try_get()
            break
        if not got_reset:
            self.logger.warning(
                "FSM entered fatal error state but was never reset afterwards! This might suggest invalid test construction."
            )

        # Do not enter this function again unless new fatal err occurred
        self.fatal_err_ts = None

    def check_if_transfers(self, if_name):
        assert if_name in ["gpr", "csr"]

        tr = self.tx_buf[if_name]

        # Collect simultaneous transactions
        reject_xfers = False
        for i in range(3):
            if not isinstance(tr[i], RegBusItem):
                self.passed = False
                self.logger.error(f"Received invalid bus item on {if_name.upper()} port!")
                continue

        if not (tr[0].timestamp == tr[1].timestamp == tr[2].timestamp):
            self.passed = False
            self.logger.error(
                f"Received {if_name.upper()} transactions do not match in time, {tr[0].timestamp} vs {tr[1].timestamp} vs {tr[2].timestamp}"
            )
            return

        tr_ts = tr[0].timestamp
        log_prefix = f"[{tr_ts}] ({if_name.upper()})"
        # Perform initial data checks and save read data for later comparison
        for i in range(3):
            # Discard all operations between fatal error and hard reset
            if self.hard_rst_ts is not None and self.hard_rst_ts > tr[i].timestamp:
                reject_xfers = True
                continue

            read_reg_value = self.reg_reads[if_name][i].get(int(tr[i].rdaddr))
            if tr[i].write and (read_reg_value is None):
                self.passed = False
                self.logger.error(f"{log_prefix} written without prior read at this address")
                continue

            if not tr[i].write:
                # Save read value for later comparison
                self.reg_reads[if_name][i][int(tr[i].rdaddr)] = int(tr[i].rddata)
                self.logger.debug(
                    f"{log_prefix} read value {hex(tr[i].rddata)} at {hex(tr[i].rdaddr)}"
                )

        if reject_xfers:
            self.logger.debug(
                f"{log_prefix} Ignoring transfer that happened between fatal error and hard reset."
            )
            return

        self.logger.debug(
            f"{log_prefix} Majority voting: {hex(tr[0].rddata)} vs {hex(tr[1].rddata)} vs {hex(tr[2].rddata)}"
        )
        rddata_act = self.majority_vote(
            int(tr[0].rddata),
            int(tr[1].rddata),
            int(tr[2].rddata),
        )
        self.logger.debug(f"{log_prefix} Got rddata: {rddata_act}")
        if rddata_act is None:
            self.logger.debug(f"{log_prefix} Voter failed")
            if not self.fatal_err_port.can_get():
                self.passed = False
                self.logger.error(f"{log_prefix} FSM did not report fatal error!")
                return
            _, fatal_event = self.fatal_err_port.try_get()
            self.fatal_err_ts = fatal_event.timestamp
            self.logger.debug(f"{log_prefix} Detected fatal error at {self.fatal_err_ts}")

            # Check if fatal_err was reported exactly one cycle after error
            exp_fatal_ts = tr_ts + self.period_ns
            if (fatal_event.fatal == MuBiTrue) and (self.fatal_err_ts != exp_fatal_ts):
                self.passed = False
                self.logger.error(
                    f"{log_prefix} FSM reported fatal error at unexpected timestamp! Got {self.fatal_err_ts}, expected: {exp_fatal_ts}"
                )
                return
            return

        rddata_exp = self.majority_vote(
            self.reg_reads[if_name][0][int(tr[0].rdaddr)],
            self.reg_reads[if_name][1][int(tr[1].rdaddr)],
            self.reg_reads[if_name][2][int(tr[2].rdaddr)],
        )
        self.logger.debug(f"{log_prefix} Expected rddata: {rddata_exp}")
        for i in range(3):
            if tr[i].write:
                if rddata_exp != int(tr[i].wrdata):
                    self.passed = False
                    self.logger.error(
                        f"{log_prefix} written different value than earlier read at address {hex(tr[i].wraddr)}, expected: {hex(rddata_exp)}, got: {hex(tr[i].wrdata)}"
                    )
                    continue
                if int(tr[i].rddata) not in [0, int(tr[i].wrdata)]:
                    self.passed = False
                    self.logger.error(
                        f"{log_prefix} During write, read data should be either 0 or equal to write data"
                    )
                    continue
                if int(tr[i].wraddr) != int(tr[i].rdaddr):
                    self.passed = False
                    self.logger.error(
                        f"{log_prefix} Simultaneous read and write is only allowed at the same address"
                    )
                    continue

    def check_phase(self):
        # Initiate data buffers
        if not self.load_next_xfer_batch("csr") or not self.load_next_xfer_batch("gpr"):
            self.passed = False
            self.logger.error("At least one register bus transactions port is empty!")

        self.gpr_ts = self.tx_buf["gpr"][0].timestamp
        self.csr_ts = self.tx_buf["csr"][0].timestamp

        # Every test starts with a reset sequence which we don't care about, remove it from FIFO
        for _ in range(2):
            if self.hard_rst_port.can_get():
                _, rst_event = self.hard_rst_port.try_get()
                self.logger.debug(f"[{rst_event.timestamp}] Skipping initial reset event")
                if self.fatal_err_port.can_peek():
                    _, fatal_err_event = self.fatal_err_port.try_peek()
                    if fatal_err_event.timestamp <= rst_event.timestamp:
                        self.fatal_err_port.try_get()
                        self.logger.debug(
                            f"[{fatal_err_event.timestamp}] Skipping initial fatal error event"
                        )

        gpr_port_empty = False
        csr_port_empty = False
        while not gpr_port_empty or not csr_port_empty:
            if self.fatal_err_ts is not None:
                self.get_rst_after_fatal_err()
            if self.gpr_ts < self.csr_ts:
                if not gpr_port_empty:
                    self.check_if_transfers("gpr")
                    gpr_port_empty = not self.load_next_xfer_batch("gpr")
                elif not csr_port_empty:
                    self.check_if_transfers("csr")
                    csr_port_empty = not self.load_next_xfer_batch("csr")
            else:
                if not csr_port_empty:
                    self.check_if_transfers("csr")
                    csr_port_empty = not self.load_next_xfer_batch("csr")
                elif not gpr_port_empty:
                    self.check_if_transfers("gpr")
                    gpr_port_empty = not self.load_next_xfer_batch("gpr")

        if self.fatal_err_port.can_get():
            _, fatl_err_event = self.fatal_err_port.try_get()
            if fatl_err_event == MuBiTrue:
                self.passed = False
                self.logger.error(
                    f"Unexpected fatal error detected, first at {fatl_err_event.timestamp}"
                )

        if self.passed:
            self.logger.info("All scoreboard checks passed")


class CPUReactiveCtrlSequence(uvm_sequence):
    """
    A sequence which responds to control requests
    CPU can be either in halted or running state, so only requests that change state are processed.
    """

    def __init__(self, name, seqr, halt_delay=3, run_delay=1, stop_on_hard_reset=False):
        self.seqr = seqr
        self.halted = False
        self.reset = False
        self.halt_delay = halt_delay
        self.curr_halt_delay = self.halt_delay
        self.run_delay = run_delay
        self.curr_run_delay = self.run_delay
        self.stop_on_hard_reset = stop_on_hard_reset

        super().__init__(name)

    async def body(self):
        while True:
            item = CPUCtrlStatusItem()
            item.wait_req = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)

            item = CPUCtrlStatusItem()
            item.sample = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)

            state = await self.seqr.get_response()
            if state.hard_reset and self.stop_on_hard_reset:
                break
            if state.reset:
                self.reset = True
                item = CPUCtrlStatusItem()
                item.noop = True
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)
                continue

            if self.reset:
                self.reset = False
                self.halted = False if state.mpc_reset_run_req else True
                self.curr_halt_delay = self.halt_delay
                self.curr_run_delay = self.run_delay
                continue

            if not state.mpc_debug_halt_req:
                self.curr_halt_delay = self.halt_delay
            if not state.mpc_debug_run_req:
                self.curr_run_delay = self.run_delay

            if state.mpc_debug_halt_req:
                if not self.halted:
                    self.curr_halt_delay = self.curr_halt_delay - 1
                    item = CPUCtrlStatusItem()
                    item.drive_ext = True
                    await self.seqr.start_item(item)
                    await self.seqr.finish_item(item)
                    if self.curr_halt_delay == 0:
                        self.halted = True
                    continue
            if state.mpc_debug_run_req:
                if self.halted:
                    self.curr_run_delay = self.curr_run_delay - 1
                    item = CPUCtrlStatusItem()
                    item.drive_ext = True
                    await self.seqr.start_item(item)
                    await self.seqr.finish_item(item)
                    if self.curr_run_delay == 0:
                        self.halted = False
                    continue
            item = CPUCtrlStatusItem()
            item.drive_ext = True
            item.mpc_debug_halt_ack = state.mpc_debug_halt_req
            item.mpc_debug_run_ack = state.mpc_debug_run_req
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            item = CPUCtrlStatusItem()
            item.sample = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            state = await self.seqr.get_response()
            if state.mpc_debug_halt_req == 0 and state.mpc_debug_run_req == 0:
                item = CPUCtrlStatusItem()
                item.drive_ext = True
                item.mpc_debug_halt_ack = state.mpc_debug_halt_req
                item.mpc_debug_run_ack = state.mpc_debug_run_req
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)


class CPUNoHaltReactiveCtrlSequence(CPUReactiveCtrlSequence):
    """
    A sequence which responds to control requests
    CPU can be either in halted or running state, so only requests that change state are processed.
    """

    def __init__(self, name, seqr, run_delay=1, stop_on_hard_reset=False):
        super().__init__(
            name, seqr, halt_delay=0, run_delay=run_delay, stop_on_hard_reset=stop_on_hard_reset
        )


class ExternalFlagSequence(uvm_sequence):
    """
    A sequence which drives external flag and responds to clear request
    """

    def __init__(self, name, seqr, clear_delay=0, faulty_core=None):
        self.seqr = seqr
        self.clear_delay = clear_delay
        self.faulty_core = faulty_core
        super().__init__(name)

    async def body(self):
        item = ExtFlagsItem()
        item.ext = MuBiTrue
        item.faulty_core = [MuBiFalse for _ in range(3)]
        if self.faulty_core is not None:
            item.faulty_core[self.faulty_core] = MuBiTrue
        item.drive_ext = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()

        item = ExtFlagsItem()
        item.wait_for_clr = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()

        for _ in range(self.clear_delay):
            item = ExtFlagsItem()
            item.ext = MuBiTrue
            item.faulty_core = [MuBiFalse for _ in range(3)]
            if self.faulty_core is not None:
                item.faulty_core[self.faulty_core] = MuBiTrue
            item.drive_ext = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            _ = await self.seqr.get_response()

        item = ExtFlagsItem()
        item.ext = MuBiFalse
        item.faulty_core = [MuBiFalse for _ in range(3)]
        item.drive_ext = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()


class RecoveryInterfaceSequence(uvm_sequence):
    """
    A sequence which drives recovery interface
    """

    def __init__(self, name, seqr, reg_map=None):
        self.reg_map = {}
        if reg_map is not None:
            self.reg_map = copy.deepcopy(reg_map)
        self.seqr = seqr
        self.random_output = False
        super().__init__(name)

    def update_reg_map(self, reg_map):
        self.reg_map = copy.deepcopy(reg_map)

    def arm_random_response(self):
        self.random_output = True

    async def body(self):
        while True:
            item = RegBusItem()
            item.wait_enable = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)

            sitem = RegBusItem()
            sitem.sample_bus = True
            await self.seqr.start_item(sitem)
            await self.seqr.finish_item(sitem)

            sample = await self.seqr.get_response()
            if sample.reset:
                self.random_output = False
                for reg in self.reg_map:
                    self.reg_map[reg] = 0
                item = RegBusItem()
                item.noop = True
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)
                continue
            elif sample.en == MuBiTrue:
                ritem = RegBusItem()
                ritem.rddata = (
                    self.reg_map[int(sample.rdaddr)] ^ random.randrange(1, 2**32)
                    if self.random_output
                    else self.reg_map[int(sample.rdaddr)]
                )
                ritem.drive_rddata = True
                await self.seqr.start_item(ritem)
                await self.seqr.finish_item(ritem)
                if int(sample.write) == 1:
                    self.reg_map[int(sample.wraddr)] = int(sample.wrdata)
            elif sample.en == MuBiFalse:
                ritem = RegBusItem()
                ritem.rddata = 0
                ritem.drive_rddata = True
                await self.seqr.start_item(ritem)
                await self.seqr.finish_item(ritem)
