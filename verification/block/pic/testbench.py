#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import *

# ==============================================================================


class RegisterMap:
    """
    Map of PIC memory-mapped registers
    """

    def __init__(self, max_irqs=32, base_addr=0xF00C0000):
        self.reg = dict()
        self.adr = dict()

        self.add_reg("mpiccfg", base_addr + 0x3000)

        for s in range(1, max_irqs):
            name = "meipl{}".format(s)
            addr = base_addr + 4 * s
            self.add_reg(name, addr)

        for x in range(0, max_irqs // 32):
            name = "meip{}".format(x)
            addr = base_addr + 0x1000 + 4 * x
            self.add_reg(name, addr)

        for s in range(1, max_irqs):
            name = "meie{}".format(s)
            addr = base_addr + 0x2000 + 4 * s
            self.add_reg(name, addr)

        for s in range(1, max_irqs):
            name = "meigwctrl{}".format(s)
            addr = base_addr + 0x4000 + 4 * s
            self.add_reg(name, addr)

        for s in range(1, max_irqs):
            name = "meigwclr{}".format(s)
            addr = base_addr + 0x5000 + 4 * s
            self.add_reg(name, addr)

    def add_reg(self, name, addr):
        self.reg[name] = addr
        self.adr[addr] = name


# ==============================================================================


class BusWriteItem(uvm_sequence_item):
    """
    A generic data bus write request / response
    """

    def __init__(self, addr, data):
        super().__init__("BusWriteItem")
        self.addr = addr
        self.data = data

    def randomize(self):
        pass


class BusReadItem(uvm_sequence_item):
    """
    A generic data bus read request / response
    """

    def __init__(self, addr, data=None):
        super().__init__("BusReadItem")
        self.addr = addr
        self.data = data

    def randomize(self):
        pass


class PrioLvlItem(uvm_sequence_item):
    def __init__(self, prio):
        super().__init__("PrioLvlItem")
        self.prio = prio


class PrioThrItem(uvm_sequence_item):
    def __init__(self, prio):
        super().__init__("PrioThrItem")
        self.prio = prio


class IrqItem(uvm_sequence_item):
    def __init__(self, irqs):
        super().__init__("IrqItem")
        self.irqs = irqs


class ClaimItem(uvm_sequence_item):
    def __init__(self, claimid, claimpl, mexintpend, mhwakeup):
        super().__init__("ClaimItem")
        self.claimid = claimid
        self.claimpl = claimpl

        self.mexintpend = mexintpend
        self.mhwakeup = mhwakeup


class WaitItem(uvm_sequence_item):
    """
    A generic wait item. Used to instruct a driver to wait N cycles
    """

    def __init__(self, cycles):
        super().__init__("WaitItem")
        self.cycles = cycles

    def randomize(self):
        pass


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


class RegisterBfm:
    """
    A BFM for the PIC configuration (registers) interface.
    """

    SIGNALS = [
        "picm_rden",
        "picm_rdaddr",
        "picm_rd_data",
        "picm_wren",
        "picm_wraddr",
        "picm_wr_data",
        "picm_mken",
    ]

    def __init__(self, uut, clk):
        # Collect signals
        collect_signals(self.SIGNALS, uut, self)

        # Get the clock
        obj = getattr(uut, clk)
        setattr(self, "picm_clk", obj)

    async def read(self, addr):
        """
        Reads a register
        """

        await RisingEdge(self.picm_clk)

        self.picm_rdaddr.value = addr
        self.picm_rden.value = 1
        self.picm_mken.value = 0

        await RisingEdge(self.picm_clk)

        self.picm_rden.value = 0

        await FallingEdge(self.picm_clk)

        data = self.picm_rd_data.value

        return data

    async def write(self, addr, data):
        """
        Writes a register
        """

        await RisingEdge(self.picm_clk)

        self.picm_wraddr.value = addr
        self.picm_wr_data.value = data
        self.picm_wren.value = 1
        self.picm_mken.value = 0

        await RisingEdge(self.picm_clk)

        self.picm_wren.value = 0


class RegisterDriver(uvm_driver):
    """
    Configuration (register) interface driver
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, BusWriteItem):
                await self.bfm.write(it.addr, it.data)
            elif isinstance(it, BusReadItem):
                it.data = await self.bfm.read(it.addr)
            elif isinstance(it, WaitItem):
                await ClockCycles(self.bfm.picm_clk)
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class RegisterMonitor(uvm_component):
    """
    Configuration (register) interface monitor
    """

    def __init__(self, *args, **kwargs):
        self.bfm = kwargs["bfm"]
        del kwargs["bfm"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            await RisingEdge(self.bfm.picm_clk)

            # Read
            if self.bfm.picm_rden.value:
                addr = int(self.bfm.picm_rdaddr.value)

                await FallingEdge(self.bfm.picm_clk)

                data = int(self.bfm.picm_rd_data.value)
                self.logger.debug("read  0x{:08X} -> 0x{:08X}".format(addr, data))
                self.ap.write(BusReadItem(addr, data))

            # Write
            if self.bfm.picm_wren.value:
                addr = int(self.bfm.picm_wraddr.value)
                data = int(self.bfm.picm_wr_data.value)
                self.logger.debug("write 0x{:08X} <- 0x{:08X}".format(addr, data))
                self.ap.write(BusWriteItem(addr, data))


# ==============================================================================


class PrioDriver(uvm_driver):
    """
    A driver for priority and priority threshold inputs of the PIC
    """

    SIGNALS = [
        "meicurpl",
        "meipt",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, PrioLvlItem):
                self.meicurpl.value = it.prio
            elif isinstance(it, PrioThrItem):
                self.meipt.value = it.prio
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class PrioMonitor(uvm_component):
    """
    A monitor for priority and priority threshold of the PIC
    """

    SIGNALS = [
        "clk",
        "meicurpl",
        "meipt",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.prev_meicurpl = None
        self.prev_meipt = None

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Even though the signals are not registered sample them on
            # rising clock edge
            await RisingEdge(self.clk)

            # Sample signals
            curr_meicurpl = int(self.meicurpl.value)
            curr_meipt = int(self.meipt.value)

            # Send an item in case of a change
            if self.prev_meicurpl != curr_meicurpl:
                self.ap.write(PrioLvlItem(curr_meicurpl))
            if self.prev_meipt != curr_meipt:
                self.ap.write(PrioThrItem(curr_meipt))

            self.prev_meicurpl = curr_meicurpl
            self.prev_meipt = curr_meipt


# ==============================================================================


class IrqDriver(uvm_driver):
    """
    A driver for interrupt requests
    """

    SIGNALS = [
        "extintsrc_req",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, IrqItem):
                self.extintsrc_req.value = it.irqs
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class IrqMonitor(uvm_component):
    """
    A monitor for interrupt requests
    """

    SIGNALS = [
        "clk",
        "extintsrc_req",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.prev_irqs = None

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Sample signals
            await RisingEdge(self.clk)
            curr_irqs = int(self.extintsrc_req.value)

            # Send an item in case of a change
            if self.prev_irqs != curr_irqs:
                self.ap.write(IrqItem(curr_irqs))

            self.prev_irqs = curr_irqs


# ==============================================================================


class ClaimMonitor(uvm_component):
    SIGNALS = [
        "clk",
        "extintsrc_req",
        "picm_wren",
        "claimid",
        "pl",
        "mexintpend",
        "mhwakeup",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.prev_irqs = 0
        self.prev_wren = 0

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Sample control signals
            await RisingEdge(self.clk)
            irqs = int(self.extintsrc_req.value)
            wren = int(self.picm_wren.value)

            is_wren = wren and not self.prev_wren  # Rising edge of wren
            is_irqs = irqs & ~self.prev_irqs  # Rising edge of any IRQ

            if is_wren or is_irqs:
                # Sample signals after a delay to give PIC time to react.
                # It was observed that in the simulation that the wait must
                # be at least 3 clock cycles long.
                await ClockCycles(self.clk, 3)

                claimid = int(self.claimid.value)
                claimpl = int(self.pl.value)
                mexintpend = int(self.mexintpend.value)
                mhwakeup = int(self.mhwakeup.value)

                self.ap.write(ClaimItem(claimid, claimpl, mexintpend, mhwakeup))

            self.prev_irqs = irqs
            self.prev_wren = wren


# ==============================================================================


class PriorityPredictor:
    class Irq:
        """
        Interrupt request state
        """

        def __init__(self, n):
            self.id = n
            self.priority = 0
            self.enabled = False
            self.triggered = False

        def __str__(self):
            return "id={:3d} en={} pri={:2d} trg={}".format(
                self.id,
                int(self.enabled),
                self.priority,
                int(self.triggered),
            )

        def __repr__(self):
            return str(self)

    def __init__(self, logger=None):
        self.inv_order = False
        self.irqs = {i: self.Irq(i) for i in range(1, 32)}
        self.logger = logger

        if self.logger is None:
            self.logger = uvm_root().logger

    def predict(self):
        # Dump IRQs
        self.logger.debug("IRQs:")
        keys = sorted(list(self.irqs))
        for k in keys:
            self.logger.debug(" " + str(self.irqs[k]))

        # Filter only enabled and triggered
        irqs = {k: v for k, v in self.irqs.items() if v.enabled and v.triggered}

        # Get the highest priority
        pred = None
        for irq in irqs.values():
            # Skip priority 0 or 15
            if self.inv_order:
                if irq.priority == 15:
                    continue
            else:
                if irq.priority == 0:
                    continue

            # Find max priority and min id
            if pred is None:
                pred = irq
            else:
                if self.inv_order:
                    if irq.priority < pred.priority:
                        pred = irq
                else:
                    if irq.priority > pred.priority:
                        pred = irq

                if irq.priority == pred.priority:
                    if irq.id < pred.id:
                        pred = irq

        if pred is None:
            return self.Irq(0)

        self.logger.debug("pred:")
        self.logger.debug(" " + str(pred))

        return pred


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "PIC_NUM_INTERRUPTS", 32)
        ConfigDB().set(None, "*", "PIC_NUM_PRIORITIES", 15)

        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 50)
        ConfigDB().set(None, "*", "TEST_IRQ_ENA_PROB", 0.75)
        ConfigDB().set(None, "*", "TEST_IRQ_REQ_PROB", 0.90)

        # Sequencers
        self.reg_seqr = uvm_sequencer("reg_seqr", self)
        self.pri_seqr = uvm_sequencer("pri_seqr", self)
        self.irq_seqr = uvm_sequencer("irq_seqr", self)

        # Register interface
        bfm = RegisterBfm(cocotb.top, "clk")
        self.reg_drv = RegisterDriver("reg_drv", self, bfm=bfm)
        self.reg_mon = RegisterMonitor("reg_mon", self, bfm=bfm)

        # Current priority and priority threshold interface
        self.pri_drv = PrioDriver("pri_drv", self, uut=cocotb.top)
        self.pri_mon = PrioMonitor("pri_mon", self, uut=cocotb.top)

        # Interrupt request
        self.irq_drv = IrqDriver("irq_drv", self, uut=cocotb.top)
        self.irq_mon = IrqMonitor("irq_mon", self, uut=cocotb.top)

        # Interrupt claim monitor
        self.claim_mon = ClaimMonitor("claim_mon", self, uut=cocotb.top)

        ConfigDB().set(None, "*", "REG_SEQR", self.reg_seqr)
        ConfigDB().set(None, "*", "PRI_SEQR", self.pri_seqr)
        ConfigDB().set(None, "*", "IRQ_SEQR", self.irq_seqr)

    def connect_phase(self):
        self.reg_drv.seq_item_port.connect(self.reg_seqr.seq_item_export)
        self.pri_drv.seq_item_port.connect(self.pri_seqr.seq_item_export)
        self.irq_drv.seq_item_port.connect(self.irq_seqr.seq_item_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self):
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("free_clk")

        # Issue reset
        await self.do_reset()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
