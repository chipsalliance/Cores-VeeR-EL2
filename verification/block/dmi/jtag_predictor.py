# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import os

from cocotb.types import Logic, LogicArray, Range, concat
from common import *
from jtag_pkg import *


class JTAGPredictor:
    """
    A predictor for JTAG TAP that is able to calculate current states of
    internal FSM, registers and output ports.
    """

    def __init__(self, dut):
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))

        self.AWIDTH = AWIDTH = ConfigDB().get(None, "", "AWIDTH")
        self.reg_range = Range(AWIDTH + 33, "downto", 0)
        self.logger = uvm_root().logger
        self.logger.setLevel(level)
        self.dut = dut

        # Predicted output ports
        self.tdo = Logic(0)
        self.tdo_next = Logic(0)
        self.tdoEnable = Logic(0)
        self.wr_data = LogicArray(0, Range(31, "downto", 0))
        self.wr_addr = LogicArray(0, Range(AWIDTH - 1, "downto", 0))
        self.wr_en = Logic(0)
        self.rd_en = Logic(0)
        self.dmi_hard_reset = Logic(0)

        # JTAG input ports
        self.rd_data = dut.rd_data
        self.trst_n = dut.trst_n
        self.tms = dut.tms
        self.tdi = dut.tdi

        # Internal JTAG state and registers
        self.nstate = JTAGStates.TEST_LOGIC_RESET_STATE
        self.state = self.nstate
        self.prev_nstate = self.state
        self.ir = LogicArray(0x1, Range(4, "downto", 0))
        self.dr = LogicArray(0x0, self.reg_range)
        self.ndr = LogicArray(0x0, self.reg_range)
        self.sr = LogicArray(0x0, self.reg_range)
        self.nsr = LogicArray(0x0, self.reg_range)

    def __str__(self):
        str = "TAP Controller currently in state: {}\n".format(JTAGStates(self.state).name)
        str += "Expected vs actual outputs:\n"
        str += "tdo:            {} vs {}\n".format(hex(int(self.tdo)), hex(self.dut.tdo.value))
        str += "tdoEnable:      {} vs {}\n".format(
            hex(int(self.tdoEnable)), hex(self.dut.tdoEnable.value)
        )
        str += "wr_data:        {} vs {}\n".format(
            hex(self.wr_data.integer), hex(self.dut.reg_wr_data.value)
        )
        str += "wr_addr:        {} vs {}\n".format(
            hex(self.wr_addr.integer), hex(self.dut.reg_wr_addr.value)
        )
        str += "wr_en:          {} vs {}\n".format(
            hex(int(self.wr_en)), hex(self.dut.reg_wr_en.value)
        )
        str += "rd_en:          {} vs {}\n".format(hex(int(self.rd_en)), hex(self.dut.reg_en.value))
        str += "dmi_hard_reset: {} vs {}".format(
            hex(int(self.dmi_hard_reset)), hex(self.dut.dmi_hard_reset.value)
        )

        return str

    def update_state(self):
        if self.state != self.nstate:
            self.logger.debug(
                "Switching state {} to {}".format(
                    JTAGStates(self.state).name,
                    JTAGStates(self.nstate).name,
                )
            )
        self.state = self.nstate

    def update_nstate(self):
        """
        State machine compliant with TAP Controller documentation (IEEE Std 1149.1-2001)
        and VeeR EL2 specific TAP implementation.
        """
        self.prev_nstate = self.nstate
        if self.trst_n == 0:
            self.nstate = JTAGStates.TEST_LOGIC_RESET_STATE
            pass

        if self.state == JTAGStates.TEST_LOGIC_RESET_STATE:
            self.nstate = (
                JTAGStates.TEST_LOGIC_RESET_STATE
                if get_int(self.tms) == 1
                else JTAGStates.RUN_TEST_IDLE_STATE
            )

        elif self.state == JTAGStates.RUN_TEST_IDLE_STATE:
            self.nstate = (
                JTAGStates.SELECT_DR_SCAN_STATE
                if get_int(self.tms) == 1
                else JTAGStates.RUN_TEST_IDLE_STATE
            )

        elif self.state == JTAGStates.SELECT_DR_SCAN_STATE:
            self.nstate = (
                JTAGStates.SELECT_IR_SCAN_STATE
                if get_int(self.tms) == 1
                else JTAGStates.CAPTURE_DR_STATE
            )

        elif self.state == JTAGStates.CAPTURE_DR_STATE:
            self.nstate = (
                JTAGStates.EXIT1_DR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_DR_STATE
            )

        elif self.state == JTAGStates.SHIFT_DR_STATE:
            self.nstate = (
                JTAGStates.EXIT1_DR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_DR_STATE
            )

        elif self.state == JTAGStates.EXIT1_DR_STATE:
            self.nstate = (
                JTAGStates.UPDATE_DR_STATE if get_int(self.tms) == 1 else JTAGStates.PAUSE_DR_STATE
            )

        elif self.state == JTAGStates.PAUSE_DR_STATE:
            self.nstate = (
                JTAGStates.EXIT2_DR_STATE if get_int(self.tms) == 1 else JTAGStates.PAUSE_DR_STATE
            )

        elif self.state == JTAGStates.EXIT2_DR_STATE:
            self.nstate = (
                JTAGStates.UPDATE_DR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_DR_STATE
            )

        elif self.state == JTAGStates.UPDATE_DR_STATE:
            self.nstate = (
                JTAGStates.SELECT_DR_SCAN_STATE
                if get_int(self.tms) == 1
                else JTAGStates.RUN_TEST_IDLE_STATE
            )

        elif self.state == JTAGStates.SELECT_IR_SCAN_STATE:
            self.nstate = (
                JTAGStates.TEST_LOGIC_RESET_STATE
                if get_int(self.tms) == 1
                else JTAGStates.CAPTURE_IR_STATE
            )

        elif self.state == JTAGStates.CAPTURE_IR_STATE:
            self.nstate = (
                JTAGStates.EXIT1_IR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_IR_STATE
            )

        elif self.state == JTAGStates.SHIFT_IR_STATE:
            self.nstate = (
                JTAGStates.EXIT1_IR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_IR_STATE
            )

        elif self.state == JTAGStates.EXIT1_IR_STATE:
            self.nstate = (
                JTAGStates.UPDATE_IR_STATE if get_int(self.tms) == 1 else JTAGStates.PAUSE_IR_STATE
            )

        elif self.state == JTAGStates.PAUSE_IR_STATE:
            self.nstate = (
                JTAGStates.EXIT2_IR_STATE if get_int(self.tms) == 1 else JTAGStates.PAUSE_IR_STATE
            )

        elif self.state == JTAGStates.EXIT2_IR_STATE:
            self.nstate = (
                JTAGStates.UPDATE_IR_STATE if get_int(self.tms) == 1 else JTAGStates.SHIFT_IR_STATE
            )

        elif self.state == JTAGStates.UPDATE_IR_STATE:
            self.nstate = (
                JTAGStates.SELECT_DR_SCAN_STATE
                if get_int(self.tms) == 1
                else JTAGStates.RUN_TEST_IDLE_STATE
            )

        else:
            self.nstate = JTAGStates.TEST_LOGIC_RESET_STATE

        if self.prev_nstate != self.nstate:
            self.logger.debug(
                "Switching nstate {} to {}".format(
                    JTAGStates(self.prev_nstate).name,
                    JTAGStates(self.nstate).name,
                )
            )

    def predict_regs_posedge(self):
        """
        Calculate values of internal registers IR, DR and SR
        """
        self.dr = self.ndr

        if self.trst_n == 0:
            self.sr = LogicArray(0, self.reg_range)
        else:
            self.sr = LogicArray(get_int(self.nsr), self.reg_range)

        if self.trst_n == 0:
            self.nsr = LogicArray(0, self.nsr.range)
            self.ir = LogicArray(1, self.ir.range)
            self.ndr = LogicArray(0, self.dr.range)

        if self.state == JTAGStates.UPDATE_IR_STATE:
            self.ir = (
                LogicArray(0x1F, self.ir.range) if (self.sr[4:0].integer == 0) else self.sr[4:0]
            )

        if self.state == JTAGStates.UPDATE_DR_STATE and self.ir == JTAGInstructions.DR_EN_1:
            self.ndr = LogicArray(get_int(self.sr), self.reg_range)
        else:
            self.ndr = concat(self.dr[self.AWIDTH + 33 : 2], LogicArray(0, range(2)))

        self.predict_nsr_reg()

    def predict_nsr_reg(self):
        """
        Calculate next value of the SR register
        """
        tdi_lr = LogicArray(get_int(self.tdi))
        self.nsr = LogicArray(get_int(self.sr), self.reg_range)

        # Predict value of nsr register
        if self.state == JTAGStates.SHIFT_DR_STATE:
            if self.ir == JTAGInstructions.DR_EN_1:
                self.nsr = concat(tdi_lr, self.sr[self.AWIDTH + 33 : 1])

            elif self.ir in [JTAGInstructions.DR_EN_0, JTAGInstructions.DEVICE_ID_SEL]:
                self.nsr = concat(
                    LogicArray(0, range(self.AWIDTH + 2)), concat(tdi_lr, self.sr[31:1])
                )

            else:
                self.nsr = LogicArray(get_int(self.tdi), self.nsr.range)

        elif self.state == JTAGStates.CAPTURE_DR_STATE:
            self.nsr[0] = 0
            if self.ir == JTAGInstructions.DR_EN_0:
                self.nsr = concat(
                    LogicArray(0, range(self.AWIDTH + 19)),
                    concat(
                        concat(concat(JTAGDefaults.IDLE, JTAGDefaults.DMI_STAT), Defaults.ABITS),
                        JTAGDefaults.VERSION,
                    ),
                )

            elif self.ir == JTAGInstructions.DR_EN_1:
                self.nsr = concat(
                    concat(
                        LogicArray(0, range(self.AWIDTH)),
                        LogicArray(self.rd_data.value, Range(31, "downto", 0)),
                    ),
                    JTAGDefaults.RD_STATUS,
                )

            elif self.ir == JTAGInstructions.DEVICE_ID_SEL:
                self.nsr = concat(
                    LogicArray(0, range(self.AWIDTH + 2)), concat(Defaults.JTAG_ID, LogicArray(1))
                )

        elif self.state == JTAGStates.SHIFT_IR_STATE:
            self.nsr = concat(LogicArray(0, range(self.AWIDTH + 29)), concat(tdi_lr, self.sr[4:1]))

        elif self.state == JTAGStates.CAPTURE_IR_STATE:
            self.nsr = LogicArray(1, self.reg_range)

    def predict_regs_negedge(self):
        self.tdo = Logic(get_int(self.sr[0]))
        self.tdoEnable = (
            Logic(1)
            if self.state in [JTAGStates.SHIFT_DR_STATE, JTAGStates.SHIFT_IR_STATE]
            else Logic(0)
        )
        self.predict_nsr_reg()

    def predict_ports(self):
        """
        Calculate JTAG TAP output ports' values
        """

        self.tdoEnable = (
            Logic(1)
            if self.state in [JTAGStates.SHIFT_DR_STATE, JTAGStates.SHIFT_IR_STATE]
            else Logic(0)
        )

        self.wr_addr = LogicArray(get_int(self.dr[self.AWIDTH + 34 - 1 : 34]))
        self.wr_data = LogicArray(get_int(self.dr[33:2]))
        self.wr_en = Logic(get_int(self.dr[1]))
        self.rd_en = Logic(get_int(self.dr[0]))

        if self.trst_n == 0:
            self.dmi_hard_reset = Logic(0)
        if self.state == JTAGStates.UPDATE_DR_STATE and self.ir == JTAGInstructions.DR_EN_0:
            self.dmi_hard_reset = Logic(get_int(self.sr[17]))
        else:
            self.dmi_hard_reset = Logic(0)

    def predict_jtag_outputs(self, edge):
        """
        Predict JTAG TAP internal state and outputs based on current inputs.
        This method is assumed to be executed just after detecting an edge of
        the clock. Since it must know previous state of the FSM, prediction
        should be executed after each clock edge.
        """

        assert edge in ["pos", "neg"]

        self.update_nstate()

        if edge == "pos":
            self.update_state()
            self.predict_regs_posedge()
        else:
            self.predict_regs_negedge()

        self.predict_ports()
        self.logger.debug(str(self))
        self.logger.debug("Internal registers:")
        self.logger.debug("nsr: {}".format(self.nsr))
        self.logger.debug("sr:  {}".format(self.sr))
        self.logger.debug("dr:  {}".format(self.dr))
        self.logger.debug("ir:  {}\n".format(self.ir))
