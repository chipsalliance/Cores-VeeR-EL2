# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import logging

import cocotb
from pyuvm import uvm_analysis_port, uvm_component, uvm_sequence


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


def get_int(signal):
    try:
        sig = int(signal.value)
    except ValueError:
        sig = 0
    return sig


def get_signals(signals, obj):
    """
    Returns signal objects attached to object.
    It is presumed that "signals" is a list of strings.
    """
    attrs = []
    for sig in signals:
        if hasattr(obj, sig):
            attrs.append(getattr(obj, sig))
        else:
            raise Exception(f"Module {obj} does not have a signal {sig}")
    return attrs


class BaseSeq(uvm_sequence):
    async def run_items(self, items):
        for item in items:
            await self.start_item(item)
            item.randomize()
            await self.finish_item(item)


class BaseMonitor(uvm_component):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        self.ap_req = uvm_analysis_port("ap_req", self)
        self.ap_rsp = uvm_analysis_port("ap_rsp", self)
        self.bfm = None

    async def monitor_req(self):
        while True:
            datum = await self.bfm.req_monitor_q_get()
            self.logger.debug(f"monitor_req: {datum}")
            self.ap_req.write(datum)

    async def monitor_rsp(self):
        while True:
            datum = await self.bfm.rsp_monitor_q_get()
            self.logger.debug(f"monitor_rsp: {datum}")
            self.ap_rsp.write(datum)

    async def run_phase(self):
        cocotb.start_soon(self.monitor_req())
        cocotb.start_soon(self.monitor_rsp())
