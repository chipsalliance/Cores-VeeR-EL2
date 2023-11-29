# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0
import logging

# ==============================================================================


def collect_signals(signals, uut, obj, uut_prefix="", obj_prefix="", signal_map=None):
    """
    Collects signal objects from UUT and attaches them to the given object.
    Optionally UUT signals can be prefixed with the uut_prefix and object
    signals with the obj_prefix. If signal_map is given it should be a dict
    mapping signal names to actual UUT signal names.
    """

    for sig in signals:
        if signal_map is not None:
            uut_sig = signal_map.get(sig, uut_prefix + sig)
        else:
            uut_sig = uut_prefix + sig
        obj_sig = obj_prefix + sig
        if hasattr(uut, uut_sig):
            s = getattr(uut, uut_sig)

        else:
            s = None
            logging.error("Module {} does not have a signal '{}'".format(str(uut), sig))

        setattr(obj, obj_sig, s)
