# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0
import logging
from collections.abc import Callable

from scipy.stats import binom

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


def collect_bytes(data, strb=None):
    """
    Collects data bytes asserted on a data bus. Uses the strb value to
    determine which octets are valid. Both data and strb must be cocotb
    signals. strb can be None.
    """

    if strb is not None:
        assert len(data) == 8 * len(strb)

    res = []
    for i in range(len(data) // 8):
        if strb is None or strb.value & (1 << i):
            dat = (int(data.value) >> (8 * i)) & 0xFF
            res.append(dat)

    return bytes(res)


def smallest_number_of_trials(p: float, k: int, j: float):
    """
    This function is used to calculate the minimum number of clock cycles that
    need to pass for an event to be successful given the probability of its
    conditions occurring.

    Example:
        Let module under test enter into a busy state with probability `p`.
        For an event A to occur the module must not be in the busy state.

        Then, n = smallest_number_of_trials(p, 1, 99.9) is the smallest number
        of clock cycles that need to pass for there being 99.9% chance that at least
        one event A occurs in this n-cycle period.

    (see verification/block/dma)

    Based on https://math.stackexchange.com/a/4776687.

    Returns the smallest n such that
    P(X >= k) >= j / 100, where X is Binomial(n, p).
    """

    def function_bisect(f: Callable[[int], float], target: float) -> float:
        """
        f is an increasing function from the nonnegative integers to floats.
        Returns the smallest x such that f(x) >= target.
        WARNING: This loops forever if there is no x for which f(x) >= target.
        """

        lower_lim = 0
        if f(lower_lim) >= target:
            return lower_lim

        upper_lim = 2
        while f(upper_lim) < target:
            upper_lim *= 2

        while upper_lim - lower_lim >= 2:
            mid = (lower_lim + upper_lim) // 2
            if f(mid) >= target:
                upper_lim = mid
            elif f(mid) < target:
                lower_lim = mid
        return upper_lim

    def prob_X_ge_k(n):
        return 1 - binom.cdf(k - 1, n, p)

    return function_bisect(prob_X_ge_k, j / 100)
