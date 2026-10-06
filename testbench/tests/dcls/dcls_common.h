/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Shared DCLS Skipped Signal Predicates
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Defines the shared `is_skipped_in_dcls()` predicate used by both `dcls.c`
 * and `dcls_skipped_signals.c` so the baseline test and the skipped-signals
 * test form a single-source-of-truth partition across AXI and AHB builds.
 */

#ifndef VEER_TESTBENCH_TESTS_DCLS_DCLS_COMMON_H_
#define VEER_TESTBENCH_TESTS_DCLS_DCLS_COMMON_H_

#include <stdbool.h>
#include <stdint.h>

#include "defines.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Returns `true` if `id` (`old_boot_count`) is skipped in `dcls.c` because
 * forcing that Main Core (`VEER`) signal breaks instruction fetch from `.text`
 * (`0x80000000`), corrupts the DCCM stack, or requires targeted stimulus in
 * `dcls_skipped_signals.c`.
 *
 * @param id Signal injection index (`2 * case_num` for `VEER`,
 *           `2 * case_num + 1` for `LOCKSTEP_CORE`).
 * @return `true` if skipped by `dcls.c` and owned by `dcls_skipped_signals.c`.
 */
static inline bool is_skipped_in_dcls(uint32_t id) {
  if (id == (0 * 2) ||
      id == (2 * 2) || id == (3 * 2) || id == (6 * 2) ||
      id == (9 * 2) || id == (10 * 2) || id == (13 * 2) ||
      id == (18 * 2) || id == (19 * 2) || id == (28 * 2) ||
      id == (33 * 2) ||
#if (SDVT_AHB == 0)
      id == (52 * 2) || id == (63 * 2) || id == (65 * 2) ||
      id == (66 * 2) || id == (67 * 2) ||
      (id >= (100 * 2) && id <= (194 * 2) && (id % 2 == 0))
#else
      id == (48 * 2) || id == (50 * 2) || id == (66 * 2) ||
      (id >= (67 * 2) && id <= (89 * 2) && (id % 2 == 0))
#endif
  ) {
    return true;
  }
  return false;
}

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // VEER_TESTBENCH_TESTS_DCLS_DCLS_COMMON_H_
