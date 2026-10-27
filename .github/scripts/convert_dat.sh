#!/bin/bash

DAT_FILE="${1}"
INFO_FILE="${2}"

# verilator_coverage --filter-type only accepts a single coverage type per call.
# First extract non-toggle coverage types (line, branch, expr, fsm_state, fsm_arc)
# into temporary .dat files, then combine them into ${INFO_FILE}_branch.info
# (which prepare_coverage_data.sh later splits into _line.info, _cond.info, and
# _branch.info) and remove (--unlink) the temporary .dat files once written.
verilator_coverage --filter-type line --write "${INFO_FILE}_line.dat" "${DAT_FILE}"
verilator_coverage --filter-type branch --write "${INFO_FILE}_branch.dat" "${DAT_FILE}"
verilator_coverage --filter-type expr --write "${INFO_FILE}_expr.dat" "${DAT_FILE}"
verilator_coverage --filter-type fsm_state --write "${INFO_FILE}_fsm_state.dat" "${DAT_FILE}"
verilator_coverage --filter-type fsm_arc --write "${INFO_FILE}_fsm_arc.dat" "${DAT_FILE}"
verilator_coverage --unlink --write-info "${INFO_FILE}_branch.info" \
  "${INFO_FILE}_line.dat" "${INFO_FILE}_branch.dat" "${INFO_FILE}_expr.dat" \
  "${INFO_FILE}_fsm_state.dat" "${INFO_FILE}_fsm_arc.dat"

# Extract toggle coverage separately into ${INFO_FILE}_toggle.info.
verilator_coverage --filter-type toggle --write-info "${INFO_FILE}_toggle.info" "${DAT_FILE}"

# Convert user (cover property) coverage into ${INFO_FILE}_fcov.info with BRDA
# entries so Coverview renders functional coverage tables.
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
REPO_ROOT="$(readlink -f "${SCRIPT_DIR}/../..")"
python3 "${SCRIPT_DIR}/convert_verilator_fcov_to_lcov.py" \
  --dat "${DAT_FILE}" \
  --repo-root "${REPO_ROOT}" \
  --output "${INFO_FILE}_fcov.info"

