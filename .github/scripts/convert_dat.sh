#!/bin/bash

DAT_FILE="${1}"
INFO_FILE="${2}"

verilator_coverage --filter-type toggle --write-info "${INFO_FILE}_branch.info" "${DAT_FILE}"
verilator_coverage --filter-type 'line|branch|expr|fsm_state|fsm_arc' --write-info "${INFO_FILE}_toggle.info" "${DAT_FILE}"
