#!/bin/bash

DAT_FILE="${1}"
INFO_FILE="${2}"

verilator_coverage --skip-toggle --write-info "${INFO_FILE}_branch.info" "${DAT_FILE}"
verilator_coverage --toggle-only --write-info "${INFO_FILE}_toggle.info" "${DAT_FILE}"
