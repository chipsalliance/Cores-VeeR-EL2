#!/bin/bash

DAT_FILE="${1}"
INFO_FILE="${2}"

verilator_coverage --write-info "${INFO_FILE}.info" "${DAT_FILE}"
