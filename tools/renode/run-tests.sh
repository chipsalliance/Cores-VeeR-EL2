#!/usr/bin/env bash

set -x
set -e

RENODE_RUN_DIR="$(dirname $0)/renode_run"
RENODE_RUN_VENV_DIR="$(dirname $0)/.venv"

if [[ ! -d "${RENODE_RUN_VENV_DIR}" ]]; then
    python3 -m venv "${RENODE_RUN_VENV_DIR}"
    source "${RENODE_RUN_VENV_DIR}/bin/activate"
    pip install git+https://github.com/antmicro/renode-run
else
    source "${RENODE_RUN_VENV_DIR}/bin/activate"
fi

mkdir -p $RENODE_RUN_DIR
renode-run -a "${RENODE_RUN_DIR}" download
renode-run test -- veer.robot
