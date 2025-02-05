#!/bin/bash

set -ex

apt update
apt install -y git pipx

# By default pipx uses `/root/.local/bin` which isn't in PATH.
export PIPX_BIN_DIR=/usr/local/bin
pipx install git+https://github.com/antmicro/info-process@86db0773
