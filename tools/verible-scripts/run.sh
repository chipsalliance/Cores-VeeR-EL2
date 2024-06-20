#!/bin/bash

echo "[LINT] See exec_lint.log"
python verible.py --tool=lint &> exec_lint.log

echo "[FORMAT] See exec_format.log"
python verible.py --tool=format &> exec_format.log

echo "[LINT STATS] See lint.rpt"
python stats_lint.py &> lint.rpt

