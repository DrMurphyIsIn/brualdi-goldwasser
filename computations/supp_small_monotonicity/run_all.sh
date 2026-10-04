#!/bin/sh
# Runs the eight chunks of the monotonicity certificate on [0, 0.198] sequentially (single-threaded).
# Arguments of lemmaS_certify.py: S0 S1 W (range and box width; 0.001 on [0, 0.03], 0.002 beyond).
# The chunks are independent and may also be run in parallel. Logs go to logs/<chunk>.log.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
mkdir -p logs
run() { name=$1; shift; python3 lemmaS_certify.py "$@" > logs/$name.log 2>&1; echo "$name: $(tail -1 logs/$name.log)"; }
run cert_0.0_0.015    0.0   0.015 0.001
run cert_0.015_0.03   0.015 0.03  0.001
run cert_0.03_0.06    0.03  0.06  0.002
run cert_0.06_0.09    0.06  0.09  0.002
run cert_0.09_0.12    0.09  0.12  0.002
run cert_0.12_0.15    0.12  0.15  0.002
run cert_0.15_0.174   0.15  0.174 0.002
run cert_0.174_0.198  0.174 0.198 0.002
