#!/bin/sh
# Runs the eight chunks of the band certificate on [0.1, 2.85] sequentially (single-threaded).
# Arguments of run_band.py: LAM0 LAM1 W0 WMAX DELTA (start width, maximal width, built-in slack).
# The chunks are independent and may also be run in parallel. Logs go to logs/<chunk>.log.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
mkdir -p logs
run() { name=$1; shift; python3 run_band.py "$@" > logs/$name.log 2>&1; echo "$name: $(tail -1 logs/$name.log)"; }
run band_0.1_0.15  0.1  0.15 0.0005 0.002 0.0002
run band_0.15_0.2  0.15 0.2  0.001  0.003 0.0002
run band_0.2_0.3   0.2  0.3  0.002  0.005 0.0002
run band_0.3_0.5   0.3  0.5  0.004  0.01  0.0002
run band_0.5_1.0   0.5  1.0  0.01   0.03  0.0003
run band_1.0_1.6   1.0  1.6  0.02   0.05  0.0003
run band_1.6_2.2   1.6  2.2  0.02   0.05  0.0003
run band_2.2_2.85  2.2  2.85 0.01   0.04  0.0003
