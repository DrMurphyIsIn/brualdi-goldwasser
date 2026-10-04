#!/bin/sh
# Runs every chunk of the witness covers of [0.08, 3.22] sequentially (single-threaded).
# The chunks are independent and may also be run in parallel. Logs go to logs/<chunk>.log.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
mkdir -p logs
run() { name=$1; shift; python3 "$@" > logs/$name.log 2>&1; echo "$name: $(tail -1 logs/$name.log)"; }
# power shoulder
run pow_08_10 certify_pow.py 0.08 0.1 0.0005
run pow_10_18 certify_pow.py 0.1 0.18 0.0025
run pow_18_26 certify_pow.py 0.18 0.26 0.0025
run pow_26_34 certify_pow.py 0.26 0.34 0.0025
run pow_34_41 certify_pow.py 0.34 0.41 0.0025
run pow_41_47 certify_pow.py 0.41 0.47 0.0025
# quadratic shoulder, theta = 4/5 and 7/10
run quad08_47_60 certify_quad_t08.py 0.47 0.6 0.0025
run quad08_60_80 certify_quad_t08.py 0.6 0.8 0.0025
run quad_80_110 certify_quad.py 0.8 1.1 0.005
run quad_110_135 certify_quad.py 1.1 1.35 0.005
run quad_135_160 certify_quad.py 1.35 1.6 0.005
# three-piece linear witness
run arm_160_200 certify_arm.py 1.6 2.0 0.01
run arm_200_240 certify_arm.py 2.0 2.4 0.01
run arm_240_270 certify_arm.py 2.4 2.7 0.01
run arm_270_285 certify_arm.py 2.7 2.85 0.01
run arm_285_300 certify_arm.py 2.85 3.0 0.01
run arm_300_310 certify_arm.py 3.0 3.1 0.005
run arm_310_315 certify_arm.py 3.1 3.15 0.0025
run arm_315_320 certify_arm.py 3.15 3.2 0.001
run arm_320_322 certify_arm.py 3.2 3.22 0.0005
