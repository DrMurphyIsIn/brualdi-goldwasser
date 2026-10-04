#!/bin/sh
# Hinge on [1+sqrt5, 100] and the chain route on [100, 2000], sequentially (single-threaded).
# certify_large.py takes LAM0 LAM1 RATIO (lambda-boxes grow geometrically by RATIO).
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
mkdir -p logs
python3 certify_L5.py 100 > logs/hinge_L5.log 2>&1; echo "hinge: $(tail -1 logs/hinge_L5.log)"
for r in "100 300" "300 700" "700 1300" "1300 2000"; do
  set -- $r; python3 certify_large.py $1 $2 1.1 > logs/large_$1_$2.log 2>&1; echo "large_$1_$2: $(tail -1 logs/large_$1_$2.log)"
done
