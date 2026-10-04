#!/bin/sh
# Typed induction on (0, 0.1]: 200 boxes of width 1/2000, run in five chunks of 40 boxes.
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 certify_small.py 0.02 0.0005 0.006 0
python3 certify_small.py 0.04 0.0005 0.006 0.02
python3 certify_small.py 0.06 0.0005 0.006 0.04
python3 certify_small.py 0.08 0.0005 0.006 0.06
python3 certify_small.py 0.1  0.0005 0.006 0.08
python3 small_spider_strict.py
python3 small_hyp_check.py
