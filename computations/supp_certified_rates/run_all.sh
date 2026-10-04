#!/bin/sh
# Re-runs the 28 certificates of the certified-rates theorem (19 plain, 9 leaf-exempt).
# Each run solves an (untrusted) linear program for the witness and then certifies it rigorously;
# certificates are written to out/. Single-threaded.
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
mkdir -p out
for pq in "1 100" "1 10" "1 4" "2 5" "43 100" "431 1000" "1 2" "3 4" "87 100" "1 1" "119 100" "6 5" "3 2" "2 1" "5 2" "3 1" "16 5" "7 2" "39 10"; do
  echo "== plain $pq"; python3 certify_plain.py $pq || echo "FAILED plain $pq"
done
for pq in "1 10" "1 1" "13 4" "4 1" "5 1" "6 1" "10 1" "30 1" "100 1"; do
  echo "== leaf-exempt $pq"; python3 certify_leafx.py $pq || echo "FAILED leafx $pq"
done
