#!/bin/bash
# Regenerate every certificate family from scratch and check it against the frozen Telperion record and
# the Lean sources; then run the exact re-checks.  Needs python3 >= 3.11 with sympy, numpy, mpmath, networkx.
set -e
cd "$(dirname "$0")"
for f in spider_table envcert_g149 mid_cells cand_certs; do python3 $f/generate.py; done
(cd checks && ./run_checks.sh "$@")
echo "all certificate families reproduce exactly"
