#!/bin/bash
# Exact re-checks that emit no Lean (the constants they verify are embedded in hand-assembled Lean files,
# which the kernel checks independently).  Run from this directory.
set -e
echo "== high-degree cell cores (BGSpiderCells.lean constants)";  python3 bg_spider_reduction.py gen-cells
echo "== low-degree rate/root cells (BGSpiderLowDegree.lean constants)"; python3 bg_spider_reduction.py gen-rate
echo "== spider-family structure exchanges (BGSpiderStruct.lean)"; python3 bg_spider_struct_check.py
if [ "$1" = "--full" ]; then
  echo "== independent certified all-tree search, n <= 491 (~16 min, 1 core)"; python3 bg_certified_interval.py 491
fi
