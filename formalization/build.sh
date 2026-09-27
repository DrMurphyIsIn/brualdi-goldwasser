#!/bin/bash
# Build the whole formalization with bounded memory.
#
# Lake has no option to limit parallelism, and the heaviest certificate files need a lot of memory while
# the kernel checks them (G149/Frag22 alone peaks at about 63 GB; several others need 20-50 GB), so a
# plain cold `lake build` runs out of memory.  This script builds the heavy
# certificate modules explicitly, a few at a time, and then runs `lake build` for everything else
# (which is then cheap).  On an already-built tree every step is a quick no-op.
#
#   ./build.sh          # 1 heavy module at a time: needs about 64 GB free, 96 GB of RAM recommended
#   ./build.sh 2        # 2 at a time: faster; tested on 96 GB (cold build 1 h 14 min on an M3 Ultra)
set -euo pipefail
cd "$(dirname "$0")"
N="${1:-1}"

# Already built?  Then there is nothing to batch.
if lake build --no-build >/dev/null 2>&1; then echo "up to date"; lake build; exit 0; fi

batch() {   # batch SIZE MODULE...
  local size="$1"; shift
  while [ $# -gt 0 ]; do
    local chunk=("${@:1:$size}")
    echo "== ${chunk[*]}"
    lake build "${chunk[@]}"
    shift $(( $# < size ? $# : size ))
  done
}

lake build R3Cert.BGEnvCert.G149.Common R3Cert.BGEnvCert.AssembleK R3Cert.BGSpiderTable R3Cert.BGSpiderMid

g149() { ls R3Cert/BGEnvCert/G149/"$1"*.lean | sed 's|/|.|g; s|\.lean$||'; }
# Heaviest first: the envelope-certificate shards (up to about 63 GB each).
batch "$N" $(g149 SharedTan) $(g149 SharedSp) $(g149 SharedLd) $(g149 Cap) $(g149 Frag)
# Lighter generated certificates.
batch $(( N * 3 )) $(ls R3Cert/BGSpiderTableChunk_*.lean R3Cert/BGSpiderMidCells*.lean R3Cert/BGSpiderMidRoot*.lean | sed 's|/|.|g; s|\.lean$||')
# Everything else.
lake build
