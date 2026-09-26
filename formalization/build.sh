#!/bin/bash
# Build the whole formalization with bounded memory.
#
# Lake has no option to limit parallelism, and some certificate files need 15-35 GiB each while the
# kernel checks them, so a plain cold `lake build` can run out of memory.  This script builds the heavy
# certificate modules explicitly, a few at a time, and then runs `lake build` for everything else
# (which is then cheap).  On an already-built tree every step is a quick no-op.
#
#   ./build.sh          # 3 heavy modules at a time (about 64 GiB of memory is comfortable)
#   ./build.sh 6        # more at a time, if you have the memory
set -euo pipefail
cd "$(dirname "$0")"
N="${1:-3}"

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
# Heaviest first: the envelope-certificate shards (15-35 GiB each).
batch "$N" $(g149 SharedTan) $(g149 SharedSp) $(g149 SharedLd) $(g149 Cap) $(g149 Frag)
# Lighter generated certificates.
batch $(( N * 3 )) $(ls R3Cert/BGSpiderTableChunk_*.lean R3Cert/BGSpiderMidCells*.lean R3Cert/BGSpiderMidRoot*.lean | sed 's|/|.|g; s|\.lean$||')
# Everything else.
lake build
