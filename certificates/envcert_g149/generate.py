"""The envelope certificate G149 (Lean: R3Cert/BGEnvCert/G149/*): every non-spider maximum-degree rooting
with root degree <= 23 on 7 <= n <= 149 vertices is strictly beaten by the certified spider.

  envcert_emit.py 149 <caps> (ENVCERT_KMAX=23) -- tables, witnesses, tangent/log data, 11 cap fragments;
                                                   every inequality re-checked in exact arithmetic;
  gen_g149_extra.py                              -- sliced shared checks + MainK.
Usage: python3 generate.py [--freeze]
"""
import os, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import bgfreeze as B

SOURCES = [HERE / f for f in ("envcert.py", "envcert_emit.py", "gen_g149_extra.py", "bg_spider_reduction.py")]
CAPS = "1,2,3,4,5,6,7,8,12,16,22"


def generate(out: Path, tmp: Path) -> None:
    root = out.parent
    B.py(str(HERE / "envcert_emit.py"), "149", CAPS, str(root), cwd=HERE, env={"ENVCERT_KMAX": "23"})
    g = out / "BGEnvCert" / "G149"
    for f in ("FragShared.lean", "Main.lean"):
        (g / f).unlink(missing_ok=True)
    B.py(str(HERE / "gen_g149_extra.py"), str(g), cwd=HERE)


if __name__ == "__main__":
    sys.exit(B.run("envcert_g149", HERE, SOURCES, generate))
