"""Candidate certificates for CandProp 492 (Lean: BGSpiderCandCells0..8, BGSpiderCand): within the bounded
candidate set, the rule spider W n beats every configuration for every n >= 492 -- 223 exact polynomial
certificates (221 all-nonnegative-coefficient shifts, 2 Bernstein on the bounded exception ranges).
bg_spider_cand_certs.py re-checks every certificate exactly and brute-forces CandProp for n = 492..3000.
Usage: python3 generate.py [--freeze]
"""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import bgfreeze as B

SOURCES = [HERE / "bg_spider_cand_certs.py"]


def generate(out: Path, tmp: Path) -> None:
    B.py(str(HERE / "bg_spider_cand_certs.py"), "--emit", cwd=HERE, env={"BG_FORMAL_ROOT": str(out.parent)})


if __name__ == "__main__":
    sys.exit(B.run("cand_certs", HERE, SOURCES, generate))
