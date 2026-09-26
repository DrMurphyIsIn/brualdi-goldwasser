"""Mid-range certificates 150 <= n <= 491 (Lean: BGSpiderMidCellsD2..23, BGSpiderMidRootK2..23,
BGSpiderMidSpiders): credited rate cells per degree cap, per-root-degree kernel knapsack checks, and
exact spider lower bounds.  gen_mid_lean.py recomputes every rational and re-checks every inequality.
Usage: python3 generate.py [--freeze]
"""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import bgfreeze as B

SOURCES = [HERE / "gen_mid_lean.py", HERE / "bg_spider_reduction.py"]


def generate(out: Path, tmp: Path) -> None:
    B.py(str(HERE / "gen_mid_lean.py"), str(out), cwd=HERE)


if __name__ == "__main__":
    sys.exit(B.run("mid_cells", HERE, SOURCES, generate))
