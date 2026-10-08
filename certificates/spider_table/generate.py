"""Spider-family optimum for 4 <= n <= 491 (Lean: BGSpiderTableData, BGSpiderTableChunk_*, BGSpiderTableAll).

Pipeline (every step exact):
  1. bg_spider_opt.py search 4 491   -- exhaustive exact maximization over the spider family;
  2. bg_spider_table_sweep.py 491     -- canonical balanced form of each maximizer + the exact sweep
                                         (every balanced configuration and every <=2-child one);
  3. gen_spider_table_lean.py         -- the Lean data, 46 kernel-checked chunk modules (small per-n declarations), and the assembly.
Usage: python3 generate.py [--freeze]
"""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import bgfreeze as B

SOURCES = [HERE / "bg_spider_opt.py", HERE / "bg_spider_table_sweep.py", HERE / "gen_spider_table_lean.py"]


def generate(out: Path, tmp: Path) -> None:
    B.py(str(HERE / "bg_spider_opt.py"), "search", "4", "491", str(tmp / "opt.json"), cwd=HERE)
    B.py(str(HERE / "bg_spider_table_sweep.py"), "491", str(tmp / "opt.json"), str(tmp / "canon.json"), cwd=HERE)
    B.py(str(HERE / "gen_spider_table_lean.py"), cwd=HERE, env={"BG_R3OUT": str(out), "BG_CANON": str(tmp / "canon.json")})


if __name__ == "__main__":
    sys.exit(B.run("spider_table", HERE, SOURCES, generate))
