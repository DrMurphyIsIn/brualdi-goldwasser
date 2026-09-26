"""Telperion packaging for the Brualdi-Goldwasser certificate families.

Each family's generator (the untrusted certifying step: it re-checks every inequality in exact
arithmetic before writing Lean) regenerates its Lean files into a scratch directory.  This helper
wraps that output as a Telperion `EmitResult` and uses Telperion's provenance layer:

  * `--freeze`: `telperion.provenance.freeze` into `<family>/frozen/` (+ manifest.json with the input
    hash of the generator sources);
  * `--check` (default): `telperion.provenance.diff_frozen` against `frozen/`, AND a sync check that
    every emitted file is byte-identical to the copy under `formalization/R3Cert/` that Lean builds.

The Lean kernel is the only trusted component: a wrong certificate is a failed `lake build`.
"""
from __future__ import annotations
import argparse, hashlib, os, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "telperion" / "src"))
from telperion.provenance import EmitResult, freeze, diff_frozen  # noqa: E402

R3 = ROOT / "formalization" / "R3Cert"


def flat(rel: str) -> str:
    return rel.replace("/", "__")


def unflat(name: str) -> str:
    return name.replace("__", "/")


def input_hash(paths: list[Path]) -> str:
    h = hashlib.sha256()
    for p in sorted(paths):
        h.update(p.name.encode())
        h.update(p.read_bytes())
    return h.hexdigest()


def collect(out: Path, family: str, sources: list[Path]) -> EmitResult:
    files = {}
    for p in sorted(out.rglob("*.lean")):
        files[flat(str(p.relative_to(out)))] = p.read_text()
    n_thm = sum(t.count("\ntheorem ") + t.startswith("theorem ") for t in files.values())
    return EmitResult(family, input_hash(sources), files, n_thm, len(files))


def run(family: str, here: Path, sources: list[Path], generate) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--freeze", action="store_true")
    args = ap.parse_args()
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "R3Cert"
        out.mkdir()
        generate(out, Path(td))
        res = collect(out, family, sources)
        if args.freeze:
            frozen = here / "frozen"
            if frozen.exists():
                shutil.rmtree(frozen)
            freeze(res, frozen)
            print(f"[{family}] froze {len(res.files)} files, {res.n_theorems} theorems")
            return 0
        rep = diff_frozen(res, here / "frozen")
        bad = list(rep.details)
        for name, text in res.files.items():
            tgt = R3 / unflat(name)
            if not tgt.exists() or tgt.read_text() != text:
                bad.append(f"formalization drift: {tgt.relative_to(ROOT)}")
        if bad:
            print(f"[{family}] FAIL"); [print("  " + b) for b in bad[:20]]
            return 1
        print(f"[{family}] OK: {len(res.files)} files match frozen/ and formalization/, "
              f"{res.n_theorems} theorems")
        return 0


def py(*args, cwd: Path, env: dict | None = None) -> None:
    e = dict(os.environ); e.update(env or {})
    subprocess.run([sys.executable, *args], cwd=cwd, env=e, check=True)
