"""Generate the maximizer table (n = 4..491) for the paper from the Lean data file.

Reads tabData from formalization/R3Cert/BGSpiderTableData.lean, recomputes each exact value with the
closed form F, and writes table_maximizers.tex.
"""
import re, math
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
src = (ROOT / "formalization/R3Cert/BGSpiderTableData.lean").read_text()
body = src.split("def tabData")[1].split(":=", 1)[1].split("\n\n")[0]
rows = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", body)]
assert len(rows) == 488, len(rows)

def g(j):  # planted value of arm A_j (A_0 = leaf)
    return Fr(3, 2) ** j * Fr(4 * j + 3, 3 * (j + 1))
def r(j):
    return Fr(3, 4 * j + 3)

def F(C, s, a, b):
    kids = [("P",)] * C + [("A", s)] * a + [("A", s + 1)] * b
    G, R = Fr(1), Fr(0)
    for k in kids:
        if k[0] == "P":
            G *= Fr(3, 2); R += Fr(1, 3)
        else:
            G *= g(k[1]); R += r(k[1])
    return G * (1 + R / len(kids))

def label(C, s, a, b):
    parts = []
    if C:
        parts.append(f"$C^{{{C}}}$" if C > 1 else "$C$")
    for size, cnt in ((s + 1, b), (s, a)):
        if cnt == 0:
            continue
        name = "L" if size == 0 else f"A_{{{size}}}"
        parts.append(f"${name}^{{{cnt}}}$" if cnt > 1 else f"${name}$")
    return "\\,".join(parts)

out = []
for i, (C, s, a, b) in enumerate(rows):
    n = i + 4
    assert 1 + 2 * C + a * (2 * s + 1) + b * (2 * s + 3) == n
    v = F(C, s, a, b)
    rho = (621 / 64) ** (1 / 11)
    out.append((n, label(C, s, a, b), float(v) / rho ** (n - 1)))

ncol = 3
per = math.ceil(len(out) / ncol)
lines = []
for i in range(per):
    cells = []
    for c in range(ncol):
        j = c * per + i
        if j < len(out):
            n, lab, ratio = out[j]
            cells.append(f"{n} & {lab} & {ratio:.4f}")
        else:
            cells.append("& &")
    lines.append(" & ".join(cells) + r" \\")
Path(__file__).with_name("table_maximizers.tex").write_text("\n".join(lines) + "\n")
print("rows", len(out), "per column", per)
