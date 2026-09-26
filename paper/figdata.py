"""Generate the data files behind the paper's plots (paper/figdata/*.dat).

All values come from the closed-form spider value F and, for n <= 491, the Lean table
formalization/R3Cert/BGSpiderTableData.lean.  Floats are for plotting only.
"""
import math, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "figdata"
OUT.mkdir(exist_ok=True)
LR = math.log(621 / 64) / 11

src = (HERE.parent / "formalization/R3Cert/BGSpiderTableData.lean").read_text()
body = src.split("def tabData")[1].split(":=", 1)[1].split("\n\n")[0]
ROWS = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", body)]


def logg(j):
    return j * math.log(1.5) + math.log((4 * j + 3) / (3 * (j + 1)))


def y(j):
    return 3 / (4 * j + 3)


def logF(c, arms):
    """c cherries at the centre, arms = {j: count}."""
    lg, R, D = c * math.log(1.5), c / 3, c
    for j, m in arms.items():
        lg += m * logg(j); R += m * y(j); D += m
    return lg + math.log(1 + R / D)


def rule(n):
    s = 6 * (n - 1) % 11
    k4 = k6 = 0
    if 1 <= s <= 4:
        if (s == 3 and n <= 722) or (s == 4 and n <= 2319):
            k4 = 11 - s
        else:
            k6 = s
    elif s >= 5:
        k4 = 11 - s
    k5 = (n - 1 - 9 * k4 - 13 * k6) // 11
    return {4: k4, 5: k5, 6: k6}


def best(n):
    if n <= 491:
        C, s, a, b = ROWS[n - 4]
        arms = {}
        if a: arms[s] = a
        if b: arms[s + 1] = arms.get(s + 1, 0) + b
        return C, arms
    return 0, {j: m for j, m in rule(n).items() if m}


# 1. per-vertex rates of the arms
with open(OUT / "rates.dat", "w") as f:
    f.write("j rate\n")
    for j in range(1, 16):
        f.write(f"{j} {logg(j) / (2 * j + 1):.8f}\n")

# 2. the normalized maximum pi / rho^(n-1)
with open(OUT / "ratio_table.dat", "w") as f1, open(OUT / "ratio_rule.dat", "w") as f2:
    f1.write("n r\n"); f2.write("n r\n")
    for n in range(4, 1501):
        c, arms = best(n)
        v = math.exp(logF(c, arms) - (n - 1) * LR)
        (f1 if n <= 491 else f2).write(f"{n} {v:.6f}\n")

# 3. the two late competitions: (11-s) fours against s sixes, in classes s = 3 and s = 4
for s, fname in ((3, "race_s3.dat"), (4, "race_s4.dat")):
    with open(OUT / fname, "w") as f:
        f.write("n d\n")
        for n in range(300, 3001):
            if 6 * (n - 1) % 11 != s:
                continue
            k4, k6 = 11 - s, s
            a5 = (n - 1 - 9 * k4) // 11
            b5 = (n - 1 - 13 * k6) // 11
            d = logF(0, {4: k4, 5: a5}) - logF(0, {5: b5, 6: k6})
            f.write(f"{n} {1e6 * math.expm1(d):.4f}\n")

print("wrote", sorted(p.name for p in OUT.iterdir()))
