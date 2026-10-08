"""Negative controls for the row checker of Lemma lam-polycert(a) (../lowdeg_tables.py).

The checker accepts a row (a box [t1, t2] for one condition) only if the interval lower bound of the condition
on the box is positive and at least 30% of its value at the midpoint, and builds each table greedily (P10: by
halving).  This program runs the checker's own code -- the definitions of ../lowdeg_tables.py up to the point
where it starts writing output, executed unchanged, with the conditions of ../handatoms.py, ../s6_table.py and
../w2_table.py -- on deliberately wrong inputs, each of which must be rejected:

every condition used in the proof (P1, P3, P7, P8 and the nine conditions of P10), lowered by a constant
c slightly above its value at a point t* of its range (so the lowered condition is negative at t*), for three
points t* per condition.  Each such table must be rejected ("cannot start" for the greedy tables; for P10 the
halving reaches the minimum box width 1e-6 and stops).
Positive control: the unchanged conditions are run through the same code and give the 63 rows of the paper.

Written in October 2026 as an additional check.
Usage: python3 row_checker_controls.py      (from this folder)
"""
import os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.normpath(os.path.join(HERE, ".."))
sys.path.insert(0, PARENT)
os.chdir(PARENT)
import mpmath as mp
from mpmath import iv

src = open(os.path.join(PARENT, "lowdeg_tables.py")).read()
cut = src.index("out = open('lowdeg_tables.out', 'w')")
ns = {"__name__": "lowdeg_tables_defs"}
exec(compile(src[:cut], "lowdeg_tables.py", "exec"), ns)
greedy, okrow, M = ns["greedy"], ns["okrow"], ns["M"]
W2 = ns["W2"]
TPHI = Fr(6181, 10000)


def c10_rows(f):
    """the P10 table construction of ../lowdeg_tables.py (same code, as a function)"""
    stack = [(Fr(3, 86), Fr(3, 43)), (Fr(0), Fr(3, 86))]
    rows = []
    while stack:
        x, y = stack.pop()
        v, good = okrow(f, x, y)
        if good:
            rows.append((x, y, v.a)); continue
        assert y - x > Fr(1, 10**6), (x, y)
        m = (x + y) / 2
        stack.append((m, y)); stack.append((x, m))
    return rows


TABLES = [("P1 (S2)", ns["S2"], Fr(0), TPHI, "greedy"),
          ("P3 (S4)", ns["S4"], Fr(0), TPHI, "greedy"),
          ("P7 (S6), W_1", ns["S6"], Fr(3, 43), Fr(3229, 10000), "greedy"),
          ("P8 (S6), lambda >= 2", ns["S6hi"], Fr(1, 2), TPHI, "greedy")]
TABLES += [(f"P10 {k}", f, Fr(0), Fr(3, 43), "c10") for k, f in W2.CONDS.items()]


def build(kind, f, a, b):
    return greedy(f, a, b) if kind == "greedy" else c10_rows(f)


def rejected(kind, f, a, b):
    try:
        rows = build(kind, f, a, b)
    except RuntimeError as e:
        return True, f"rejected ({e})"
    except AssertionError as e:
        return True, f"rejected (box width at the minimum 1e-6 near {[str(x) for x in e.args[0]]})"
    return False, f"ACCEPTED with {len(rows)} rows"


allok = True
# positive control
total = 0
for name, f, a, b, kind in TABLES:
    total += len(build(kind, f, a, b))
print(f"positive control: unchanged conditions give {total} rows (paper: 63)")
allok &= (total == 63)

# B. each condition lowered below its value at one point
print("Each condition minus c, with c just above its value at t* (t* = a + (b-a)/4, (a+b)/2, a + 3(b-a)/4 on its range [a, b]):")
count = 0
for name, f, a, b, kind in TABLES:
    for ts in (a + (b - a) / 4, (a + b) / 2, a + 3 * (b - a) / 4):
        c = f(M(ts), M(ts)).b + mp.mpf("1e-12")
        g = (lambda f, c: (lambda x, y: f(x, y) - c))(f, c)
        rej, msg = rejected(kind, g, a, b)
        allok &= rej; count += 1
        print(f"   {name:22s} t* = {str(ts):>12s}  c = {mp.nstr(mp.mpf(c.b), 8):>12s}  {msg}")
print(f"{count} negative controls run")
print("ALL NEGATIVE CONTROLS REJECTED" if allok else "A NEGATIVE CONTROL WAS NOT REJECTED")
