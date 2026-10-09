"""Tail of the non-atom gap (case 2 <= c <= 9): the values m_c + w_c(y(A_31)).

Written in October 2026. Both certifying programs include the tail in their per-c minimum without printing it:
../../bg_rate/certify.py (section B; candidate `A>30`, that is m_c + w_c(y(A_31))) and the second
implementation ../gapcheck.py (candidate `A>60`). This program runs the definitions of each, unchanged (the
source of certify.py up to the line `J = 30`, and the source of gapcheck.py up to its first check), in separate
namespaces, and prints for each c the value m_c + w_c(y(A_31)) in interval arithmetic, with
m_c = Phi_c(c/3) and y(A_j) = 3/(4j+3). Since w_c decreases on [0, 1/3] and y(A_j) <= y(A_31) for j >= 31,
these values bound m_c + w_c(y(A_j)) + sigma(A_j) from below for every j >= 31.

Usage (from this folder): python3 tail_values.py
"""
import os, sys
os.environ.setdefault("OMP_NUM_THREADS", "1")
here = os.path.dirname(os.path.abspath(__file__))


def load(folder, filename, marker):
    d = os.path.normpath(os.path.join(here, folder))
    sys.path.insert(0, d)
    cwd = os.getcwd()
    os.chdir(d)
    ns = {"__name__": "defs"}
    exec(open(filename).read().split(marker)[0], ns)
    os.chdir(cwd)
    sys.path.remove(d)
    return ns


A = load("../../bg_rate", "certify.py", "\nJ = 30\n")
for mod in ("core", "ivtools"):  # gapcheck has its own modules; do not reuse certify's
    sys.modules.pop(mod, None)
B = load("..", "gapcheck.py", "# also check w_c directly")

ok = True
lows = []
print("c   certify.py definitions        gapcheck.py definitions")
for c in range(2, 10):
    va = A["PhiI"](c, A["Fr"](c, 3)) + A["w_c"](c, A["atom_x"](31))
    vb = B["Phi"](c, B["I"](c) / 3) + B["wc"](c, B["xa"](31))
    la, ha, lb_, hb = float(va.a), float(va.b), float(vb.a), float(vb.b)
    lows.append((min(la, lb_), c))
    ok &= abs(la - lb_) < 1e-9
    print(f"{c}   [{la:.6f}, {ha:.6f}]          [{lb_:.6f}, {hb:.6f}]")
m, c = min(lows)
print(f"minimum over 2 <= c <= 9: >= {m:.6f} at c = {c}")
print("the two programs agree to 1e-9:", ok)
assert ok and m >= 0.028
print("all tail values >= 0.028: OK")
