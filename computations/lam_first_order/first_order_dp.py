"""First-order (lam -> 0) exact DP.  L(b) = R_-1(b) - kappa |b| (planted: root degree d = #children + 1; the phantom edge carries no weight).
L(b) = sum_c [L(c) + 1/(d d_c)] - kappa, so V(d) := sup{L(b): root degree d} satisfies, with V(1) = -kappa (leaf):
  V(d) = (d-1) * max_{e>=1} (V(e) + 1/(d e)) - kappa     (children independent; choose the best child type)
Value iteration from V = -inf (least fixed point = true sup over finite trees)."""
from fractions import Fraction as Fr
import sys
kappa = Fr(15, 56); D = int(sys.argv[1]) if len(sys.argv) > 1 else 40
NEG = None
V = {1: -kappa}
for it in range(200):
    new = {1: -kappa}
    for d in range(2, D+1):
        cands = [V[e] + Fr(1, d*e) for e in V]
        new[d] = (d-1)*max(cands) - kappa
    if new == V: break
    V = new
print("converged after", it, "iterations")
for d in range(1, 13):
    best = max(V, key=lambda e: V[e] + Fr(1, d*e)) if d > 1 else None
    print(f"d={d:2d}: V*={float(V[d]):+.6f}  ({V[d]})  best child degree = {best}")
print("sup_d V*(d) over d <=", D, "=", float(max(V.values())), "at d =", max(V, key=V.get))
