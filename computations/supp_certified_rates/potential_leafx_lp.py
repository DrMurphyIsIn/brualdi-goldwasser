"""Leaf-exempt convex potential search (floating point, untrusted).
Children of a vertex: k leaves (treated exactly, deficit F each) and m non-leaf children with mean message
ybar in [0, 1/2]. For (k, m) != (0, 0):
  Phi_{k,m}(ybar) = (k+1) F + m h(ybar) - log(1 + lam (k + m ybar)/(k+m+1)) - h(1/(k+m+1+lam(k+m ybar))) >= 0.
h convex on [0, 1/2]; every non-leaf branch then has g(b) >= h(y_b).
Usage: python3 potential_leafx_lp.py lam ..."""
import os, sys, math
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
from scipy.optimize import linprog
from potential_lp import atoms, interp_row


def solve(lam, Kc=12, Mc=40, nnodes=80, nsample=300, hmin=0.0, pinned=True):
    A = atoms(lam)
    F, yc, ys = A["F"], A["yc"], A["ystar"]
    g = list(np.linspace(0, 0.5, nnodes)) + [yc, ys, 0.5] + list(yc + np.linspace(-0.02, 0.02, 21))
    g += list(np.geomspace(ys, 0.5, 40)) + list(yc * (1 + np.linspace(-0.3, 0.3, 13)))
    nodes = np.array(sorted(set(float("%.13g" % x) for x in g if 0 <= x <= 0.5)))
    K = len(nodes); nv = K + 1
    Aub, bub = [], []
    eq = {(1, 0, None)} | {(0, j, yc) for j in A["js"]}
    ys_s = np.concatenate([np.linspace(0, 0.5, nsample), yc + np.linspace(-0.01, 0.01, 41),
                           np.geomspace(max(ys, 1e-6) / 4, 0.5, 120)])
    for k in range(0, Kc + 1):
        for m in range(0, Mc + 1):
            if k + m == 0:
                continue
            d = k + m + 1
            pts = [0.0] if m == 0 else [y for y in ys_s if 0 <= y <= 0.5]
            for yb in pts:
                R = k + m * yb
                ybb = 1 / (d + lam * R)
                const = (k + 1) * F - math.log(1 + lam * R / d)
                row = m * interp_row(nodes, yb) - interp_row(nodes, ybb)
                om = 1.0
                if m == 0 and k == 1:
                    om = 0.0
                for (ke, me, ye) in eq:
                    if ke == k and me == m and ye is not None:
                        om = min(om, 5 * abs(yb - ye))
                Aub.append(np.concatenate([-row, [om]])); bub.append(const)
    for kk in range(1, K - 1):
        dl = nodes[kk] - nodes[kk - 1]; dr = nodes[kk + 1] - nodes[kk]
        r = np.zeros(nv); r[kk] = 1 / dl + 1 / dr; r[kk - 1] = -1 / dl; r[kk + 1] = -1 / dr
        Aub.append(r); bub.append(0.0)
    Aeq, beq = [], []
    if pinned:
        beta = A["beta"]
        iy = int(np.argmin(abs(nodes - yc))); i0 = int(np.argmin(abs(nodes - ys)))
        for kk in range(K):
            if nodes[kk] <= ys + 1e-15:
                r = np.zeros(nv); r[kk] = 1; Aeq.append(r); beq.append(0.0)
        r = np.zeros(nv); r[iy] = 1; Aeq.append(r); beq.append(beta)
        def srow(k, side):
            r = np.zeros(nv)
            if side > 0 and k + 1 < K:
                d = nodes[k + 1] - nodes[k]; r[k + 1] += 1 / d; r[k] -= 1 / d
            if side < 0 and k >= 1:
                d = nodes[k] - nodes[k - 1]; r[k] += 1 / d; r[k - 1] -= 1 / d
            return r
        for j in A["js"]:
            Lm = (lam * j / (j + 1)) / (1 + lam * j * yc / (j + 1))
            r = -j * srow(iy, +1); r[-1] = 1.0; Aub.append(r); bub.append(-Lm)
            r = j * srow(iy, -1) + lam * j * ys * ys * srow(i0, +1); r[-1] = 1.0; Aub.append(r); bub.append(Lm)
        # tail node conditions with N+1 = Mc+Kc (d-1 >= N+1)
        rho = math.exp(F); ydag = (rho - 1) / lam
        for kk in range(K):
            if nodes[kk] > ydag:
                r = np.zeros(nv); r[kk] = -(min(Kc, Mc) + 1); Aub.append(r); bub.append(-lam * (nodes[kk] - ydag) / rho)
    c_ = np.zeros(nv); c_[-1] = -1
    bounds = [(hmin, None)] * K + [(None, 1.0)]
    res = linprog(c_, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq) if Aeq else None,
                  b_eq=np.array(beq) if beq else None, bounds=bounds, method="highs")
    return dict(A=A, t=(-res.fun if res.status == 0 else None), status=res.status, nodes=nodes,
                h=(res.x[:K] if res.status == 0 else None))


if __name__ == "__main__":
    for lam in [float(x) for x in sys.argv[1:]]:
        r = solve(lam)
        print("lam=%-7g best=%-7s status %d margin t=%s" % (lam, ("A%d" % r["A"]["jstar"]) if r["A"]["jstar"]
              else "cherry", r["status"], "%.3e" % r["t"] if r["t"] is not None else None))
        if r["h"] is not None and os.environ.get("SHOW"):
            for y, v in zip(r["nodes"][::6], r["h"][::6]):
                print("   h(%.4f) = %.5f" % (y, v))
        sys.stdout.flush()
