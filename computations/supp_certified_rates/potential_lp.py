"""Search (floating point, untrusted) for a convex message potential h_lam certifying the growth rate of
pi_lam, by linear programming over piecewise-linear convex h.

Bellman inequality (Jensen form), for integers m >= 1 and ybar in [0, 1]:
    Phi_m(ybar) = F + m h(ybar) - log(1 + lam m ybar/(m+1)) - h(1/(m+1+lam m ybar)) >= 0,
with h convex, h = 0 on [0, y*] (y* = message of the optimal atom), h(y_c) = beta, h(1) = F.
The optimal atom is the arm A_j* (lam < 1+sqrt5) or the cherry (lam >= 1+sqrt5; then y* = y_c, beta = 0).
Tail (m > M) is handled by the lemma: h = 0 on [0, y0], 1/(M+2) <= y0 and (M+1) h_i >= lam (y_i - ydag)/rho
at nodes y_i > ydag, ydag = (rho - 1)/lam.  These node conditions are imposed in the LP.
"""
import os, sys, math
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
from scipy.optimize import linprog
ALPHA = float(os.environ.get("ALPHA", "1"))
W = lambda d: float(d) ** ALPHA   # vertex weight w(d) = d^alpha (alpha = 1: the pi_lam family)


def atoms(lam):
    c = 1 + lam / W(2)
    yc = 1 / (W(2) + lam)
    def arm(j):
        return j * math.log(c) + math.log(1 + lam * j * yc / W(j + 1)), 1 / (W(j + 1) + lam * j * yc)
    best = max(range(1, 5000), key=lambda j: arm(j)[0] / (2 * j + 1))
    Fa = arm(best)[0] / (2 * best + 1)
    Fc = math.log(c) / 2
    if Fa > Fc:
        F = Fa; ystar = arm(best)[1]; js = [best]
        # near-tie arms (breakpoints)
        for j in (best - 1, best + 1):
            if j >= 1 and abs(arm(j)[0] / (2 * j + 1) - F) < 1e-13:
                js.append(j)
    else:
        F = Fc; ystar = yc; js = []
        best = None
    beta = 2 * F - math.log(c)
    return dict(F=F, yc=yc, ystar=ystar, beta=beta, js=js, jstar=best, rho=math.exp(F),
                ydag=(math.exp(F) - 1) / lam)


def interp_row(nodes, y):
    """row r with h(y) = r . hvec (piecewise linear, h = 0 left of nodes[0])."""
    r = np.zeros(len(nodes))
    if y <= nodes[0]:
        return r
    if y >= nodes[-1]:
        r[-1] = 1.0; return r
    k = np.searchsorted(nodes, y) - 1
    a, b = nodes[k], nodes[k + 1]
    s = (y - a) / (b - a)
    r[k] = 1 - s; r[k + 1] = s
    return r


def solve(lam, nnodes=70, nsample=500, Mlp=None, verbose=False, return_all=False, free=False):
    A = atoms(lam)
    F, yc, ys, beta = A["F"], A["yc"], A["ystar"], A["beta"]
    jst = A["jstar"]
    if Mlp is None:
        Mlp = max(30, int(3 * (jst or 1)) + 10, int(1 / ys) + 2)
    # nodes: y*, grid, yc, 1 ; denser near yc and near y*
    g = list(np.linspace(ys, 1, nnodes))
    g += list(yc + (np.linspace(-1, 1, 21) ** 3) * 0.05)
    g += list(ys + np.linspace(0, 1, 11) ** 2 * (yc - ys))
    g += [yc, 1.0, ys]
    if free:
        g += list(np.linspace(0, ys, 15))
    lo = 0.0 if free else ys
    nodes = np.array(sorted(set(float("%.12g" % x) for x in g if lo <= x <= 1)))
    K = len(nodes)
    iy = int(np.argmin(abs(nodes - yc))); nodes[iy] = yc
    i0 = int(np.argmin(abs(nodes - ys))); nodes[i0] = ys
    nv = K + 1  # h values + t
    Aub, bub = [], []
    eq_pts = [(1, 1.0)] + [(j, yc) for j in A["js"]]
    if not A["js"]:
        pass
    samples = set(np.linspace(0, 1, nsample))
    samples |= set(nodes)
    samples |= set(yc + np.linspace(-0.02, 0.02, 41))
    for m in range(1, Mlp + 1):
        pts = set(samples)
        for y in nodes:
            pre = (1 / y - W(m + 1)) / (lam * m) if y > 0 else -1
            if 0 <= pre <= 1:
                pts.add(pre)
        for yb in sorted(pts):
            if yb < 0 or yb > 1:
                continue
            ybb = 1 / (W(m + 1) + lam * m * yb)
            const = F - math.log(1 + lam * m * yb / W(m + 1))
            row = m * interp_row(nodes, yb) - interp_row(nodes, ybb)
            om = 1.0
            for (me, ye) in eq_pts:
                if m == me:
                    om = min(om, abs(yb - ye) * 5)
            # Phi = const + row.h >= t*om  <=>  -row.h + om t <= const
            Aub.append(np.concatenate([-row, [om]])); bub.append(const)
    # convexity: slopes nondecreasing, first slope >= 0 (h=0 left of y*)
    for k in range(K - 1):
        r = np.zeros(nv)
        if k == 0:
            if not free:  # slope_0 >= 0: h1 - h0 >= 0
                r[1] = -1; r[0] = 1
                Aub.append(r); bub.append(0.0)
            continue
        dl = nodes[k] - nodes[k - 1]; dr = nodes[k + 1] - nodes[k]
        # (h[k]-h[k-1])/dl <= (h[k+1]-h[k])/dr
        r = np.zeros(nv)
        r[k] = 1 / dl + 1 / dr; r[k - 1] = -1 / dl; r[k + 1] = -1 / dr
        Aub.append(r); bub.append(0.0)
    # tail node conditions
    for k in range(K if not free else 0):
        if nodes[k] > A["ydag"]:
            r = np.zeros(nv); r[k] = -(Mlp + 1)
            Aub.append(r); bub.append(-lam * (nodes[k] - A["ydag"]) / A["rho"])
    # one-sided derivative conditions at the forced equality points (margin t)
    if not free:
        def srow(k, side):
            r = np.zeros(nv)
            if side > 0:
                if k + 1 < K:
                    d = nodes[k + 1] - nodes[k]; r[k + 1] += 1 / d; r[k] -= 1 / d
            else:
                if k >= 1:
                    d = nodes[k] - nodes[k - 1]; r[k] += 1 / d; r[k - 1] -= 1 / d
            return r
        # m = 1 at ybar = 1:  s_-(1) - (lam/2)/(1+lam/2) + lam yc^2 s_+(yc) <= -t
        r = srow(K - 1, -1) + lam * yc * yc * srow(iy, +1); r[-1] = 1.0
        Aub.append(r); bub.append((lam / W(2)) / (1 + lam / W(2)))
        for j in A["js"]:
            Lm = (lam * j / W(j + 1)) / (1 + lam * j * yc / W(j + 1))
            # right derivative >= t :  -j s_+(yc) + t <= -Lm
            r = -j * srow(iy, +1); r[-1] = 1.0
            Aub.append(r); bub.append(-Lm)
            # left derivative <= -t : j s_-(yc) + lam j y*^2 s_+(y*) + t <= Lm
            r = j * srow(iy, -1) + lam * j * ys * ys * srow(i0, +1); r[-1] = 1.0
            Aub.append(r); bub.append(Lm)
    Aeq, beq = [], []
    for k, val in ((i0, 0.0), (iy, beta), (K - 1, F)):
        r = np.zeros(nv); r[k] = 1; Aeq.append(r); beq.append(val)
    c = np.zeros(nv); c[-1] = -1
    bounds = ([(-10, None)] if free else [(0, None)]) * K + [(None, 1.0)]
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq), b_eq=np.array(beq),
                  bounds=bounds, method="highs")
    out = dict(lam=lam, status=res.status, t=(-res.fun if res.status == 0 else None), A=A, Mlp=Mlp)
    if res.status == 0:
        out["nodes"] = nodes; out["h"] = res.x[:K]
    return out


if __name__ == "__main__":
    lams = [float(x) for x in sys.argv[1:]] or [0.01, 0.05, 0.1, 0.25, 0.4, 0.4305, 0.431, 0.5, 0.75, 0.8725, 1.0,
                                                 1.1924, 1.5, 2.0, 2.5, 3.0, 3.2, 3.236, 3.24, 3.5, 4, 6, 10, 30]
    free = os.environ.get("FREE") == "1"
    for lam in lams:
        r = solve(lam, free=free)
        A = r["A"]
        t = r["t"]
        print("lam=%-8g best=%-6s F=%.8f  Mlp=%d  LP status=%d  margin t=%s  t/F=%s" %
              (lam, ("A%d" % A["jstar"]) if A["jstar"] else "cherry", A["F"], r["Mlp"], r["status"],
               "%.3e" % t if t is not None else None, "%.3e" % (t / A["F"]) if t is not None else None))
        sys.stdout.flush()
