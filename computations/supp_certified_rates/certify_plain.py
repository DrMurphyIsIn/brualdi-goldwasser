"""Rigorous certificate for the growth rate of pi_lam at a rational lam, by a convex piecewise-linear message
potential in the PLAIN form, verified with exact rationals, formal logarithms and interval arithmetic.

Statement verified (the plain-witness lemma of the paper; used for the certified rates):
  h : [0,1] -> [0,inf) convex, piecewise linear with rational nodes, h = 0 on [0, y0], h(1) = F, and
  Phi_m(ybar) = F + m h(ybar) - log(1 + lam m ybar/(m+1)) - h(1/(m+1+lam m ybar)) >= 0
  for all integers m >= 1 and all ybar in [0,1].
  m <= M: cells + tangent lines (Lemma 'cells'); m > M: tail lemma (h = 0 on [0,y0], 1/(M+2) <= y0,
  (M+1) h_i >= lam (y_i - ydag)/rho at nodes y_i > ydag).
Consequence: T_b <= rho^{|b|} for every planted branch, and rho^{(2j+1) floor((n-1)/(2j+1))} <= max pi_lam
<= (1+lam) rho^{n-1}, rho = e^F.
Usage: python3 certify_plain.py p q [nnodes]"""
import os, sys, json, time
os.environ["OMP_NUM_THREADS"] = "1"
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv
from formal import FL, ivq
import potential_lp


def arm_formal(j, lam):
    c = 1 + lam / 2
    yc = 1 / (2 + lam)
    logT = j * FL.log(c) + FL.log(1 + lam * j * yc / (j + 1))
    return logT, 1 / (j + 1 + lam * j * yc)


def regime(lam):
    """Return (kind, j*, F formal, y* rational). Rigorous: compares enclosures, with the analytic facts
    (unimodality in j; cherry regime iff lam^2 - 2 lam - 4 >= 0) from the paper."""
    c = 1 + lam / 2
    if lam * lam - 2 * lam - 4 >= 0:
        return "cherry", None, FL.log(c) / 2, 1 / (2 + lam)
    # unimodal: find the first j with f_{j+1} < f_j (rigorously separated)
    j = 1
    while True:
        a = arm_formal(j, lam)[0] / (2 * j + 1)
        b = arm_formal(j + 1, lam)[0] / (2 * j + 3)
        d = (b - a).iv()
        if d.b < 0:
            break
        assert d.a > 0, "tie within enclosure: lam too close to a breakpoint"
        j += 1
    logT, ys = arm_formal(j, lam)
    return "arm", j, logT / (2 * j + 1), ys


def build_h(lam, kind, js, F, ys, nnodes=70, extra_nodes=()):
    lamf = float(lam)
    r = potential_lp.solve(lamf, nnodes=nnodes)
    assert r["status"] == 0 and r["t"] > 0, ("LP failed", r["status"], r["t"])
    nodes_f, hv = list(r["nodes"]), list(r["h"])
    yc = 1 / (2 + lam)
    pinned = lambda y: min(abs(y - float(ys)), abs(y - float(yc)), abs(y - 1.0)) < 1e-12
    changed = True
    while changed:
        changed = False
        for k in range(1, len(nodes_f) - 1):
            if pinned(nodes_f[k]):
                continue
            sl = (hv[k] - hv[k - 1]) / (nodes_f[k] - nodes_f[k - 1])
            sr = (hv[k + 1] - hv[k]) / (nodes_f[k + 1] - nodes_f[k])
            if sr - sl < 1e-7:
                del nodes_f[k]; del hv[k]; changed = True
                break
    beta = 2 * F - FL.log(1 + lam / 2)
    D = 10 ** 9
    nodes, vals = [], []
    for y, v in zip(nodes_f, hv):
        if abs(y - float(ys)) < 1e-12:
            yq, vq = ys, FL(0)
        elif abs(y - float(yc)) < 1e-12:
            yq, vq = yc, beta
        elif abs(y - 1.0) < 1e-12:
            yq, vq = Fr(1), F
        else:
            yq = Fr(round(y * D), D)
            vq = FL(Fr(max(0.0, v)).limit_denominator(10 ** 12))
        nodes.append(yq); vals.append(vq)
    # dedupe (keep pinned values)
    seen = {}
    for y, v in zip(nodes, vals):
        if y not in seen or not v.a:
            seen[y] = v if (y not in seen) else seen[y]
    nodes = sorted(seen); vals = [seen[y] for y in nodes]
    return nodes, vals, r


class PWL:
    def __init__(self, nodes, vals):
        self.x = nodes; self.v = vals  # h = 0 left of x[0] (x[0] = y* with value 0)

    def piece(self, y):
        """index k with x[k] <= y <= x[k+1]; -1 for the zero piece left of x[0]."""
        if y <= self.x[0]:
            return -1
        lo, hi = 0, len(self.x) - 1
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if self.x[mid] <= y:
                lo = mid
            else:
                hi = mid
        return lo

    def __call__(self, y):
        if y <= self.x[0]:
            return FL(0)
        if y >= self.x[-1]:
            return self.v[-1]
        k = self.piece(y)
        a, b = self.x[k], self.x[k + 1]
        s = (y - a) / (b - a)
        return self.v[k] * (1 - s) + self.v[k + 1] * s

    def slopes(self):
        return [(self.v[k + 1] - self.v[k]) / (self.x[k + 1] - self.x[k]) for k in range(len(self.x) - 1)]


def certify(lam, nnodes=70, verbose=True, maxdepth=30):
    t0 = time.time()
    kind, js, F, ys = regime(lam)
    yc = 1 / (2 + lam)
    nodes, vals, lp = build_h(lam, kind, js, F, ys, nnodes)
    h = PWL(nodes, vals)
    Fi = F.iv()
    rho = iv.exp(Fi)
    ydag = (rho - 1) / ivq(lam)
    info = dict(lam=str(lam), regime=kind, jstar=js, F=[str(Fi.a), str(Fi.b)], nnodes=len(nodes))
    # --- structural checks: h >= 0, convex (nondecreasing slopes, first slope >= 0), h(1) = F
    sl = h.slopes()
    assert all(v.lo() >= 0 or v.is_zero() for v in vals), "h negative at a node"
    prev = FL(0)
    for s in sl:
        d = (s - prev)
        assert d.is_zero() or d.lo() >= 0, "convexity fails"
        prev = s
    k = nodes.index(yc)
    left = sl[k - 1] if k > 0 else FL(0)   # h = 0 left of nodes[0] (cherry regime: y_c = y* = nodes[0])
    corner = (sl[k] - left).lo()
    info["corner_at_yc"] = str(corner)
    # --- tail
    y0 = nodes[0]
    for y, v in zip(nodes, vals):
        if v.is_zero() or (not v.a and v.c == 0):
            y0 = y
        else:
            break
    M = 1
    while Fr(1, M + 2) > y0:
        M += 1
    def node_ok(M):
        for y, v in zip(nodes, vals):
            yi = ivq(y)
            if (yi - ydag).a > 0:
                need = ivq(lam) * (yi - ydag) / rho
                if not ((M + 1) * v.iv() - need).a >= 0:
                    return False
            elif not (yi - ydag).b < 0 and not v.is_zero():
                # node inside the enclosure of ydag: require the stronger bound with ydag.lo
                need = ivq(lam) * (yi - ydag.a) / rho
                if not ((M + 1) * v.iv() - need).a >= 0:
                    return False
        return True
    while not node_ok(M):
        M += 1
    info["y0"] = str(y0); info["M"] = M
    # --- cells
    eqpts = {(1, Fr(1))}
    if kind == "arm":
        eqpts.add((js, yc))
    ncert = 0; worst = None; nzero = 0
    L = lam
    for m in range(1, M + 1):
        cuts = {Fr(0), Fr(1)}
        for y in nodes:
            if 0 < y < 1:
                cuts.add(y)
            pre = (1 / y - m - 1) / (L * m)
            if 0 < pre < 1:
                cuts.add(pre)
        cuts = sorted(cuts)
        stack = [(a, b, 0) for a, b in zip(cuts, cuts[1:])]
        while stack:
            p, q, dep = stack.pop()
            # tangent point
            if (m, p) in eqpts:
                t = p
            elif (m, q) in eqpts:
                t = q
            else:
                t = (p + q) / 2
            ok = True
            vals_end = []
            # convexity requirement: slope of h on y_b(cell) >= 0 (h nondecreasing) -- guaranteed globally
            for e in (p, q):
                arg_t = 1 + L * m * t / (m + 1)
                Lt = FL.log(arg_t) + (L * m / (m + 1)) * (e - t) / arg_t
                yb = 1 / (m + 1 + L * m * e)
                val = -F - m * h(e) + Lt + h(yb)
                if (m, e) in eqpts and t == e:
                    if not val.is_zero():
                        ok = False
                    else:
                        nzero += 1
                    vals_end.append(0.0)
                    continue
                hi = val.hi()
                vals_end.append(float(hi))
                if not hi < 0:
                    ok = False
            if ok:
                ncert += 1
                w = max(vals_end)
                if (worst is None or w > worst[0]) and w < 0:
                    worst = (w, m, float(p), float(q))
            else:
                assert dep < maxdepth, ("certificate failed", m, float(p), float(q), vals_end)
                mid = (p + q) / 2
                stack.append((p, mid, dep + 1)); stack.append((mid, q, dep + 1))
    info["certificates"] = ncert
    info["exact_zero_endpoints"] = nzero
    info["worst_nonzero_endpoint"] = worst
    info["seconds"] = round(time.time() - t0, 1)
    info["nodes"] = [[str(y), repr(v)] for y, v in zip(nodes, vals)]
    if verbose:
        print({k: v for k, v in info.items() if k != "nodes"})
    return info


if __name__ == "__main__":
    p, q = int(sys.argv[1]), int(sys.argv[2])
    nn = int(sys.argv[3]) if len(sys.argv) > 3 else 70
    lam = Fr(p, q)
    info = certify(lam, nn)
    os.makedirs("out", exist_ok=True)
    with open("out/cert_plain_%d_%d.json" % (p, q), "w") as f:
        json.dump(info, f, indent=1)
    print("CERTIFIED: growth rate of pi_lam at lam=%s is exp(F), F in [%s, %s]" % (lam, info["F"][0][:14],
          info["F"][1][:14]))
