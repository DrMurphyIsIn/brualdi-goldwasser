"""Rigorous certificate for the growth rate of pi_lam at rational lam by a convex message potential in the
LEAF-EXEMPT form (leaves treated exactly, other children pooled by Jensen).

Verified statement (the leaf-exempt-witness lemma of the paper; used for the certified rates): h : [0,1/2] -> [0,inf) convex piecewise
linear with rational nodes, h = 0 on [0, y0], and for all integers k, m >= 0 with (k,m) != (0,0) and all
ybar in [0,1/2] (ybar absent when m = 0), with d = k+m+1:
   Phi_{k,m}(ybar) = (k+1)F + m h(ybar) - log(1 + lam (k + m ybar)/d) - h(1/(d + lam (k + m ybar))) >= 0.
Cells cover d <= N+1; the tail lemma covers d >= N+2 provided
   1/(N+2) <= y0,  (N+1) F >= lam (1 - ydag)/rho,  (N+1) F >= log(1+lam),
   (N+1) h_i >= lam (y_i - ydag)/rho at nodes y_i > ydag.
Consequence: every non-leaf planted branch has g(b) >= h(y_b) >= 0, so T_b <= rho^{|b|}.
Usage: python3 certify_leafx.py p q"""
import os, sys, json, time
os.environ["OMP_NUM_THREADS"] = "1"
from fractions import Fraction as Fr
import numpy as np
from mpmath import iv
from formal import FL, ivq
from certify_plain import regime, PWL
import potential_leafx_lp


def build_h(lam, F, ys, Kc=12, Mc=40):
    if ys > 0:
        Mc = max(Mc, int(1.5 / float(ys)) + 5)
        Kc = max(Kc, min(Mc, 40))
    r = potential_leafx_lp.solve(float(lam), Kc=Kc, Mc=Mc)
    assert r["status"] == 0 and r["t"] > 0, ("LP failed", r["status"], r["t"])
    nodes_f, hv = list(r["nodes"]), list(r["h"])
    yc = 1 / (2 + lam)
    pin = lambda y: min(abs(y - float(ys)), abs(y - float(yc)), abs(y - 0.5)) < 1e-12
    changed = True
    while changed:
        changed = False
        for k in range(1, len(nodes_f) - 1):
            if pin(nodes_f[k]):
                continue
            sl = (hv[k] - hv[k - 1]) / (nodes_f[k] - nodes_f[k - 1])
            sr = (hv[k + 1] - hv[k]) / (nodes_f[k + 1] - nodes_f[k])
            if sr - sl < 1e-7:
                del nodes_f[k]; del hv[k]; changed = True
                break
    beta = 2 * F - FL.log(1 + lam / 2)
    D = 10 ** 9
    out = {}
    for y, v in zip(nodes_f, hv):
        if abs(y - float(ys)) < 1e-12:
            out[ys] = FL(0)
        elif abs(y - float(yc)) < 1e-12:
            out[yc] = beta
        elif y < float(ys):
            continue
        elif abs(y - 0.5) < 1e-12:
            out[Fr(1, 2)] = FL(Fr(max(0.0, v)).limit_denominator(10 ** 12))
        else:
            out.setdefault(Fr(round(y * D), D), FL(Fr(max(0.0, v)).limit_denominator(10 ** 12)))
    nodes = sorted(out)
    return nodes, [out[y] for y in nodes], r


def certify(lam, verbose=True, maxdepth=30):
    t0 = time.time()
    kind, js, F, ys = regime(lam)
    yc = 1 / (2 + lam)
    nodes, vals, lp = build_h(lam, F, ys)
    assert nodes[0] == ys and nodes[-1] == Fr(1, 2)
    h = PWL(nodes, vals)
    Fi = F.iv(); rho = iv.exp(Fi); ydag = (rho - 1) / ivq(lam); L = lam
    info = dict(form="leaf-exempt", lam=str(lam), regime=kind, jstar=js, F=[str(Fi.a), str(Fi.b)], nnodes=len(nodes))
    sl = h.slopes()
    assert all(v.is_zero() or v.lo() >= 0 for v in vals), "h negative"
    prev = FL(0)
    for s in sl:
        d = s - prev
        assert d.is_zero() or d.lo() >= 0, "convexity fails"
        prev = s
    # tail parameters
    y0 = nodes[0]
    for y, v in zip(nodes, vals):
        if v.is_zero():
            y0 = y
        else:
            break
    lamI = ivq(lam)
    def tail_ok(N):
        if Fr(1, N + 2) > y0:
            return False
        if not ((N + 1) * Fi - lamI * (1 - ydag) / rho).a > 0:
            return False
        if not ((N + 1) * Fi - iv.log(1 + lamI)).a > 0:
            return False
        for y, v in zip(nodes, vals):
            yi = ivq(y)
            if (yi - ydag).b > 0:
                need = lamI * (yi - ydag.a) / rho
                if not ((N + 1) * v.iv() - need).a >= 0:
                    return False
        return True
    N = 1
    while not tail_ok(N):
        N += 1
    info["y0"] = str(y0); info["N"] = N
    eqpts = set()
    if kind == "arm":
        eqpts.add((0, js, yc))
    ncert = nzero = 0; worst = None
    # m = 0 : single evaluations, k = 1..N
    for k in range(1, N + 1):
        d = k + 1
        val = -(k + 1) * F + FL.log(1 + L * k / d) + h(1 / (d + L * k))
        if k == 1:
            assert val.is_zero(), "cherry equality not exact"
            nzero += 1
        else:
            assert val.hi() < 0, ("m=0 check failed", k)
            ncert += 1
    for k in range(0, N + 1):
        for m in range(1, N + 1 - k):
            d = k + m + 1
            cuts = {Fr(0), Fr(1, 2)}
            for y in nodes:
                if 0 < y < Fr(1, 2):
                    cuts.add(y)
                pre = (1 / y - d - L * k) / (L * m)
                if 0 < pre < Fr(1, 2):
                    cuts.add(pre)
            cuts = sorted(cuts)
            stack = [(a, b, 0) for a, b in zip(cuts, cuts[1:])]
            while stack:
                p, q, dep = stack.pop()
                if (k, m, p) in eqpts:
                    t = p
                elif (k, m, q) in eqpts:
                    t = q
                else:
                    t = (p + q) / 2
                ok = True; ve = []
                for e in (p, q):
                    arg = 1 + L * (k + m * t) / d
                    Lt = FL.log(arg) + (L * m / d) * (e - t) / arg
                    yb = 1 / (d + L * (k + m * e))
                    val = -(k + 1) * F - m * h(e) + Lt + h(yb)
                    if (k, m, e) in eqpts and t == e:
                        if val.is_zero():
                            nzero += 1; ve.append(0.0); continue
                        ok = False; ve.append(None); continue
                    hi = val.hi(); ve.append(float(hi))
                    if not hi < 0:
                        ok = False
                if ok:
                    ncert += 1
                    w = max(ve)
                    if w < 0 and (worst is None or w > worst[0]):
                        worst = (w, k, m, float(p), float(q))
                else:
                    assert dep < maxdepth, ("certificate failed", k, m, float(p), float(q), ve)
                    mid = (p + q) / 2
                    stack += [(p, mid, dep + 1), (mid, q, dep + 1)]
    info.update(certificates=ncert, exact_zero_endpoints=nzero, worst_nonzero_endpoint=worst,
                seconds=round(time.time() - t0, 1), nodes=[[str(y), repr(v)] for y, v in zip(nodes, vals)])
    if verbose:
        print({k: v for k, v in info.items() if k != "nodes"})
    return info


if __name__ == "__main__":
    p, q = int(sys.argv[1]), int(sys.argv[2])
    lam = Fr(p, q)
    info = certify(lam)
    with open("out/cert_leafx_%d_%d.json" % (p, q), "w") as f:
        json.dump(info, f, indent=1)
    print("CERTIFIED (leaf-exempt): growth rate of pi_lam at lam=%s is exp(F), F in [%s, %s]" %
          (lam, info["F"][0][:16], info["F"][1][:16]))
