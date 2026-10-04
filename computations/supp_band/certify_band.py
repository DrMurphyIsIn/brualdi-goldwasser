"""Band certificate (rem:lam-band; mid range): sharp ceiling log T_b(lam) <= |b| F*(lam) for lam in [LAM0, LAM1] (target [0.1, 2.85];
the window checks cover [2.84, lam_c]).  Degree x R-bin typed induction (same skeleton as the typed induction on (0, 0.1]).

Notation: planted branch b, root degree d = #children + 1, R_b = sum of children's messages, y_b = 1/(d + lam R_b),
l(b) = log T_b - |b| F*.  Cavity: l(b) = sum_c l(c) + log(1 + lam R_b/d) - F*.  Since every bound is nonincreasing in F*, we
use F* >= r_J(lam) for one fixed arm J per box (J = argmax at the box centre; any J is valid).
Types (exhaustive, disjoint):
  LEAF (d = 1): l = -F*, y = 1.            P2 (d = 2, child LEAF): l = log(1+lam/2) - 2F*, y = 1/(2+lam).
  S_e  (d = e >= 3, all children P2) = arm A_{e-1}: l <= 0 by definition of F* (and <= its own bound), y = 1/(e + lam(e-1)/(2+lam)).
  ST   = all S_e with e > DT: l <= 0, y <= y(S_{DT+1}).
  GEN (e, k), 2 <= e <= DT: every other branch with root degree e and R_b in bin k = [R_k, R_{k+1}] of [0, e-1] (K equal bins):
       hypothesis l <= G[e,k]; then y in [1/(e + lam R_{k+1}), 1/(e + lam R_k)].
  GT   = every other branch with root degree e > DT: hypothesis l <= GT, y <= 1/(DT+1).
Exact-type values over a lam-box [a,b] (w = b - a): l_t(lam) <= A_t(lam) - n_t r_J(lam) =: u_t(lam), and
  sup_box u_t <= max(u_t(a), u_t(b)) + (w^2/8) max(0, -inf_box u_t'')   (chord + curvature; u_t'' in closed form, interval-evaluated;
  an earlier version used max(0, sup u'') -- wrong sign, numerically inactive on all 167 boxes).
Parent checks (every GEN parent (d, bin [A,B]) and the tail), for configurations other than the exact ones ({LEAF} at d=2, {P2}^(d-1)):
  with phi(S, lam) = log(1 + lam S/d) - r_J(lam) (concave increasing in S):
  d = 2: exact over the single child t: h_t + sup_box phi(min(yhi_t, B)), whenever ylo_t <= B and yhi_t >= A.
  d >= 3: tangent at S0 plus Lagrange terms mu (B - S_lo) >= 0, nu (S_hi - A) >= 0 (both nonnegative on feasible configurations):
     l <= sum_c [h_c + (beta_hi + nu) yhi_c - mu ylo_c] + sup_box phi(S0) - beta_lo S0 + mu B - nu A,
     beta = (lam/d)/(1 + lam S0/d) in [beta(a), beta(b)];  separable: (d-1) max, or (d-2) c_P2 + 2nd best when the max is P2.
  Tail parents DT < d <= DMAX: the same with the single bin [0, d-1], bound <= GT.
  Tail parents d > DMAX: S0 = (d-1) sigma, rho = (d-1)/d in [DMAX/(DMAX+1), 1]:  (d-1) c_t = (d-1) h_t + lam rho y_t/(1 + lam sigma rho)
     <= DMAX h_t + sup_rho lam rho yhi_t/(1 + lam sigma rho) (h_t <= 0 for every type, checked), and
     sup phi(S0) - beta S0 <= sup_rho [log(1 + lam sigma rho) - lam sigma rho/(1 + lam sigma rho)] - r_J.  Bound <= GT.
Conclusion: every type has l <= 0 (G < 0, GT < 0, exact types), so the ceiling holds.  Equality: only at the best arm(s).
Arithmetic: transcendental inputs in mpmath.iv, rounded outward to float64; separable maxima in float64 (IEEE round-to-nearest);
every comparison requires slack PAD = 1e-9.  ROUNDING BUDGET: every float input is an outward-rounded enclosure; the
separable stage computes c_t = h_t + (bh+nu) yhi_t - mu ylo_t (3 flops, |terms| <= 1.6), then (d-1) c_top (+ c_2nd), then adds
P - bl s0 + mu B - nu A (|terms| <= ~50 for d <= 1200).  With unit roundoff 2^-53 ~ 1.1e-16 and at most ~10 roundings on quantities
of magnitude <= 2e3, the total error is < 1e-11 (a second count gives <= ~1e-12), i.e. < PAD/100.  Bin edges (e-1)k/K in float differ from
the rational edges by <= 1e-15; their effect (mu (B - S_lo) and phi at B) is < 1e-15, also inside PAD."""
import sys, math, time
import numpy as np
from mpmath import iv, mpf
iv.dps = 30
PAD = 1e-9
DT, K, DMAX = 60, 8, 1200
INF = float('inf')
def up(x):  return math.nextafter(float(mpf(iv.mpf(x).b)), INF)
def dn(x):  return math.nextafter(float(mpf(iv.mpf(x).a)), -INF)
# ---------- arm rates ----------
def r_arm_f(j, lam): return (j*math.log1p(lam/2) + math.log1p(j*lam/((j+1)*(2+lam))))/(2*j+1)
def best_J(lam):
    j = np.arange(1, 5001, dtype=float)
    r = (j*np.log1p(lam/2) + np.log1p(j*lam/((j+1)*(2+lam))))/(2*j+1)
    J = int(np.argmax(r)) + 1; assert J < 4990
    return J, max(float(np.max(r)), math.log1p(lam/2)/2)
def A_parts(e):
    """exact type -> (coefficient of log(1+lam/2), q or None, n_vertices): A = c log(1+lam/2) + [log(2+lam(1+q)) - log(2+lam)]."""
    if e == 'L': return 0, None, 1
    if e == 'P2': return 1, None, 2
    return e - 1, iv.mpf(e-1)/e, 2*e - 1
def rJ_iv(J, L):
    q = iv.mpf(J)/(J+1)
    return (J*iv.log(1 + L/2) + iv.log(2 + L*(1+q)) - iv.log(2 + L))/(2*J+1)
def rJ2_iv(J, L):   # r_J''
    q = iv.mpf(J)/(J+1)
    return (-J/(2+L)**2 - (1+q)**2/(2 + L*(1+q))**2 + 1/(2+L)**2)/(2*J+1)
def u_iv(t, J, L):
    c, q, n = A_parts(t)
    v = c*iv.log(1 + L/2) - n*rJ_iv(J, L)
    if q is not None: v += iv.log(2 + L*(1+q)) - iv.log(2 + L)
    return v
def u2_iv(t, J, L):
    c, q, n = A_parts(t)
    v = -c/(2+L)**2 - n*rJ2_iv(J, L)
    if q is not None: v += -(1+q)**2/(2 + L*(1+q))**2 + 1/(2+L)**2
    return v
def sup_box(fun, fun2, a, b):
    """chord + curvature upper bound of a C^2 function over [a, b]: if u'' >= -M (M >= 0) then u - chord <= M (x-a)(b-x)/2,
    so sup u <= max(u(a), u(b)) + (w^2/8) max(0, -inf u'').  (A concave function lies ABOVE its chord.)"""
    A, B, Lb = iv.mpf(a), iv.mpf(b), iv.mpf([a, b]); w = B - A
    M = fun2(Lb); Mb = -mpf(M.a) if M.a < 0 else mpf(0)      # the excess over the chord is governed by -inf u''
    return up(iv.mpf([max(mpf(fun(A).b), mpf(fun(B).b)), max(mpf(fun(A).b), mpf(fun(B).b))]) + w*w/8*Mb)
# ---------- types ----------
def build_types(a, b, J, G, GT):
    names, h, ylo, yhi = [], [], [], []
    for t in ['L', 'P2'] + list(range(3, DT+1)):
        hv = sup_box(lambda L: u_iv(t, J, L), lambda L: u2_iv(t, J, L), a, b)
        if t not in ('L', 'P2'): hv = min(hv, 0.0)                         # spiders: l <= 0 by definition of F*
        if t == 'L': lo = hi = 1.0
        elif t == 'P2': lo, hi = dn(1/(2 + iv.mpf(b))), up(1/(2 + iv.mpf(a)))
        else:
            ys = lambda L: 1/(t + L*(t-1)/(2+L))                           # decreasing in lam
            lo, hi = dn(ys(iv.mpf(b))), up(ys(iv.mpf(a)))
        names.append(t if t in ('L', 'P2') else ('S', t)); h.append(hv); ylo.append(lo); yhi.append(hi)
    names.append('ST'); h.append(0.0); ylo.append(0.0)
    yhi.append(up(1/(DT+1 + iv.mpf(a)*DT/(2 + iv.mpf(a)))))
    for e in range(2, DT+1):
        ed = [mpf(e-1)*i/K for i in range(K+1)]
        for k in range(K):
            names.append((e, k)); h.append(G[(e, k)])
            ylo.append(dn(1/(e + iv.mpf(b)*ed[k+1]))); yhi.append(up(1/(e + iv.mpf(a)*ed[k])))
    names.append('GT'); h.append(GT); ylo.append(0.0); yhi.append(up(iv.mpf(1)/(DT+1)))
    assert h[0] < 0 and h[1] < 0, "h(LEAF), h(P2) must be < 0 (strictness)"
    return names, np.array(h), np.array(ylo), np.array(yhi)
# ---------- parent bound ----------
def phi_sup(S0, d, J, a, b):
    S0 = mpf(S0)
    f = lambda L: iv.log(1 + L*S0/d) - rJ_iv(J, L)
    f2 = lambda L: -(iv.mpf(S0)/d)**2/(1 + L*iv.mpf(S0)/d)**2 - rJ2_iv(J, L)     # full phi'' (its negative part is what matters)
    return sup_box(f, f2, a, b)
MUS = [0.0, 0.05, 0.3]; NUS = [0.0, 0.05, 0.3]
def parent_bound(d, A, B, a, b, J, names, h, ylo, yhi, iL, iP2, need_S0=None):
    if d == 2:
        best = -INF
        for t in range(len(h)):
            if t == iL or not np.isfinite(h[t]) or ylo[t] > B or yhi[t] < A: continue
            v = h[t] + phi_sup(min(yhi[t], B), 2, J, a, b)
            best = max(best, v)
        return best
    lm = 0.5*(a + b); S0 = 0.5*(A + B)
    for _ in range(40):
        be = (lm/d)/(1 + lm*S0/d); c = h + be*yhi; o = np.argsort(c)[::-1]
        S1 = (d-1)*yhi[o[0]] if o[0] != iP2 else (d-2)*yhi[o[0]] + yhi[o[1]]
        S1 = min(max(S1, A), B)
        if abs(S1 - S0) < 1e-13: break
        S0 = S1
    best = INF
    for s0 in [S0, min(B, S0*1.02 + 1e-9), max(A, S0*0.98)]:
        bl = dn((iv.mpf(a)/d)/(1 + iv.mpf(a)*mpf(s0)/d)); bh = up((iv.mpf(b)/d)/(1 + iv.mpf(b)*mpf(s0)/d))
        P = phi_sup(s0, d, J, a, b)
        for mu in MUS:
            for nu in NUS:
                c = h + (bh + nu)*yhi - mu*ylo
                o = np.argsort(c)[::-1]
                s = (d-1)*c[o[0]] if o[0] != iP2 else (d-2)*c[o[0]] + c[o[1]]
                best = min(best, s + P - bl*s0 + mu*B - nu*A)
    return best
def tail_bound(a, b, J, h, yhi, sigmas=(0.05, 0.1, 0.15, 0.2, 0.3)):
    """parents d > DMAX (any R): see docstring."""
    assert np.all(h <= 0), "tail needs h_t <= 0 for every type"
    best = INF; rho0 = mpf(DMAX)/(DMAX+1); Lb = iv.mpf([a, b]); R = iv.mpf([rho0, 1])
    rJa = mpf(rJ_iv(J, iv.mpf(a)).a)   # r_J increasing in lam: r_J >= r_J(a) on the box
    for sg in sigmas:
        coef = up(Lb*R/(1 + Lb*sg*R))          # sup over (lam, rho) of lam rho/(1 + lam sigma rho)
        c = DMAX*h + coef*yhi
        const = up(iv.log(1 + Lb*sg*R) - Lb*sg*R/(1 + Lb*sg*R) - rJa)
        best = min(best, float(np.max(c)) + const)
    return best
# ---------- witness (untrusted) ----------
def witness(a, b, DELTA):
    lam = 0.5*(a + b); J, F = best_J(lam)
    G = {(e, k): -INF for e in range(2, DT+1) for k in range(K)}; GT = -INF
    for it in range(60):
        names, h, ylo, yhi = build_types(a, b, J, G, GT)
        iL, iP2 = 0, 1
        newG = {}
        for e in range(2, DT+1):
            for k in range(K):
                A, B = (e-1)*k/K, (e-1)*(k+1)/K
                newG[(e, k)] = parent_bound(e, A, B, a, b, J, names, h, ylo, yhi, iL, iP2) + DELTA
        tv = [parent_bound(d, 0, d-1, a, b, J, names, h, ylo, yhi, iL, iP2) for d in range(DT+1, DMAX+1, 1)]
        newGT = max(max(tv), tail_bound(a, b, J, np.minimum(h, 0), yhi)) + DELTA
        if max(newG.values()) > 0.5 or newGT > 0.5: raise RuntimeError("witness diverged")
        same = all(abs(newG[x] - G[x]) < 1e-12 or (newG[x] == G[x]) for x in G) and abs(newGT - GT) < 1e-12
        G, GT = newG, newGT
        if same: break
    return J, G, GT
# ---------- trusted check ----------
def check(a, b, J, G, GT):
    names, h, ylo, yhi = build_types(a, b, J, G, GT)
    assert max(G.values()) < 0 and GT < 0
    iL, iP2 = 0, 1; worst = (-INF, None)
    for e in range(2, DT+1):
        for k in range(K):
            A, B = (e-1)*k/K, (e-1)*(k+1)/K
            pb = parent_bound(e, A, B, a, b, J, names, h, ylo, yhi, iL, iP2)
            if G[(e, k)] == -INF:
                v = -INF if pb == -INF else INF          # an empty bin must have no feasible configuration
            else:
                v = pb - G[(e, k)] + PAD
            if v > worst[0]: worst = (v, (e, k))
    for d in range(DT+1, DMAX+1):
        v = parent_bound(d, 0, d-1, a, b, J, names, h, ylo, yhi, iL, iP2) - GT + PAD
        if v > worst[0]: worst = (v, ('tail', d))
    v = tail_bound(a, b, J, h, yhi) - GT + PAD
    if v > worst[0]: worst = (v, 'tail>DMAX')
    return worst
if __name__ == "__main__":
    a, b, DELTA = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    t0 = time.time(); J, G, GT = witness(a, b, DELTA)
    fin = [v for v in G.values() if v > -INF]
    print(f"witness at {0.5*(a+b):.4f}: J={J}, max G={max(fin):+.5f}, GT={GT:+.5f}, {time.time()-t0:.1f}s", flush=True)
    t1 = time.time(); w = check(a, b, J, G, GT)
    print(f"check [{a}, {b}]: worst = {w[0]:+.3e} at {w[1]} -> {'PASS' if w[0] < 0 else 'FAIL'}  ({time.time()-t1:.1f}s)")
