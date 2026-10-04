"""RIGOROUS monotonicity certificate (rem:lam-smallmono, "Lemma S") on [S0, S1] (target (0, 0.198]):
   for every planted branch b and s in the box,  l'(b) := d/ds [log T_b(s) - |b| r_3(s)] <= 0,  equality only for A3.
Notation: root degree d (= #children + 1), Q_b = s sum_c y_c, y_b = 1/(d + Q_b), z_b = d/ds (s y_b) = (d + Q_b - s Q_b')/(d + Q_b)^2,
 Q_b' = sum_c z_c.  Cavity: l'(b) = sum_c l'(c) + Q_b'/(d + Q_b) - r_3'.
LEMMA Z (induction): 0 <= s Q_b' <= Q_b, hence 0 <= z_b <= y_b.  [leaf: Q = 0.  Step: s z_c = s(d_c+Q_c-sQ_c')/(d_c+Q_c)^2 lies in
 [s d_c/(d_c+Q_c)^2, s/(d_c+Q_c)] = [>=0, s y_c], and summing gives 0 <= s Q_b' <= Q_b.]
TYPES.  EXACT: every branch with <= N0 = 7 vertices, and every spider S_e (all children P2; S_e = arm A_{e-1}).  l'(A3) = 0 identically.
 GEN: every other branch.  For root degree e <= D1 = 12, a GEN branch has class k = floor(sum_c ylo_c / YH) (ylo_c = exact y_c for an
 exact child, 1/(e_c + s(e_c - 1)) for a GEN child; this is a lower bound on y_c because R_c <= e_c - 1).
 HYPOTHESIS: GEN_(e,k): l' <= g[e][k], z <= y <= 1/(e + s k YH).  GEN_e (D1 < e <= DT): l' <= gs[e], z <= 1/e.  GEN_e (e > DT): l' <= gT,
 z <= 1/(DT+1).  Always y >= 1/(e + s(e-1)).
STEP for a GEN parent (degree d, class k): l' <= sum_c [l'_c + z_c/(d + s k YH)] - r_3' (z_c >= 0, Q >= s sum ylo >= s k YH), and
 sum ylo_c lies in [kYH, (k+1)YH), so for any mu: sum h_c <= sum (h_c + mu ylo_c) - mu*(kYH if mu >= 0 else (k+1)YH).  The max over
 configurations is a DP over (#children, size capped at N0, has-non-P2) enforcing "GEN": (size >= N0 or a big child) and not all-P2.
 D1 < d <= DT: denominator d, mu = 0.  d > DT: TAIL. With N = {A3, S5}, every child c outside N has l'_c <= -eta, and every child in N has
 l'_c <= 0 (checked).  If DT + 1 >= (1 - zN)/eta, then every child contributes <= zN/d, so the bound is <= zN - r_3' <= gT.
CONCLUSION: all g, gs, gT < 0 and every exact type other than A3 has l' < 0 on the box, so l'(b) <= 0, with equality iff b = A3.
NUMERICS: type quantities are mpmath-iv enclosures over the s-box.  The DP runs in IEEE doubles on inputs rounded outward with
 math.nextafter; every DP value is a sum of <= 300 terms of size < 2, so the rounding error is < 1e-12.  All comparisons use a cushion EPS = 1e-9.
g, gs come from a float value iteration at the box midpoint with the same item set (+ DELTA); gT = -0.012; only the verification below is part of the proof."""
import sys, math, time
from mpmath import iv, mpf
iv.dps = 30
exec(open('exp1_ceiling.py').read().split('def ev(')[0].replace("NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15", "NMAX = 1"))
N0, D1, DT, YH, DELTA, EPS = 7, 12, 300, 0.1, 0.003, 1e-9
MUS = [m*sg for m in [0, 0.01, 0.03, 0.06, 0.1, 0.2, 0.4] for sg in (1, -1)]
A3 = (((),), ((),), ((),))
def UPf(x):
    v = mpf(iv.mpf(x).b)
    return 0.0 if v == 0 else math.nextafter(float(v), math.inf)
def LOf(x):
    v = mpf(iv.mpf(x).a)
    return 0.0 if v == 0 else math.nextafter(float(v), -math.inf)
U = lambda v: math.nextafter(v, math.inf)
def r3p_iv(S): return (iv.mpf('1.5')/(1 + S/2) + (iv.mpf('1.5')/(2 + S)**2)/(1 + 3*S/(4*(2 + S))))/7
class D:
    """forward-mode AD over intervals: value and d/ds, both mpmath-iv."""
    def __init__(s_, v, d=0): s_.v = iv.mpf(v); s_.d = iv.mpf(d)
    def __add__(a, b): b = b if isinstance(b, D) else D(b); return D(a.v + b.v, a.d + b.d)
    __radd__ = __add__
    def __sub__(a, b): b = b if isinstance(b, D) else D(b); return D(a.v - b.v, a.d - b.d)
    def __rsub__(a, b): return D(b) - a
    def __mul__(a, b): b = b if isinstance(b, D) else D(b); return D(a.v*b.v, a.d*b.v + a.v*b.d)
    __rmul__ = __mul__
    def __truediv__(a, b): b = b if isinstance(b, D) else D(b); return D(a.v/b.v, (a.d*b.v - a.v*b.d)/(b.v*b.v))
    def __rtruediv__(a, b): return D(b)/a
    def __neg__(a): return D(-a.v, -a.d)
def exact_raw(Sv):
    """quantities for every exact type as D-numbers in s (s = D(Sv, 1))."""
    S = D(Sv, 1)
    rp = (D('1.5')/(1 + S/2) + (D('1.5')/((2 + S)*(2 + S)))/(1 + 3*S/(4*(2 + S))))/7
    memo = {}
    def ev(t):
        if t in memo: return memo[t]
        dg = len(t) + 1; ch = [ev(c) for c in t]
        Ysum = D(0); Zsum = D(0); Lsum = D(0)
        for c in ch: Ysum = Ysum + c[1]; Zsum = Zsum + c[2]; Lsum = Lsum + c[0]
        Q = S*Ysum; den = dg + Q
        r = (Lsum + Zsum/den - rp, 1/den, (den - S*Zsum)/(den*den)); memo[t] = r; return r
    out = []
    for n in range(1, N0+1):
        for t in trees(n):
            lp, y, z = ev(t)
            if t == A3: lp = D(0)
            out.append(dict(lp=lp, y=y, z=z, n=n, p2=(t == ((),)), big=False, name=t))
    P2 = ev(((),)); lP2, yP2, zP2 = P2
    for e in range(3, DT+1):
        if 2*e - 1 <= N0: continue
        Q = (e-1)*S*yP2; Qp = (e-1)*zP2; den = e + Q
        out.append(dict(lp=(e-1)*lP2 + Qp/den - rp, y=1/den, z=(den - S*Qp)/(den*den), n=2*e-1, p2=False, big=True, name=('S', e)))
    return out, rp, lP2
def exact_types(S):
    """interval enclosures over the box S: naive form intersected with the mean-value form f(m) + f'(S)(S - m)."""
    a, b = mpf(S.a), mpf(S.b); m = (a + b)/2
    box, rpb, lP2b = exact_raw(S); pt, rpm, lP2m = exact_raw(iv.mpf([m, m]))
    def mv(fb, fm):
        w = fm.v + fb.d*(S - m); lo = max(mpf(w.a), mpf(fb.v.a)); hi = min(mpf(w.b), mpf(fb.v.b))
        return iv.mpf([lo, hi])
    out = []
    for tb, tm in zip(box, pt):
        out.append(dict(lp=(iv.mpf(0) if tb['name'] == A3 else mv(tb['lp'], tm['lp'])), y=mv(tb['y'], tm['y']), z=mv(tb['z'], tm['z']),
                        n=tb['n'], p2=tb['p2'], big=tb['big'], name=tb['name']))
    rp = mv(rpb, rpm); lP2 = mv(lP2b, lP2m)
    # spiders e > DT: l' <= (e-1) lP2 + 1/2 - r3'  (Q'/(e+Q) <= Q'/e <= 2/(2+s)^2 <= 1/2), decreasing in e since lP2 < 0
    assert UPf(lP2) < 0
    out.append(dict(lp=DT*lP2 + iv.mpf('0.5') - rp, y=iv.mpf([0, 1.0/(DT+1)]), z=iv.mpf([0, 1.0/(DT+1)]), n=N0, p2=False, big=True, name='ST'))
    return out, rp
def ylo_gen(e, S): return 1/(e + S*(e - 1))
def dp_max(items, k):
    best = {}
    for sc, n, p2, big in items:
        key = (N0 if big else min(n, N0), p2)
        if sc > best.get(key, -1e300): best[key] = sc
    its = list(best.items()); B = {(0, False): 0.0}
    for j in range(k):
        C = {}
        for (sg, np2), v in B.items():
            for (n, p2), sc in its:
                st = (min(N0, sg + n), np2 or (not p2)); w = v + sc
                if w > C.get(st, -1e300): C[st] = w
        B = C
    return max((v for (sg, np2), v in B.items() if sg >= N0 and np2), default=-1e300)
def prep(E, S):
    """float endpoints, computed once per box: (lp_up, z_up, y_up, y_lo, n, p2, big)."""
    return [(UPf(t['lp']), UPf(t['z']), UPf(t['y']), LOf(t['y']), t['n'], t['p2'], t['big']) for t in E]
def items_for(P, a, den_lo, mu, Gc, Gs, gT, ylo_up, ylo_lo):
    """upper bounds (floats, rounded up; den_lo > 0, z >= 0) of h_c + mu*ylo_c for every child type."""
    it = []
    for lp, zu, yu, yl, n, p2, big in P:
        it.append((U(U(lp + U(zu/den_lo)) + U(mu*(yu if mu >= 0 else yl))), n, p2, big))
    for e, cl in Gc.items():
        yv = ylo_up[e] if mu >= 0 else ylo_lo[e]
        zeta = [U(1.0/LOf(iv.mpf(e) + iv.mpf(a)*k*YH)) for k in range(len(cl))] if False else ZETA[e]
        it.append((U(max(U(g + U(zt/den_lo)) for g, zt in zip(cl, zeta)) + U(mu*yv)), N0, False, True))
    for e, g in Gs.items():
        yv = ylo_up[e] if mu >= 0 else ylo_lo[e]
        it.append((U(U(g + U(U(1.0/e)/den_lo)) + U(mu*yv)), N0, False, True))
    it.append((U(U(gT + U(U(1.0/(DT+1))/den_lo)) + (U(mu/(DT+1)) if mu > 0 else 0.0)), N0, False, True))
    return it
ZETA = {}
def g_iter(sm, gT, iters=80):
    """Float value iteration at the point s = sm with EXACTLY the item set used in the verification (+ DELTA).
    Not part of the proof: it only proposes g; check_box verifies it on the whole box."""
    S = iv.mpf([sm, sm]); E, rp = exact_types(S); rp_lo = LOf(rp); P = prep(E, S)
    ylo_up = {e: UPf(ylo_gen(e, S)) for e in range(2, DT+1)}; ylo_lo = {e: LOf(ylo_gen(e, S)) for e in range(2, DT+1)}
    Gc, Gs = {}, {}
    for it in range(iters):
        ZETA.clear()
        for e, cl in Gc.items(): ZETA[e] = [1.0/(e + sm*k*YH) for k in range(len(cl))]
        nGc = {}
        for d in range(2, D1+1):
            cl = []
            for k in range(int((d-1)/YH) + 1):
                Ys = k*YH; den = d + sm*Ys; vb = 1e300
                for mu in MUS:
                    vb = min(vb, dp_max(items_for(P, sm, den, mu, Gc, Gs, gT, ylo_up, ylo_lo), d-1) - mu*(Ys if mu >= 0 else Ys + YH))
                cl.append(vb - rp_lo + DELTA)
            nGc[d] = cl
        nGs = {d: dp_max(items_for(P, sm, float(d), 0.0, Gc, Gs, gT, ylo_up, ylo_lo), d-1) - rp_lo + DELTA for d in range(D1+1, DT+1)}
        if max(max(c) for c in nGc.values()) > 0.5: raise AssertionError("value iteration diverged")
        done = Gc and all(abs(x - y) < 1e-13 for d in nGc for x, y in zip(nGc[d], Gc[d])) and all(abs(nGs[d] - Gs[d]) < 1e-13 for d in nGs)
        Gc, Gs = nGc, nGs
        if done: break
    return Gc, Gs
def check_box(a, b, W=None):
    """W = (Gc, Gs) supplies an external witness (used by negative controls); default: generated at the box midpoint."""
    S = iv.mpf([a, b]); E, rp = exact_types(S)
    rp_lo = LOf(rp); P = prep(E, S)
    ylo_up = {e: UPf(ylo_gen(e, S)) for e in range(2, DT+1)}; ylo_lo = {e: LOf(ylo_gen(e, S)) for e in range(2, DT+1)}
    gT = -0.012
    Gc, Gs = g_iter((a + b)/2, gT) if W is None else W
    ZETA.clear()
    for e, cl in Gc.items(): ZETA[e] = [UPf(1/(iv.mpf(e) + iv.mpf(a)*iv.mpf(k)*iv.mpf(YH))) for k in range(len(cl))]
    worst = (-1e300, None)
    # GEN_(d,k), d <= D1
    for d in range(2, D1+1):
        for k, g in enumerate(Gc[d]):
            Ys = k*YH; den_lo = LOf(d + iv.mpf(a)*iv.mpf(k)*iv.mpf(YH)); vb = 1e300
            for mu in MUS:
                its = items_for(P, a, den_lo, mu, Gc, Gs, gT, ylo_up, ylo_lo)
                v = dp_max(its, d-1) - mu*(Ys if mu >= 0 else Ys + YH)
                vb = min(vb, v)
            m = vb - rp_lo + EPS - g
            if m > worst[0]: worst = (m, ('C', d, k))
    for d in range(D1+1, DT+1):
        its = items_for(P, a, float(d), 0.0, Gc, Gs, gT, ylo_up, ylo_lo)
        m = dp_max(its, d-1) - rp_lo + EPS - Gs[d]
        if m > worst[0]: worst = (m, ('S', d))
    # tail
    Nset = [t for t in E if t['name'] in (A3, ('S', 5))]
    zN = max(UPf(t['z']) for t in Nset)
    nmax = max(UPf(t['lp']) for t in Nset)
    assert nmax <= 0, f"N-set l' <= 0 violated: max {nmax:+.2e}"
    others = [UPf(t['lp']) for t in E if t['name'] not in (A3, ('S', 5))] + [max(c) for c in Gc.values()] + list(Gs.values()) + [gT]
    eta = -max(others)
    assert eta > 0 and DT + 1 >= (1 - zN)/eta, ("tail", eta, zN)
    m = zN - rp_lo + EPS - gT
    if m > worst[0]: worst = (m, 'tail')
    # conclusion: all bounds negative; exact types other than A3 strictly negative
    allg = [max(c) for c in Gc.values()] + list(Gs.values()) + [gT]
    assert max(allg) < 0
    ex = max(UPf(t['lp']) for t in E if t['name'] != A3)
    return worst, ex
if __name__ == "__main__":
    S0, S1, W = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    t0 = time.time(); x = S0; nb = 0; worst = (-1e300, None); exw = -1e300; fails = []
    while x < S1 - 1e-15:
        y = min(x + W, S1)
        w, ex = check_box(x, y); nb += 1
        if w[0] > worst[0]: worst = (w[0], w[1], x)
        exw = max(exw, ex)
        if w[0] >= 0 or ex >= 0: fails.append((x, y, w, ex)); print("FAIL", x, y, w, ex, flush=True)
        x = y
    print(f"s in [{S0}, {S1}]: {'CERTIFIED' if not fails else 'NOT certified'}; {nb} boxes; worst GEN margin {worst}; "
          f"max exact non-A3 l' upper {exw:+.3e}; {time.time()-t0:.0f}s", flush=True)
