"""RIGOROUS certificate for the sharp ceiling on the small-lam window 0 < lam <= LAM1 (target LAM1 = 0.1 to meet certify_pow.py).
Claim: for every planted branch b, l(b) := log T_b(lam) - |b| F*(lam) <= 0, where F* = max_j r_j (>= r_3, which is all we use:
every bound below is nonincreasing in F*).
Typed induction on |b| (all quantities scaled by 1/lam, so a lam-box may contain 0):
  exact types  LEAF (l = -F*, y = 1), P2 (root deg 2, leaf child), S_e (root deg e >= 3, all e-1 children P2 = arm A_{e-1}, l <= 0;
               the by-definition clip min(., 0) is ACTIVE ONLY at e = 4 = A3: every other spider's own bound is < 0, small_spider_strict.py);
  GEN_e        every other branch with root degree e:  l/lam <= g_e (e <= DT), <= gT (e > DT);  always y_b = 1/(e + lam R) <= 1/e.
Step: root degree d, children c_i (smaller branches, typed by induction): l = sum l_c + log(1 + lam S/d) - F*, S = sum y_c.
 The configurations {LEAF} (d = 2) and {P2}^(d-1) (d >= 3) are the exact types; every other configuration must satisfy bound <= g_d.
Enclosures (valid for all u >= 0): u - u^2/2 + u^3/3 - u^4/4 <= log(1+u) <= u - u^2/2 + u^3/3.
Parents d <= 5: enumeration over the Pareto front of child types (a dominated child can be replaced; P2 never used as dominator;
 d = 2 enumerates every type since LEAF may dominate and {LEAF} is excluded; for d >= 3 no replacement can create the excluded all-P2 config).
Parents 6 <= d <= DT: tangent of the concave f(S) = log(1+lam S/d)/lam at S0 (separable).  Parents d > DT: analytic tail
 (log(1+u) <= u; S_4 children contribute <= 1/(4d); every other child type has l/lam <= -eta, so for d >= 3/(4 eta) the sum is
 <= (d-1)/(4d) < 1/4 and bound <= 1/4 - F*/lam <= gT is checked; this pins the run to lam <= 0.1028).  g from the first-order (lam -> 0) DP plus slack DELTA."""
import sys, math, itertools, time
from mpmath import iv, mpf
iv.dps = 30
KAP = mpf(15)/56
DELTA = mpf(sys.argv[3]) if len(sys.argv) > 3 else mpf('0.006')   # certified value
GT = mpf('-0.009')
def UP(x): return mpf(iv.mpf(x).b)      # upper endpoint as a plain (exact) mpf
def LO(x): return mpf(iv.mpf(x).a)
def Lg_up(X, L):  X = iv.mpf(X); return X - L*X*X/2 + L*L*X*X*X/3          # >= log(1 + L X)/L
def Lg_lo(X, L):  X = iv.mpf(X); return X - L*X*X/2 + L*L*X*X*X/3 - L**3*X**4/4
def first_order_g(DT):
    """g_e for 2 <= e <= DT from the lam -> 0 DP (separable at first order), + DELTA."""
    P2 = (-mpf(1)/28, mpf(1)/2)
    base = [('L', -KAP, mpf(1)), ('P2',) + P2] + [(('S', e), (e-1)*P2[0] + mpf(e-1)/(2*e) - KAP, mpf(1)/e) for e in range(3, DT+1)]
    g = {e: -KAP for e in range(2, DT+1)}
    for it in range(5000):
        T = base + [(e, g[e], mpf(1)/e) for e in range(2, DT+1)] + [('GT', GT, mpf(1)/(DT+1))]
        new = {}
        for d in range(2, DT+1):
            h = sorted(((t[1] + t[2]/d), str(t[0])) for t in T if not (d == 2 and t[0] == 'L'))
            top, nm = h[-1]
            s = (d-1)*top if (nm != 'P2' or d == 2) else (d-2)*top + h[-2][0]
            new[d] = s - KAP + DELTA
        if max(abs(new[e] - g[e]) for e in g) < mpf(10)**-25: return new
        g = new
    raise RuntimeError('DP did not converge')
def types(L, g, DT):
    FL = (3*Lg_lo(mpf(1)/2, L) + Lg_lo(3/(4*(2 + L)), L))/7          # <= r_3/lam <= F*/lam
    luP2 = Lg_up(mpf(1)/2, L) - 2*FL; yP2 = 1/(2 + L)
    T = [('L', UP(-FL), mpf(1)), ('P2', UP(luP2), UP(yP2))]
    for e in range(3, DT+1):
        R = (e-1)*yP2
        lu = UP((e-1)*luP2 + Lg_up(R/e, L) - FL)
        T.append((('S', e), min(lu, mpf(0)), UP(1/(e + L*R))))      # spiders are arms: l <= 0 by definition of F*
    for e in range(2, DT+1): T.append((e, g[e], mpf(1)/e))
    # tail spiders e > DT: l/lam <= (e-1) luP2 + 1/2 - F*/lam, decreasing in e because luP2 < 0
    assert UP(luP2) < 0
    T.append(('ST', UP(DT*luP2 + iv.mpf(1)/2 - FL), mpf(1)/(DT+1)))
    T.append(('GT', GT, mpf(1)/(DT+1)))
    return T, FL
def pareto(T):
    keep = []
    for i, t in enumerate(T):
        dom = any(j != i and u[0] != 'P2' and u[1] >= t[1] and u[2] >= t[2] and (u[1] > t[1] or u[2] > t[2] or j < i)
                  for j, u in enumerate(T))
        if not dom or t[0] == 'P2': keep.append(t)
    return keep
def excluded(d, names):
    return (d == 2 and names == ['L']) or (d >= 3 and all(n == 'P2' for n in names))
def check_box(a, b, g, DT):
    L = iv.mpf([a, b]); T, FL = types(L, g, DT); worst = (mpf(-9), None)
    PT = pareto(T)
    for d in range(2, 6):
        # d = 2: one child, enumerate ALL types (LEAF could dominate a type, and {LEAF} is the excluded config)
        TT = T if d == 2 else PT
        for ms in itertools.combinations_with_replacement(range(len(TT)), d-1):
            names = [TT[i][0] for i in ms]
            if excluded(d, names): continue
            S = sum(TT[i][2] for i in ms)
            v = UP(iv.mpf(sum(TT[i][1] for i in ms)) + Lg_up(S/d, L) - FL) - g[d]
            if v > worst[0]: worst = (v, (d, names))
    for d in range(6, DT+1):
        # tangent point: iterate the separable argmax at the box midpoint
        lm = (a + b)/2; S0 = mpf(d-1)/4
        for _ in range(30):
            be = (mpf(1)/d)/(1 + lm*S0/d)
            i = max(range(len(T)), key=lambda i: T[i][1] + be*T[i][2]); S0n = (d-1)*T[i][2]
            if S0n == S0: break
            S0 = S0n
        beta = (iv.mpf(1)/d)/(1 + L*S0/d)
        h = sorted(((t[1] + UP(beta)*t[2]), str(t[0])) for t in T)
        top, nm = h[-1]
        s = (d-1)*top if nm != 'P2' else (d-2)*top + h[-2][0]
        v = UP(iv.mpf(s) + Lg_up(S0/d, L) - LO(beta)*iv.mpf(S0) - FL) - g[d]
        if v > worst[0]: worst = (v, (d, 'tangent', nm))
    # tail d > DT
    eta = -max(t[1] for t in T if t[0] != ('S', 4))
    assert eta > 0, "eta"
    assert DT + 1 >= 3/(4*eta), ("tail needs DT + 1 >= 3/(4 eta)", float(3/(4*eta)))   # tail parents have d >= DT + 1
    tail = UP(iv.mpf(1)/4 - FL) - GT
    if tail > worst[0]: worst = (tail, 'tail')
    return worst
if __name__ == "__main__":
    LAM1 = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf('0.1'); W = mpf(sys.argv[2]) if len(sys.argv) > 2 else mpf('0.005')
    DT = 240
    t0 = time.time(); g = first_order_g(DT)
    assert max(g.values()) < 0 and GT < 0, "all GEN bounds must be negative"
    assert all(g[e] <= GT for e in range(DT//2, DT+1)), "large-degree g_e should sit below gT"
    print(f"DELTA={DELTA}  gT={GT}  max g = {float(max(g.values())):+.5f} at e={max(g, key=g.get)}; g_2..g_8 =",
          [round(float(g[e]), 5) for e in range(2, 9)])
    LAM0 = mpf(sys.argv[4]) if len(sys.argv) > 4 else mpf(0)
    x = LAM0; nb = 0; bad = []
    def rec(p, r, dep):
        global nb
        w = check_box(p, r, g, DT); nb += 1
        if w[0] < 0: return None
        if dep >= 4: return (float(p), float(r), float(w[0]), w[1])
        m = (p + r)/2
        return rec(p, m, dep+1) or rec(m, r, dep+1)
    while x < LAM1:
        y = min(x + W, LAM1)
        f = rec(x, y, 0)
        if f: bad.append(f); break
        x = y
    print(f"lam in [{LAM0}, {LAM1}] (0 means the open end):  {'CERTIFIED' if not bad else 'NOT certified ' + str(bad)}; {nb} boxes; {time.time()-t0:.0f}s")
