"""Brute-force check of the lemmaS_certify.py induction hypothesis on EVERY planted branch with n <= 14 (53,272 branches), with exact
float cavity values (l', y, z, Q, Q') at several s.  Classifies each branch (exact: <= N0 vertices or spider; GEN class (e, k) for
e <= D1 with k = floor(sum ylo_c / YH)) and checks: Lemma Z (0 <= s Q' <= Q, 0 <= z <= y); y >= 1/(e + s(e-1));
GEN: l' <= g, z <= zeta (g from g_iter at that s); exact: l' <= 0, with equality only at A3."""
import sys, math
sys.argv = ['x']
exec(open('lemmaS_certify.py').read().split('\nif __name__')[0])
exec(open('exp1_ceiling.py').read().split('def ev(')[0].replace("NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15", "NMAX = 1"))
def r3pf(s): return (1.5/(1+s/2) + (1.5/(2+s)**2)/(1 + 3*s/(4*(2+s))))/7
def is_spider(t): return len(t) >= 2 and all(c == ((),) for c in t)
def is_exact(t, n): return n <= N0 or is_spider(t)
for s in [0.001, 0.05, 0.1, 0.15, 0.19, 0.198]:
    rp = r3pf(s); Gc, Gs = g_iter(s, -0.012); memo = {}
    def ev(t):
        if t in memo: return memo[t]
        d = len(t) + 1; ch = [ev(c) for c in t]
        Q = s*sum(c[1] for c in ch); Qp = sum(c[2] for c in ch); n = 1 + sum(c[5] for c in ch)
        r = (sum(c[0] for c in ch) + Qp/(d+Q) - rp, 1/(d+Q), (d + Q - s*Qp)/(d+Q)**2, Q, Qp, n)
        memo[t] = r; return r
    worst_gen = -9; worst_ex = -9; cnt = 0; badZ = 0
    for n in range(1, 15):
        for t in trees(n):
            lp, y, z, Q, Qp, nn = ev(t); d = len(t) + 1; cnt += 1
            if not (-1e-15 <= s*Qp <= Q + 1e-15 and -1e-15 <= z <= y + 1e-15): badZ += 1
            assert y >= 1/(d + s*(d-1)) - 1e-15
            if is_exact(t, n):
                if t != A3: worst_ex = max(worst_ex, lp)
                else: assert abs(lp) < 1e-12
                continue
            if d <= D1:
                ysum = sum((ev(c)[1] if is_exact(c, ev(c)[5]) else 1/(len(c)+1 + s*len(c))) for c in t)
                k = int(ysum/YH + 1e-12)
                worst_gen = max(worst_gen, lp - Gc[d][k]); assert z <= 1/(d + s*k*YH) + 1e-15
            else:
                worst_gen = max(worst_gen, lp - Gs[d]); assert z <= 1/d + 1e-15
    print(f"s={s}: {cnt} branches; Lemma Z violations {badZ}; max over GEN of (l' - g) = {worst_gen:+.5f} (< 0 needed); "
          f"max exact non-A3 l' = {worst_ex:+.3e}", flush=True)
