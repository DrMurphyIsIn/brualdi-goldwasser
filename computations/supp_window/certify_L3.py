"""Interval confirmation of the window checks (lem:lam-window-cv; rem:lam-window-cv): sharp ceiling on lam in [3.22, lam_c], lam_c = 1+sqrt5, uniformly as delta = lam_c - lam -> 0.
Witness (theta = 1): U = min(0, -s1 (y - ydag), -eps - kap (y - y_ch)), ydag = (e^{F*}-1)/lam, s1 = eps/(y_ch - ydag),
kap = 0.5 F*/(1/2 - y_ch), eps = 2(F* - L), L = log(1+lam/2)/2, F* = sup_j r_j.
Enclosures (proved by hand, lem:lam-window-enc; all in terms of g = log((2+2lam)/(2+lam)) - L >= 0, a = lam/(2+lam), b = a/(1+a)):
  eps_lo = g^2 (1+a)/(4a + 3(1+a) g) <= eps <= eps_hi = g^2/(2b);  F* in [L + eps_lo/2, L + eps_hi/2];
  D := y_ch - ydag in [D_lo, D_up], D_up = y_ch - (sqrt(1+lam/2)-1)/lam, D_lo = D_up - e^{L}(e^{eps_hi/2}-1)/lam.
g and D_up vanish at lam_c, so we write g = delta*q, D_up = delta*p with q = -g'(xi), p = -D_up'(xi) (mean value on [lam, lam_c]).
Checks per lambda-box:
 C1 (k >= 1, by hand): 3L - log(1 + 2lam/3) >= eps_hi  and  2log(1+lam/2) - log(1+lam) >= eps_hi.
 C2 (k = 0, 1 <= m <= 7): Psi = -m kap (yb - y_ch)^+ + log(1 + lam m yb/(m+1)) - L + eps/2 + kap (y_v - y_ch)^+ < 0 for yb in [0,1/2].
 C3 (m >= 8 structure): ydag_lo >= 1/9; y_8 <= ydag_lo; lam y_8 <= kap_lo; D_lo > 0; s1_hi = eps_hi/D_lo <= kap_lo.
 C4 (8 <= m <= M_t', window, by hand): D_up (9/8 + lam^2 D_up^2/(eps_lo (1 + lam ydag_lo)) + 2 lam D_up) <= y_ch (1 + lam y_ch).
 (m > M_t' = lam D_up/(eps_lo(1+lam ydag_lo)) + 1 >= true M_t: tangent lemma at ydag, no check needed.)"""
import sys, time
from mpmath import iv, mpf
iv.dps = 30
LC = 1 + iv.sqrt(5)
def Lf(x):  return iv.log(1 + x/2)/2
def gf(x):  return iv.log((2 + 2*x)/(2 + x)) - Lf(x)
def gp(x):  return 1/(1 + x) - iv.mpf('1.5')/(2 + x)                    # g'(x)
def Dupf(x): return 1/(2 + x) - (iv.sqrt(1 + x/2) - 1)/x
def Dupp(x):                                                             # D_up'(x)
    s = iv.sqrt(1 + x/2)
    return -1/(2 + x)**2 - ((x/(4*s)) - (s - 1))/x**2
def check_box(d0, d1):
    """delta in [d0, d1] (d0 >= 0)."""
    Dl = iv.mpf([d0, d1]); lam = LC - Dl; H = LC - iv.mpf([0, d1])           # hull [lam, lam_c] for mean values
    L = Lf(lam); a = lam/(2 + lam); b = a/(1 + a); ych = 1/(2 + lam)
    q = -gp(H); p = -Dupp(H)
    assert q.a > 0 and p.a > 0, "q, p positive"
    g = Dl*q; Dup = Dl*p
    eps_hi = Dl**2*q**2/(2*b)
    eps_lo = Dl**2*q**2*(1 + a)/(4*a + 3*(1 + a)*Dl*q)
    Fs = L + iv.mpf([eps_lo.a, eps_hi.b])/2
    kap = iv.mpf('0.5')*Fs/(iv.mpf('0.5') - ych)
    ydag_lo = (iv.exp(L) - 1)/lam
    # D_lo = D_up - e^L (e^{eps_hi/2}-1)/lam >= delta*(p - delta * e^L q^2/(4b) e^{eps_hi/2}/lam)
    corr = iv.exp(L)*(q**2/(4*b))*iv.exp(eps_hi/2)/lam
    Dlo_over_delta = p - Dl*corr
    ok = {}
    ok['C1'] = (3*L - iv.log(1 + 2*lam/3) - eps_hi).a >= 0 and (2*iv.log(1 + lam/2) - iv.log(1 + lam) - eps_hi).a >= 0
    y8 = 1/(9 + lam*8*ych)
    s1_hi = Dl*q**2/(2*b*Dlo_over_delta)                                  # eps_hi / D_lo, delta cancelled
    ok['C3'] = (ydag_lo.a >= iv.mpf(1)/9 and y8.b <= ydag_lo.a and (lam*y8).b < kap.a   # strict
                and Dlo_over_delta.a > 0 and s1_hi.b <= kap.a)
    # C4: D_up^2/eps_lo = p^2 (4a + 3(1+a) delta q)/(q^2 (1+a))
    Dsq_over_eps = p**2*(4*a + 3*(1 + a)*Dl*q)/(q**2*(1 + a))
    lhs = Dup*(iv.mpf(9)/8 + lam**2*Dsq_over_eps/(1 + lam*ydag_lo) + 2*lam*Dup)
    ok['C4'] = (lhs - ych*(1 + lam*ych)).b <= 0
    # C2: bisection in yb for m = 1..7
    nb = 0; c2 = True
    for m in range(1, 8):
        stack = [(mpf(0), mpf('0.5'), 0)]
        while stack:
            lo, hi, dep = stack.pop(); Y = iv.mpf([lo, hi]); yv = 1/(m + 1 + lam*m*Y)
            z1 = Y - ych; z1p = iv.mpf([max(mpf(0), z1.a), max(mpf(0), z1.b)])
            z2 = yv - ych; z2p = iv.mpf([max(mpf(0), z2.a), max(mpf(0), z2.b)])
            Psi = -m*kap*z1p + iv.log(1 + lam*m*Y/(m + 1)) - L + iv.mpf([0, eps_hi.b])/2 + kap*z2p
            if Psi.b < 0: nb += 1; continue
            if dep > 30: c2 = False; stack = []; break
            h = (lo + hi)/2; stack += [(lo, h, dep+1), (h, hi, dep+1)]
        if not c2: break
    ok['C2'] = c2
    return ok, nb
if __name__ == "__main__":
    DMAX = LC.b - mpf('3.22')       # delta up to lam_c - 3.22 (upper end of the lam_c enclosure: covers lam = 3.22)
    W = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf('0.0005')
    d = mpf(0); tot = 0; t0 = time.time(); bad = None
    while d < DMAX:
        e = min(d + W, DMAX); ok, nb = check_box(d, e); tot += nb
        if not all(ok.values()): bad = (float(d), float(e), ok); break
        d = e
    print("THEOREM C checks:", "ALL PASSED" if bad is None else f"FAILED {bad}", f"on delta in [0, {float(DMAX):.6f}] (lam in [3.22, lam_c]); C2 boxes {tot}; {time.time()-t0:.0f}s")
