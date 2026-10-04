"""Rigorous interval tools (mpmath.iv, outward rounding) for the potential h and the
rate potential H_eta = h - eta*w.  Constants enclosed from rational log bounds (core.log_encl)."""
import os; os.environ.setdefault("OMP_NUM_THREADS", "1")
from fractions import Fraction as Fr
from mpmath import iv, mpf
from core import LAM_LO, LAM_HI, BETA_LO, BETA_HI, KAP_LO, KAP_HI, GAM_LO, GAM_HI, log_encl

iv.prec = 120

def hull(A, B):
    return iv.mpf([min(A.a, B.a), max(A.b, B.b)])

def F(fr):
    """exact-ish interval for a Fraction"""
    fr = Fr(fr)
    return iv.mpf(fr.numerator) / fr.denominator

def ivfr(lo, hi):
    return hull(F(lo), F(hi))

LAM = ivfr(LAM_LO, LAM_HI); BETA = ivfr(BETA_LO, BETA_HI)
KAP = ivfr(KAP_LO, KAP_HI); GAM = ivfr(GAM_LO, GAM_HI)
QI = F(Fr(3, 23)); THIRD = F(Fr(1, 3))
AW = Fr(621, 14)          # slope of w on [0,1/3]: w(x) = 11 - AW (x - q)
AWI = F(AW)

def sq(D):
    if D.a >= 0 or D.b <= 0:
        return D * D
    return iv.mpf([0, max(-D.a, D.b) ** 2])

def pieces(X):
    """split X into its parts in [0,1/3] and [1/3,1]"""
    a, b = X.a, X.b
    out = []
    if a <= THIRD.b:
        out.append(('Q', iv.mpf([a, min(b, THIRD.b)])))
    if b >= THIRD.a:
        out.append(('L', iv.mpf([max(a, THIRD.a), b])))
    return out

def h_iv(X):
    res = None
    for kind, Y in pieces(X):
        v = KAP * sq(Y - QI) if kind == 'Q' else BETA + GAM * (Y - THIRD)
        res = v if res is None else hull(res, v)
    return res

def w_iv(X):
    res = None
    for kind, Y in pieces(X):
        v = 11 - AWI * (Y - QI) if kind == 'Q' else 2 - F(Fr(3, 2)) * (Y - THIRD)
        res = v if res is None else hull(res, v)
    return res

def H_iv(X, eta):
    """H = h - eta w, evaluated piecewise (so that the dependency on the piece is kept)"""
    E = F(eta)
    res = None
    for kind, Y in pieces(X):
        if kind == 'Q':
            v = KAP * sq(Y - QI) - E * (11 - AWI * (Y - QI))
        else:
            v = BETA + GAM * (Y - THIRD) - E * (2 - F(Fr(3, 2)) * (Y - THIRD))
        res = v if res is None else hull(res, v)
    return res

def Hp_iv(Y, eta, kind):
    """derivative of H on a piece: kind 'Q' (x<=1/3) or 'L' (x>=1/3)"""
    E = F(eta)
    if kind == 'Q':
        return 2 * KAP * (Y - QI) + E * AWI
    return GAM + E * F(Fr(3, 2))

def PhiH_iv(c, SI, eta):
    """Phi^H_c(S) = lam - eta + c H(S/c) - log(1+S/(c+1)) - H(1/(c+1+S))"""
    r = 1 / (c + 1 + SI)
    return LAM - F(eta) + c * H_iv(SI / c, eta) - iv.log(1 + SI / (c + 1)) - H_iv(r, eta)

def dPhiH_iv(c, SI, eta, side):
    """Phi^H_c'(S) on SI lying on one side of the kink S=c/3 (side 'Q' = S<=c/3, 'L' = S>=c/3);
    the r-part uses the piece of r: for c>=2, r<=1/3 (piece Q); for c=1, r in [1/3,1/2] (piece L)."""
    r = 1 / (c + 1 + SI)
    hy = Hp_iv(SI / c, eta, side)
    hr = Hp_iv(r, eta, 'Q' if c >= 2 else 'L')
    return hy - r + hr * r ** 2

def bb_min_ge0(f, lo, hi, eqpts=(), deriv=None, depth=0, maxdepth=70, tol=mpf('1e-4')):
    """prove f(S) >= 0 on [lo,hi] (f: interval -> interval). eqpts: points where f=0 exactly
    (proved separately); near them use deriv(Iv, side) with side in ('left','right') of the point:
    need derivative <= 0 on the left piece and >= 0 on the right piece."""
    X = iv.mpf([lo, hi])
    if f(X).a >= 0:
        return True
    if depth > maxdepth:
        return False
    for e in eqpts:
        if lo <= e <= hi and hi - lo < tol:
            okL = (lo >= e) or deriv(iv.mpf([lo, e]), 'left').b <= 0
            okR = (hi <= e) or deriv(iv.mpf([e, hi]), 'right').a >= 0
            if okL and okR:
                return True
    mid = (lo + hi) / 2
    for e in eqpts:
        if lo < e < hi and hi - lo < 16 * tol:
            mid = e
    return (bb_min_ge0(f, lo, mid, eqpts, deriv, depth + 1, maxdepth, tol) and
            bb_min_ge0(f, mid, hi, eqpts, deriv, depth + 1, maxdepth, tol))

def bb_lower(f, lo, hi, nmax=4000, target=None):
    """rigorous lower bound of min f on [lo,hi] by best-first subdivision"""
    import heapq
    X = iv.mpf([lo, hi]); v = f(X)
    heap = [(v.a, lo, hi)]
    best_up = f(iv.mpf([lo, lo])).b
    it = 0
    while heap and it < nmax:
        vlo, a, b = heapq.heappop(heap)
        if target is not None and vlo >= target:
            heapq.heappush(heap, (vlo, a, b)); break
        m = (a + b) / 2
        best_up = min(best_up, f(iv.mpf([m, m])).b)
        if best_up - vlo < mpf('1e-9'):
            heapq.heappush(heap, (vlo, a, b)); break
        for (u, t) in ((a, m), (m, b)):
            heapq.heappush(heap, (f(iv.mpf([u, t])).a, u, t))
        it += 1
    return min(h[0] for h in heap), best_up

def bb_upper(f, lo, hi, nmax=4000):
    lo_, up_ = bb_lower(lambda X: -f(X), lo, hi, nmax)
    return -lo_, -up_
