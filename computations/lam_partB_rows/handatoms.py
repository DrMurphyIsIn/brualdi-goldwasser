"""Monotone 'atoms' for hand-style interval checks in the variable t (0 <= t1 < t2 <= 1/phi).
Each atom is a monotone function of t whose value at t = 0 is its limit; on a box [t1,t2] it is enclosed by its two
endpoint values (exact monotonicity, no derivative information). Everything else is interval arithmetic on these.
Atoms:
  Lm  = -log(1-t)/t                increasing, Lm(0) = 1
  La  = log(1+a t)/(a t)            decreasing, La(0) = 1          (a = 2/3, 3/4, 4/5)
  Lx  = log(1+x)/x, x = (t/12)/(1+2t/3)   decreasing in t (x increasing, log(1+x)/x decreasing)
  kt  = kappa/t = 2/((1-t)(3+2t))   increasing
  dt  = delta/t = (1-2t)(1+t)/((1-t)(3+2t))  decreasing on [0, 1/2] (checked symbolically)
  y4  = 1/(5+4t)                     decreasing
  Xe(s) = (e^s - 1)/s               increasing in s >= 0
"""
import mpmath as mp
from mpmath import iv
iv.dps = 30
mp.mp.dps = 30

def _pt(f, t):
    # rigorous enclosure of f at the point t (f written with the iv context when given an iv point)
    T = iv.mpf(t)
    return f(T)

def _enc(f, t1, t2, increasing):
    a, b = _pt(f, t1), _pt(f, t2)      # point enclosures (iv)
    lo = a.a if increasing else b.a
    hi = b.b if increasing else a.b
    return iv.mpf([lo, hi])

def _z(t): return t.a == 0 and t.b == 0
def Lm_(t): return iv.mpf(1) if _z(t) else -iv.log(1-t)/t
def La_(a):
    return lambda t: iv.mpf(1) if _z(t) else iv.log(1+a*t)/(a*t)
def Lx_(t):
    if _z(t): return iv.mpf(1)
    x = (t/12)/(1+2*t/3); return iv.log(1+x)/x
def kt_(t): return 2/((1-t)*(3+2*t))
def dt_(t): return (1-2*t)*(1+t)/((1-t)*(3+2*t))
def y4_(t): return 1/(5+4*t)

def atoms(t1, t2):
    # outward safety: mpmath at 30 digits, widen each atom by 1e-25
    eps = iv.mpf(0)
    A = dict(
        t=iv.mpf([t1, t2]),
        Lm=_enc(Lm_, t1, t2, True) + eps,
        L23=_enc(La_(iv.mpf(2)/3), t1, t2, False) + eps,
        L34=_enc(La_(iv.mpf(3)/4), t1, t2, False) + eps,
        L45=_enc(La_(iv.mpf(4)/5), t1, t2, False) + eps,
        Lx=_enc(Lx_, t1, t2, False) + eps,
        kt=_enc(kt_, t1, t2, True) + eps,
        dt=_enc(dt_, t1, t2, False) + eps,
        y4=_enc(y4_, t1, t2, False) + eps,
    )
    return A

def Xe(s):
    # s an interval with s.a >= 0; (e^s-1)/s increasing: enclose by rigorous point values at the two ends
    def f(x):
        X = iv.mpf(x)
        return iv.mpf(1) if x == 0 else (iv.exp(X) - 1)/X
    assert s.a >= 0
    return iv.mpf([f(s.a).a, f(s.b).b])

def cover(fn, t0, t1, minw=1e-6):
    """greedy left-to-right cover; returns list of (a, b, lower bound) or raises."""
    rows = []; a = mp.mpf(t0); t1 = mp.mpf(t1); w = (t1 - a)
    while a < t1:
        w = min(w*2, t1 - a)
        while True:
            v = fn(a, a + w)
            if v.a > 0: break
            w /= 2
            if w < minw: raise RuntimeError(f"stuck at t={a}")
        rows.append((a, a+w, v.a)); a = a + w
    return rows

def G2t_(t):
    # G_2(t)/t, G_2 = 5 log(1+3t/4) - 7 log(1+2t/3) - log(1-t); power series with positive coefficients => increasing
    if _z(t): return iv.mpf(1)/12
    return (5*iv.log(1+3*t/4) - 7*iv.log(1+2*t/3) - iv.log(1-t))/t

def atoms2(t1, t2):
    A = atoms(t1, t2)
    A['G2t'] = _enc(G2t_, t1, t2, True)
    return A
