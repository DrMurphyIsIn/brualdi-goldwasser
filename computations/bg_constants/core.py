"""Core definitions for the potential h at lambda = 1 (Section "rate structure" of the paper).
Notation: lambda = log rho (the paper's F*), beta=2 lambda - log(3/2), q=3/23,
kappa=beta/(1/3-q)^2, gamma=(3/2)(lambda-beta), h(x)=kappa(x-q)^2 on [0,1/3], beta+gamma(x-1/3) on [1/3,1].
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
from fractions import Fraction as Fr
import math
import mpmath as mp

mp.mp.dps = 50

# ---------- rigorous rational log enclosure (atanh series with explicit remainder) ----------
def _log_series(z, N):
    u = (z - 1) / (z + 1)
    u2 = u * u
    s = Fr(0); p = u
    for j in range(N + 1):
        s += p / (2 * j + 1)
        p *= u2
    # remainder: 2 * sum_{j>N} u^{2j+1}/(2j+1) < 2 u^{2N+3} / ((2N+3)(1-u^2))
    rem = 2 * u ** (2 * N + 3) / ((2 * N + 3) * (1 - u2))
    return 2 * s, 2 * s + rem

_LOG2 = None
def log_encl(z, N=60):
    """Return (lo, hi) Fractions with lo <= log z <= hi for rational z>0.
    Range reduction z = 2^m y, y in [1,2), then the atanh series (u <= 1/3) with explicit remainder."""
    global _LOG2
    z = Fr(z)
    if z == 1:
        return Fr(0), Fr(0)
    if z < 1:
        lo, hi = log_encl(1 / z, N)
        return -hi, -lo
    if _LOG2 is None:
        _LOG2 = _log_series(Fr(2), 80)
    m = z.numerator.bit_length() - z.denominator.bit_length()
    y = z / Fr(2) ** m
    while y >= 2:
        y /= 2; m += 1
    while y < 1:
        y *= 2; m -= 1
    if y == 1:
        lo_y = hi_y = Fr(0)
    else:
        lo_y, hi_y = _log_series(y, N)
    lo = m * _LOG2[0] + lo_y; hi = m * _LOG2[1] + hi_y
    # keep denominators small: round outward
    return rnd(lo, 10**40, up=False), rnd(hi, 10**40, up=True)

def rnd(fr, den=10**30, up=True):
    """Round a Fraction outward to a fixed denominator to keep sizes small."""
    n = fr.numerator * den
    d = fr.denominator
    q_, r_ = divmod(n, d)
    if up and r_:
        q_ += 1
    return Fr(q_, den)

# lambda = (1/11) log(621/64)
_L = log_encl(Fr(621, 64))
LAM_LO, LAM_HI = rnd(_L[0] / 11, up=False), rnd(_L[1] / 11, up=True)
_l32 = log_encl(Fr(3, 2))
BETA_LO = rnd(2 * LAM_LO - _l32[1], up=False)
BETA_HI = rnd(2 * LAM_HI - _l32[0], up=True)
Q = Fr(3, 23)
KAP_LO = rnd(BETA_LO / (Fr(1, 3) - Q) ** 2, up=False)
KAP_HI = rnd(BETA_HI / (Fr(1, 3) - Q) ** 2, up=True)
GAM_LO = rnd(Fr(3, 2) * (LAM_LO - BETA_HI), up=False)
GAM_HI = rnd(Fr(3, 2) * (LAM_HI - BETA_LO), up=True)

# ---------- high-precision floats (for exploration) ----------
LAM = mp.log(mp.mpf(621) / 64) / 11
BETA = 2 * LAM - mp.log(mp.mpf(3) / 2)
q = mp.mpf(3) / 23
KAP = BETA / (mp.mpf(1) / 3 - q) ** 2
GAM = mp.mpf(3) / 2 * (LAM - BETA)
lam, beta, kap, gam, qf = (float(v) for v in (LAM, BETA, KAP, GAM, q))
s_tan = 2 * kap * (1 / 3 - qf)   # left slope of h at 1/3

def h(x):
    return kap * (x - qf) ** 2 if x <= 1 / 3 else beta + gam * (x - 1 / 3)

def hp(x):
    return mp.mpf(KAP) * (x - q) ** 2 if x <= mp.mpf(1) / 3 else BETA + GAM * (x - mp.mpf(1) / 3)

def slack(xs):
    """Vertex slack sigma_v for children messages xs (float)."""
    c = len(xs); S = sum(xs)
    return lam + sum(h(x) for x in xs) - math.log1p(S / (c + 1)) - h(1 / (c + 1 + S))

def Phi(c, S):
    """Phi_c(S) (Jensen-reduced slack)."""
    if c == 0:
        return lam - h(1.0)
    return lam + c * h(S / c) - math.log1p(S / (c + 1)) - h(1 / (c + 1 + S))

def e_exc(x):
    """excess of h over its left tangent line at 1/3: h(x) - [beta + s (x-1/3)]"""
    return kap * (x - 1 / 3) ** 2 if x <= 1 / 3 else (gam - s_tan) * (x - 1 / 3)

# ---------- rooted branches as nested tuples: a branch is a sorted tuple of child branches ----------
from functools import lru_cache

@lru_cache(maxsize=None)
def bval(b):
    """(Z, x, size) exact Fractions for planted branch b (tuple of children)."""
    c = len(b)
    Z = Fr(1); S = Fr(0); n = 1
    for ch in b:
        Zc, xc, nc = bval(ch)
        Z *= Zc; S += xc; n += nc
    d = c + 1
    return Z * (d + S) / d, 1 / (d + S), n

@lru_cache(maxsize=None)
def bslack(b):
    """total slack of branch b = sum over its vertices of sigma_v (float); equals g(b)-h(x(b))."""
    xs = [float(bval(ch)[1]) for ch in b]
    return slack(xs) + sum(bslack(ch) for ch in b)

def g_of(b):
    Z, x, n = bval(b)
    return n * lam - math.log(float(Z)) if Z < 10**300 else n * lam - float(mp.log(mp.mpf(Z.numerator) / Z.denominator))

LEAF = ()
CHERRY = (LEAF,)
def ARM(j):
    return tuple([CHERRY] * j) if j > 0 else LEAF

def is_atom(b):
    if b == LEAF or b == CHERRY:
        return True
    return len(b) >= 1 and all(ch == CHERRY for ch in b)

def pi_rooted(children):
    """exact pi of tree = root with given child branches"""
    k = len(children)
    Z = Fr(1); S = Fr(0)
    for ch in children:
        Zc, xc, _ = bval(ch); Z *= Zc; S += xc
    return Z * (1 + S / k)

def canon(b):
    return tuple(sorted(canon(ch) for ch in b))

def nx_to_branches(G, r):
    """children branches of tree G rooted at r"""
    def rec(u, p):
        return canon(tuple(rec(v, u) for v in G[u] if v != p))
    return [rec(v, r) for v in G[r]]

if __name__ == "__main__":
    print("lambda in", float(LAM_LO), float(LAM_HI), "width", float(LAM_HI - LAM_LO))
    print("beta", float(BETA_LO), float(BETA_HI))
    print("kappa", float(KAP_LO), float(KAP_HI))
    print("gamma", float(GAM_LO), float(GAM_HI))
    print("h(q),h(1/3),h(1):", h(qf), h(1/3), h(1.0), "lambda", lam)
