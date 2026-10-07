"""Second implementation of the rate gaps and the comparison with explicit spiders (shared definitions).
Written separately from ../conc.py, core.py and ivtools.py and imports none of them.
Ball arithmetic via python-flint arb at 200 bits; exact rationals for Z, x, S."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
from fractions import Fraction as Fr
import math
from flint import arb, ctx
ctx.prec = 200

def A(fr):  # exact rational -> arb ball
    return arb(fr.numerator) / arb(fr.denominator)

LAM = (A(Fr(621, 64))).log() / 11
BETA = 2 * LAM - A(Fr(3, 2)).log()
Q = Fr(3, 23)
KAP = BETA / (A(Fr(1, 3) - Q) ** 2)
GAM = arb(3) / 2 * (LAM - BETA)
SLOPE_L = 2 * KAP * A(Fr(1, 3) - Q)     # h'(1/3-)
W1 = Fr(621, 14)   # -w' on [0,1/3]
W2 = Fr(3, 2)      # -w' on [1/3,1]

ETA = {1: '2791/2500000', 2: '2791/2500000', 3: '2791/2500000', 4: '2791/2500000', 5: '2791/2500000',
       6: '9387/10000000', 7: '4183/5000000', 8: '7507/10000000', 9: '1701/2500000', 10: '311/500000',
       11: '179/312500', 12: '5309/10000000', 13: '2473/5000000', 14: '463/1000000', 15: '34/78125',
       16: '2053/5000000', 17: '1943/5000000', 18: '461/1250000', 19: '351/1000000', 20: '837/2500000',
       21: '1/3125', 22: '613/2000000'}
ETA = {k: Fr(v) for k, v in ETA.items()}

def h(x):   # x Fraction
    if x <= Fr(1, 3):
        return KAP * A(x - Q) ** 2
    return BETA + GAM * A(x - Fr(1, 3))
def w(x):
    if x <= Fr(1, 3):
        return 11 - W1 * (x - Q)
    return 2 - W2 * (x - Fr(1, 3))
def H(x, eta):
    return h(x) - A(eta * w(x))
def dH_left(x, eta):  # left derivative of H at x (x>0)
    if x <= Fr(1, 3):
        return 2 * KAP * A(x - Q) + A(eta * W1)
    return GAM + A(eta * W2)
def dH_right(x, eta):
    if x < Fr(1, 3):
        return 2 * KAP * A(x - Q) + A(eta * W1)
    return GAM + A(eta * W2)

def convex_ok(eta):
    return (GAM - SLOPE_L - A(eta * (W1 - W2))) > 0

# branches: (Z, x, size) exact
def branch(children):
    c = len(children); Z = Fr(1); S = Fr(0); n = 1
    for (z, x, s) in children:
        Z *= z; S += x; n += s
    return (Z * (c + 1 + S) / (c + 1), 1 / (c + 1 + S), n)
LEAF = (Fr(1), Fr(1), 1)
CH = branch([LEAF])
_arm = {0: LEAF}
def arm(j):
    if j not in _arm:
        _arm[j] = branch([CH] * j)
    return _arm[j]

_logcache = {}
def logfr(z):
    if z not in _logcache:
        _logcache[z] = A(z).log()
    return _logcache[z]

def g(b):  # deficit
    return LAM * b[2] - logfr(b[0])

def dHslack(b, eta):  # delta^H(b)
    return g(b) - A(eta * b[2]) - H(b[1], eta)

# ---- concave max over [0, Y] of f(y) = log(1 + (S + j y)/k) - j H(y) ----
def _fl(v):
    return float(v.mid())
def fmax_upper(S, j, k, eta, Y):
    """rigorous upper bound on max_{0<=y<=Y} f (f concave, requires convex H).
    S, Y Fractions."""
    # float search for maximizer
    Sf = float(S)
    lam = _fl(LAM); kap = _fl(KAP); gam = _fl(GAM); q = 3 / 23; e = float(eta)
    def fp(y, side):
        if (y < 1 / 3) or (y == 1 / 3 and side < 0):
            hp = 2 * kap * (y - q) + e * 621 / 14
        else:
            hp = gam + e * 1.5
        return j / (k + Sf + j * y) - j * hp
    Yf = float(Y)
    cands = [0.0, Yf]
    if Yf > 1 / 3: cands.append(1 / 3)
    for lo, hi in [(0.0, min(1 / 3, Yf)), (1 / 3, Yf)]:
        if hi <= lo: continue
        if fp(lo, 1) > 0 and fp(hi, -1) < 0:
            a, b = lo, hi
            for _ in range(80):
                m = (a + b) / 2
                if fp(m, 0) > 0: a = m
                else: b = m
            cands.append((a + b) / 2)
    def ff(y):
        if y <= 1 / 3: hv = kap * (y - q) ** 2 - e * (11 - 621 / 14 * (y - q))
        else: hv = (2 * lam - math.log(1.5)) + gam * (y - 1 / 3) - e * (2 - 1.5 * (y - 1 / 3))
        return math.log(1 + (Sf + j * y) / k) - j * hv
    y0f = max(cands, key=ff)
    if abs(y0f - 1 / 3) < 1e-15: y0 = Fr(1, 3)
    elif y0f == 0: y0 = Fr(0)
    elif y0f == Yf: y0 = Y
    else: y0 = Fr(y0f).limit_denominator(10 ** 13)
    fy0 = (1 + A((S + j * y0) / k)).log() - j * H(y0, eta)
    base = 1 / (A(k + S + j * y0)) * j
    gR = base - j * dH_right(y0, eta) if y0 < Y else None
    gL = base - j * dH_left(y0, eta) if y0 > 0 else None
    ub = fy0.upper()
    extra = arb(0)
    cand_extra = [arb(0)]
    if gR is not None:
        cand_extra.append(arb(gR.upper()) * A(Y - y0))
    if gL is not None:
        cand_extra.append(-arb(gL.lower()) * A(y0))
    mx = max(float(c.upper()) for c in cand_extra)
    # rigorous: add upper of the chosen max (all are rigorous upper bounds)
    best = max(cand_extra, key=lambda c: float(c.upper()))
    return (arb(ub) + best).upper()   # returns arb (upper endpoint as exact ball)
