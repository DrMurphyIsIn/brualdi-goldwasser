"""Second implementation of the 63 interval rows of the low-degree certificates of part (B).
Written separately from handatoms.py, lowdeg_tables.py and the other programs of this folder; it reads only their
output files ../lowdeg_tables.out (the claimed boxes and lower bounds) and ../lowdeg_atoms.out (the tabulated atom
values) in order to compare.
python-flint arb (rigorous ball arithmetic, 256 bits) for every point value of log/exp/sqrt, and a hand-written
endpoint-interval class (lo/hi are exact arb points; every op takes the min/max over the rigorous endpoint balls).
Atoms are enclosed by their endpoint values; their monotonicity is checked separately in exact_checks.py.
The conditions are written from the statements, not from the code of the first program.
Also: gap/coverage check of the breakpoints, 30%-room check, comparison with the claimed lower bounds.
Program names: C1, C3, C7, C8 = P1, P3, P7, P8; C10 T1..T8b = P10 (U1)..(U8b); W* = W_1.
"""
import os
import re, sys
from fractions import Fraction as Fr
import flint
from flint import arb
flint.ctx.prec = 256

def A(q):  # exact rational -> arb
    q = Fr(q); return arb(q.numerator) / arb(q.denominator)

class I:
    """closed interval [lo, hi] with exact arb endpoints"""
    def __init__(s, lo, hi=None):
        if hi is None: hi = lo
        if not isinstance(lo, arb): lo = A(lo)
        if not isinstance(hi, arb): hi = A(hi)
        s.lo, s.hi = lo.lower(), hi.upper()
        assert not (s.hi < s.lo)
    @staticmethod
    def hull(balls):
        lo = min((b.lower() for b in balls), key=lambda x: x.mid())  # exact points: mid() exact
        hi = max((b.upper() for b in balls), key=lambda x: x.mid())
        return I(lo, hi)
    def _c(o): return o if isinstance(o, I) else I(o)
    def __add__(s, o): o = I._c(o); return I((s.lo + o.lo), (s.hi + o.hi))
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o): return s + (-I._c(o))
    def __rsub__(s, o): return I._c(o) - s
    def __mul__(s, o):
        o = I._c(o); return I.hull([s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi])
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = I._c(o)
        assert o.lo > 0 or o.hi < 0, "division by interval containing 0"
        return s * I.hull([1/o.lo, 1/o.hi])
    def __rtruediv__(s, o): return I._c(o) / s
    def sqrt(s):
        assert s.lo >= 0; return I(s.lo.sqrt(), s.hi.sqrt())
    def f(s): return (float(s.lo.mid()), float(s.hi.mid()))

# ---------------- point values (arb) of the atoms at an exact rational t ----------------
def Lm(t):  return arb(1) if t == 0 else -(-A(t)).log1p()/A(t)
def La(a, t):
    if t == 0: return arb(1)
    x = A(a)*A(t); return x.log1p()/x
def G2t(t):
    if t == 0: return A(Fr(1, 12))
    T = A(t); return (5*(3*T/4).log1p() - 7*(2*T/3).log1p() - (-T).log1p())/T
def kt(t):  T = A(t); return 2/((1-T)*(3+2*T))
def dt(t):  T = A(t); return (1-2*T)*(1+T)/((1-T)*(3+2*T))
def y4(t):  return 1/(5+4*A(t))
def ky4(t): T = A(t); return 2*T/((1-T)*(3+2*T)*(5+4*T))
def q3(t):  T = A(t); return 2/((1-T)*(4+3*T))
def Lq(t):
    if t == 0: return arb(1)
    x = A(t)*q3(t); return x.log1p()/x
def r8(t):  T = A(t); return (2*T-1)*(1+T)/((1-T)*(3+2*T)**2)
def Xp(s):  # (e^s-1)/s at an exact arb point s >= 0
    return arb(1) if s == 0 else s.expm1()/s

def enc(fn, t1, t2, inc):
    a, b = fn(t1), fn(t2)
    return I(a.lower(), b.upper()) if inc else I(b.lower(), a.upper())
def X(s):  # s an interval with s.lo >= 0; X increasing
    assert s.lo >= 0; return I(Xp(s.lo).lower(), Xp(s.hi).upper())

def atoms(t1, t2):
    d = dict(t=I(A(t1), A(t2)),
             Lm=enc(Lm, t1, t2, True), L23=enc(lambda t: La(Fr(2, 3), t), t1, t2, False),
             L34=enc(lambda t: La(Fr(3, 4), t), t1, t2, False), G2t=enc(G2t, t1, t2, True),
             kt=enc(kt, t1, t2, True), dt=enc(dt, t1, t2, False), y4=enc(y4, t1, t2, False),
             ky4=enc(ky4, t1, t2, True), q3=enc(q3, t1, t2, True), Lq=enc(Lq, t1, t2, False))
    d['phi3'] = (3*d['Lm'] + Fr(3, 4)*d['L34'])/7         # f3/t
    d['et'] = (Fr(3, 2)*d['L34'] - d['Lm'])/7              # eps/t at F = f3
    d['f3'] = d['t']*d['phi3']
    d['e1'] = d['phi3']*X(d['f3'])                         # (E-1)/t
    d['h2t'] = Fr(4, 5)*d['G2t']/7                          # h2/t
    return d

# ---------------- the conditions, transcribed from the statements ----------------
def C1(a, b):  d = atoms(a, b); return d['phi3'] - d['q3']*d['Lq']
def C3(a, b):  # (1+t1)^2 - 1.291 g(rhohat(t1)) t2 (1 + (1-t2)^(-1/2)); all point values
    T1, T2 = A(a), A(b)
    rho = arb(1)/2 - T1/4 - 7*T1**2/12 + T1**3/6
    g = rho*(1 - rho/(8+6*rho))**3*(4+3*rho)
    v = (1+T1)**2 - A(Fr(1291, 1000))*g*T2*(1 + 1/(1-T2).sqrt())
    return I(v.lower(), v.upper())
def C7(a, b):
    d = atoms(a, b); ut = 1 - d['e1']
    D2t = Fr(2, 3)*d['L23'] - d['Lm']/2
    return d['et']*(Fr(3, 2) + d['dt']/ut) - D2t
def C8(a, b):
    d = atoms(a, b); return d['Lm']/2 - Fr(2, 3)*d['L23'] - I(r8(a).lower(), r8(b).upper())
def T1(a, b): d = atoms(a, b); return d['kt'] - d['e1']
def T2(a, b):
    d = atoms(a, b); return (d['et'] - d['h2t'])/(1 - d['kt']) - d['h2t']/(d['kt'] - d['e1'])
def T3a(a, b): d = atoms(a, b); return d['et'] - d['h2t']
def T4(a, b):
    d = atoms(a, b); return d['y4']*(1 - d['ky4']) - (d['et'] - d['h2t'])/(1 - d['kt'])
def T5(a, b):
    d = atoms(a, b); E = 1 + d['t']*d['e1']; return 1 + 14*E - (d['kt'] - d['e1'])/d['h2t']
def T6(a, b): d = atoms(a, b); return Fr(14, 13) - X(d['f3'])
def T7(a, b):
    d = atoms(a, b); return d['phi3'] - d['kt'] - d['h2t'] + 2*(d['kt']*d['h2t']).sqrt()
def T8(a, b): d = atoms(a, b); return d['phi3'] + 5*d['et'] - Fr(5, 6)
def T8b(a, b): d = atoms(a, b); return d['et'] - Fr(1, 36)

# ---------------- parse the claimed rows from ../lowdeg_tables.out ----------------
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
out = open(os.path.join(SRC, 'lowdeg_tables.out')).read()
blocks = re.split(r'^== ', out, flags=re.M)[1:]
claimed = {}
for bl in blocks:
    head, *lines = bl.strip().split('\n')
    name = head.split(':')[0].strip()
    rows = []
    for ln in lines:
        m = re.match(r'\s*\[(\S+), (\S+)\]\s+lower bound (\S+)', ln)
        rows.append((Fr(m.group(1)), Fr(m.group(2)), float(m.group(3))))
    claimed[name] = rows

SPEC = [('C1', 'C1 (S2)', C1, Fr(0), Fr(6181, 10000)),
        ('C3', 'C3 (S4)', C3, Fr(0), Fr(6181, 10000)),
        ('C7', 'C7 (S6), W*, lam in [3/20, 0.954]', C7, Fr(3, 43), Fr(3229, 10000)),
        ('C8', 'C8 (S6), lam >= 2', C8, Fr(1, 2), Fr(6181, 10000))]
W2C = dict(T1=T1, T2=T2, T3a=T3a, T4=T4, T5=T5, T6=T6, T7=T7, T8=T8, T8b=T8b)

report = []
nrows = 0; allok = True
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); report.append(s)

P('| check | box [t1,t2] | claimed LB | recomputed LB | value at midpoint | LB/mid | gap-free |')
P('|---|---|---|---|---|---|---|')
for key, oname, fn, a, b in SPEC:
    rows = [r for k, r in claimed.items() if k.startswith(oname)][0]
    # coverage
    assert rows[0][0] == a and rows[-1][1] == b, (key, rows[0][0], rows[-1][1])
    for (x, y, _), (x2, _, _) in zip(rows, rows[1:]):
        assert y == x2 and x < y
    for x, y, v in rows:
        lb = fn(x, y).lo; mid = (x + y)/2; pv = fn(mid, mid)
        ratio = float(lb.mid())/float(pv.lo.mid())
        ok = lb > 0 and ratio >= 0.3
        allok &= bool(lb > 0); nrows += 1
        P(f'| {key} | [{x}, {y}] | {v:.4g} | {float(lb.mid()):.6g} | {float(pv.lo.mid()):.6g} | {ratio:.3f} | yes |' + ('' if ok else ' **FAIL**'))
for k, fn in W2C.items():
    rows = claimed['C10 ' + k]
    assert rows[0][0] == 0 and rows[-1][1] == Fr(3, 43) and all(rows[i][1] == rows[i+1][0] for i in range(len(rows)-1)), k
    for x, y, v in rows:
        lb = fn(x, y).lo; mid = (x + y)/2; pv = fn(mid, mid)
        ratio = float(lb.mid())/float(pv.lo.mid())
        allok &= bool(lb > 0); nrows += 1
        P(f'| C10 {k} | [{x}, {y}] | {v:.4g} | {float(lb.mid()):.6g} | {float(pv.lo.mid()):.6g} | {ratio:.3f} | yes |' + ('' if (lb > 0 and ratio >= 0.3) else ' **FAIL**'))
P(f'\nrows recomputed: {nrows}; all lower bounds positive: {allok}')

# atom table spot-check vs lowdeg_atoms.out
worst = 0
for ln in open(os.path.join(SRC, 'lowdeg_atoms.out')).read().split('\n')[1:]:
    if not ln.strip(): continue
    p, *vals = ln.split(); p = Fr(p); vals = [float(v) for v in vals]
    mine = [Lm(p), La(Fr(2, 3), p), La(Fr(3, 4), p), None, G2t(p), kt(p), dt(p), y4(p)]
    for v, m in zip(vals, mine):
        if m is None: continue
        worst = max(worst, abs(v - float(m.mid())))
P(f'lowdeg_atoms.out: max |tabulated - recomputed| over all breakpoints, 7 atoms = {worst:.2e}')
