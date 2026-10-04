"""Low-degree ('hand-checkable') versions of the certificates C1, C2, C3, C7, C8, C10.
Each condition is a function of t, written in terms of MONOTONE ATOMS (handatoms.py); on a box [t1,t2] each atom is
replaced by its two endpoint values (exact monotonicity), and the condition's lower bound is computed by interval
arithmetic (mpmath.iv, outward rounding). A row is checkable with a calculator: evaluate the atoms at t1 and t2.
Breakpoints are rationals on a grid of mesh 1/2000 (W2: the three points 0, 3/86, 3/43).
Writes lowdeg_tables.out (all rows) and lowdeg_summary.tex (summary table).
"""
import mpmath as mp
from mpmath import iv
from fractions import Fraction as Fr
from handatoms import atoms, atoms2, Xe
import w2_table as W2
iv.dps = 30

def M(x): return mp.mpf(x.numerator)/x.denominator

SAFE = mp.mpf('0.3')   # each row must keep at least 30% of the pointwise value at its midpoint

def okrow(fn, x, y):
    v = fn(M(x), M(y))
    mid = (M(x) + M(y))/2
    p = fn(mid, mid)
    return v, (v.a > 0 and v.a >= SAFE*p.a)

def greedy(fn, a, b, mesh=Fr(1, 2000)):
    rows = []; x = a
    while x < b:
        best = None
        k = 1
        while True:
            y = min(x + k*mesh, b)
            v, good = okrow(fn, x, y)
            if good: best = (y, v)
            else: break
            if y == b: break
            k = k*2 if best is not None else k
        if best is None:
            raise RuntimeError(f"cannot start at {x}")
        # refine upward linearly between best and failure
        y0 = best[0]
        while y0 < b:
            y1 = min(y0 + mesh, b); v, good = okrow(fn, x, y1)
            if good: best = (y1, v); y0 = y1
            else: break
        rows.append((x, best[0], best[1].a)); x = best[0]
    return rows

# ---- C3 / (S4): 1.291 g(rhohat(t1)) t2 (1 + (1-t2)^(-1/2)) <= (1+t1)^2 ; g increasing, rhohat decreasing
def g(r): return r*(1 - r/(8+6*r))**3*(4+3*r)
def rh(t): return iv.mpf(1)/2 - t/4 - 7*t**2/12 + t**3/6
def S4(t1, t2):
    T1, T2 = iv.mpf(t1), iv.mpf(t2)
    return (1+T1)**2 - iv.mpf('1.291')*g(rh(T1))*T2*(1 + 1/iv.sqrt(1-T2))
# ---- C2 / (S3): (11/12)(1-t)^(-1/2)(1 - kappa y4) - (5+4t)/6 >= 0 ; kappa*y4 increasing
def ky4(T): return 2*T/((1-T)*(3+2*T)*(5+4*T))
def S3(t1, t2):
    T1, T2 = iv.mpf(t1), iv.mpf(t2)
    return iv.mpf(11)/12/iv.sqrt(1-T1)*(1 - ky4(T2)) - (5+4*T2)/6
# ---- C1 / (S2): phi3 - q3 Lq >= 0, q3 = lam y3/t = 2/((1-t)(4+3t)) increasing, Lq = log(1+x)/x at x = t q3 (decreasing)
def S2(t1, t2):
    A = atoms(t1, t2)
    phi3 = (3*A['Lm'] + iv.mpf(3)/4*A['L34'])/7
    def q3(T): return 2/((1-T)*(4+3*T))
    def Lq(T):
        if T.a == 0 and T.b == 0: return iv.mpf(1)
        x = T*q3(T); return iv.log(1+x)/x
    q = iv.mpf([q3(iv.mpf(t1)).a, q3(iv.mpf(t2)).b])
    L = iv.mpf([Lq(iv.mpf(t2)).a, Lq(iv.mpf(t1)).b])
    return phi3 - q*L
# ---- C8 / (S6, lam >= 2): -D(2) >= kappa (y2 - yC);  -D(2)/t = Lm/2 - (2/3) L23 ;
#      kappa (y2 - yC)/t = (2t-1)(1+t)/((1-t)(3+2t)^2) =: r(t) increasing on [1/2, 1/phi]
def S6hi(t1, t2):
    A = atoms(t1, t2)
    def r(T): return (2*T-1)*(1+T)/((1-T)*(3+2*T)**2)
    rr = r(iv.mpf(t2)).b
    return A['Lm']/2 - iv.mpf(2)/3*A['L23'] - rr
# ---- C7 / (S6, witness W_1 (printed as W*), F = f3) on [3/43, 0.3229]
from s6_table import S6

out = open('lowdeg_tables.out', 'w')
summ = []
def run(name, fn, a, b, mesh=Fr(1, 2000)):
    rows = greedy(fn, a, b, mesh)
    out.write(f"== {name}: {len(rows)} rows on t in [{a}, {b}]\n")
    for x, y, v in rows:
        out.write(f"   [{x}, {y}]  lower bound {mp.nstr(mp.mpf(v), 4)}\n")
    mn = min(r[2] for r in rows)
    print(f"{name:34s} rows={len(rows):3d}  min lower bound={mp.nstr(mn, 4)}  breaks={[str(r[1]) for r in rows]}", flush=True)
    summ.append((name, a, b, len(rows), mn, [r[1] for r in rows]))
    return rows

TPHI = Fr(6181, 10000)
run("C1 (S2): A3 message flat", S2, Fr(0), TPHI)
run("C2 (S3): left derivative m<=4", S3, Fr(0), TPHI)
run("C3 (S4): threshold", S4, Fr(0), TPHI)
run("C7 (S6), W*, lam in [3/20, 0.954]", S6, Fr(3, 43), Fr(3229, 10000))
run("C8 (S6), lam >= 2", S6hi, Fr(1, 2), TPHI)
# W2 on (0, 3/43]: start from the two boxes [0,3/86], [3/86,3/43]; any box failing the 30% rule is split
# (into halves, recursively) until every box meets it.
def c10_rows(f):
    stack = [(Fr(3, 86), Fr(3, 43)), (Fr(0), Fr(3, 86))]
    rows = []
    while stack:
        x, y = stack.pop()
        v, good = okrow(f, x, y)
        if good:
            rows.append((x, y, v.a)); continue
        assert y - x > Fr(1, 10**6), (x, y)
        m = (x + y)/2
        stack.append((m, y)); stack.append((x, m))
    rows.sort()
    return rows
for k, f in W2.CONDS.items():
    rows = c10_rows(f)
    for (x, y, v) in rows:
        _, good = okrow(f, x, y); assert good and v > 0
    out.write(f"== C10 {k}: {len(rows)} rows\n" + "".join(f"   [{x}, {y}]  lower bound {mp.nstr(mp.mpf(v),4)}\n" for x, y, v in rows))
    mn = min(r[2] for r in rows)
    print(f"C10 {k:30s} rows={len(rows):3d}  min lower bound={mp.nstr(mn,4)}  breaks={[str(r[1]) for r in rows]}", flush=True)
    summ.append((f"C10 {k}", Fr(0), Fr(3, 43), len(rows), mn, [r[1] for r in rows]))
out.close()
with open('lowdeg_summary.tex', 'w') as f:
    for name, a, b, n, mn, br in summ:
        f.write(f"{name} & $[{a},{b}]$ & {n} & ${mp.nstr(mp.mpf(mn),3)}$\\\\\n")
print("ALL ROWS CERTIFIED")

# ---- reader's aid: atom values at every breakpoint used (12 digits, rigorous midpoints of tight enclosures)
from handatoms import Lm_, La_, Lx_, kt_, dt_, y4_, G2t_
pts = set()
for name, a, b, n, mn, br in summ:
    pts.add(a); pts.update(br)
with open('lowdeg_atoms.out', 'w') as f:
    f.write("t | Lm=-log(1-t)/t | L23 | L34 | Lx | G2t | kt | dt | y4   (L_a = log(1+a t)/(a t); value 1 at t=0)\n")
    for p in sorted(pts):
        T = iv.mpf(M(p))
        vals = [Lm_(T), La_(iv.mpf(2)/3)(T), La_(iv.mpf(3)/4)(T), Lx_(T), G2t_(T), kt_(T), dt_(T), y4_(T)]
        f.write(f"{str(p):>12s} " + " ".join(mp.nstr(mp.mpf(v.mid), 12) for v in vals) + "\n")
print("wrote lowdeg_atoms.out with", len(pts), "breakpoints")
