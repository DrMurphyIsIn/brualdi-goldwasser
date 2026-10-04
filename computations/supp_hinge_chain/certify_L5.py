"""Rigorous interval certificate for the k = 0 (no leaf child) case of L5 on lam in [LO, HI], LO < 1+sqrt5.
U_lam(y) = -kappa(lam) (y - y_ch)^+, kappa = C F*, F* = log(1+lam/2)/2, y_ch = 1/(2+lam).
Claim for every m with 1 <= m <= ceil(HI+1) (covers the non-tail range m < max(lam+1, lam/kappa - 1)):
   Phi_m(lam, yb) = m U(yb) + log(1 + lam m yb/(m+1)) - F* - U(1/(m+1+lam m yb)) <= 0   for yb in [0, 1/2].
Method: mpmath.iv interval arithmetic (outward rounding), bisection of (lam, yb) boxes until sup Phi < 0."""
import sys, time
from mpmath import iv, mpf
iv.dps = 30
C = iv.mpf('1.6')
def U(y, kap, ych):          # -kappa*(y - ych)^+ on an interval y
    z = y - ych
    zp = iv.mpf([max(mpf(0), z.a), max(mpf(0), z.b)])
    return -kap * zp
def Phi_sup(m, L, Y):
    Fs = iv.log(1 + L/2) / 2
    kap = C * Fs; ych = 1 / (2 + L)
    yv = 1 / (m + 1 + L*m*Y)
    val = m*U(Y, kap, ych) + iv.log(1 + L*m*Y/(m+1)) - Fs - U(yv, kap, ych)
    return val.b
def certify(m, lam0, lam1, y0, y1, maxdepth=40):
    stack = [(lam0, lam1, y0, y1, 0)]; boxes = 0; worst = mpf('-inf')
    while stack:
        a, b, c, d, dep = stack.pop()
        s = Phi_sup(m, iv.mpf([a, b]), iv.mpf([c, d]))
        if s < 0:
            boxes += 1; worst = max(worst, s); continue
        if dep >= maxdepth:
            return False, (a, b, c, d, s), boxes
        # split the wider (relative) side
        if (b - a) / (lam1 - lam0) >= (d - c) / (y1 - y0):
            h = (a + b) / 2; stack += [(a, h, c, d, dep+1), (h, b, c, d, dep+1)]
        else:
            h = (c + d) / 2; stack += [(a, b, c, h, dep+1), (a, b, h, d, dep+1)]
    return True, worst, boxes
LO, HI = mpf('3.236067977'), mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf(100)
assert LO < 1 + mpf(5)**0.5
tot = 0; t0 = time.time()
import math
for m in range(1, int(math.ceil(HI + 1)) + 1):
    ok, info, nb = certify(m, LO, HI, mpf(0), mpf('0.5'))
    tot += nb
    if not ok:
        print(f"m={m}: FAILED at box {info}"); break
    if m <= 5 or m % 20 == 0: print(f"m={m:3d}: certified with {nb} boxes, max sup Phi = {float(info):.3e}  ({time.time()-t0:.0f}s)", flush=True)
else:
    print(f"ALL m in 1..{int(math.ceil(HI+1))} certified on lam in [{LO}, {HI}], yb in [0, 1/2]: {tot} boxes, {time.time()-t0:.0f}s")
