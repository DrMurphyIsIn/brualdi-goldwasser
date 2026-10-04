"""(S6) for the witness W_1 (W* in older notation) at F = f3, hand-style table. Psi/t = (eps/t)(3/2 + (delta/t)/(u/t)) - D(2)/t, with
eps/t = ((3/2)L34 - Lm)/7, D(2)/t = (2/3)L23 - Lm/2, f3/t = (3 Lm + (3/4) L34)/7, u/t = 1 - (f3/t) Xe(f3)."""
import sys, mpmath as mp
from mpmath import iv
from handatoms import atoms, Xe, cover
def S6(t1, t2):
    A = atoms(t1, t2)
    phi3 = (3*A['Lm'] + iv.mpf(3)/4*A['L34'])/7
    f3 = A['t']*phi3
    ut = 1 - phi3*Xe(f3)
    et = (iv.mpf(3)/2*A['L34'] - A['Lm'])/7
    D2t = iv.mpf(2)/3*A['L23'] - A['Lm']/2
    return et*(iv.mpf(3)/2 + A['dt']/ut) - D2t
if __name__ == '__main__':
  for lam in [0.15, 0.2, 0.25, 0.3]:
    t0 = mp.mpf(lam)/(2+lam)
    rows = cover(S6, t0, mp.mpf('0.3229'))
    print(lam, len(rows), "min lower bound", mp.nstr(min(r[2] for r in rows), 3))
