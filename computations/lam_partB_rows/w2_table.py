"""Hand-style tables for the kinked witness W2 (theta2 = 4/5) on (0, t_K], t_K = 3/43 (lam_K = 3/20).
All conditions in scaled form (divided by t), in terms of monotone atoms (handatoms.py):
  phi3 = f3/t = (3 Lm + (3/4) L34)/7,  e1 = (E-1)/t = phi3 Xe(t phi3),  et = eps/t = ((3/2) L34 - Lm)/7,
  h2t = theta2 G2t/7,  kt = kappa/t.
 T1  : kt - e1 > 0                                   (ydag < y2)
 T2  : (et - h2t)/(1 - kt) - h2t/(kt - e1) >= 0      (s_a <= s_b)
 T3a : et - h2t > 0                                  (eps > h2)
 T4  : y4 (1 - t kt y4) - (et - h2t)/(1 - kt) >= 0   (s_b <= lam y4 (1 - kappa y4))
 T5  : 1 + 14 (1 + t e1) - (kt - e1)/h2t >= 0       (M_a <= 14)
 T6  : 14/13 - Xe(t phi3) >= 0                      (N^dag_m, m <= 13)
 T7  : phi3 - kt - h2t + 2 sqrt(kt h2t) >= 0         (N^2_m for every m, by AM-GM)
 T8  : phi3 + 5 et - 5/6 >= 0  and  et - 1/36 >= 0   (N^C_5, and N^C_m increasing in m >= 5)
"""
import mpmath as mp
from mpmath import iv
from handatoms import atoms2, Xe, cover
TH2 = iv.mpf(4)/5
def base(t1, t2):
    A = atoms2(t1, t2)
    phi3 = (3*A['Lm'] + iv.mpf(3)/4*A['L34'])/7
    e1 = phi3*Xe(A['t']*phi3)
    et = (iv.mpf(3)/2*A['L34'] - A['Lm'])/7
    h2t = TH2*A['G2t']/7
    return A, phi3, e1, et, h2t
def T1(a,b): A,p,e1,et,h=base(a,b); return A['kt']-e1
def T2(a,b): A,p,e1,et,h=base(a,b); return (et-h)/(1-A['kt']) - h/(A['kt']-e1)
def T3a(a,b): A,p,e1,et,h=base(a,b); return et-h
def T4(a,b): A,p,e1,et,h=base(a,b); return A['y4']*(1-A['t']*A['kt']*A['y4']) - (et-h)/(1-A['kt'])
def T5(a,b): A,p,e1,et,h=base(a,b); return 1+14*(1+A['t']*e1) - (A['kt']-e1)/h
def T6(a,b): A,p,e1,et,h=base(a,b); return iv.mpf(14)/13 - Xe(A['t']*p)
def T7(a,b): A,p,e1,et,h=base(a,b); return p - A['kt'] - h + 2*iv.sqrt(A['kt']*h)
def T8(a,b): A,p,e1,et,h=base(a,b); return p + 5*et - iv.mpf(5)/6
def T8b(a,b): A,p,e1,et,h=base(a,b); return et - iv.mpf(1)/36
CONDS = dict(T1=T1, T2=T2, T3a=T3a, T4=T4, T5=T5, T6=T6, T7=T7, T8=T8, T8b=T8b)
if __name__ == "__main__":
    import sys
    tK = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf(3)/43
    tot = 0
    for k, f in CONDS.items():
        rows = cover(f, 0, tK)
        tot += len(rows)
        print(f"{k:4s} rows={len(rows):3d}  min lower bound={mp.nstr(min(r[2] for r in rows),3)}  breaks={[mp.nstr(r[1],4) for r in rows]}")
    print("total rows", tot)
