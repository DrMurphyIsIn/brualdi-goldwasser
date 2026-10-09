"""Strictness inventory for the typed induction on (0, 0.1]: on every certified box of (0, 0.1], the UNCLIPPED upper bound of l(S_e)/lam is < 0 for every
spider e != 4 (3 <= e <= 240, plus the e > 240 tail bound), so the definitional clip l(S_e) <= 0 is needed only at e = 4 (A3)."""
import sys
sys.argv = ['x', '0.1', '0.0005', '0.006']
exec(open('certify_small.py').read().split('if __name__')[0])
worst = (mpf(-9), None); x = mpf(0); W = mpf('0.0005')
while x < mpf('0.1'):
    L = iv.mpf([x, x + W])
    FL = (3*Lg_lo(mpf(1)/2, L) + Lg_lo(3/(4*(2 + L)), L))/7
    luP2 = Lg_up(mpf(1)/2, L) - 2*FL; yP2 = 1/(2 + L)
    for e in list(range(3, 241)):
        if e == 4: continue
        R = (e-1)*yP2; lu = UP((e-1)*luP2 + Lg_up(R/e, L) - FL)
        if lu > worst[0]: worst = (lu, (e, float(x)))
    lt = UP(240*luP2 + iv.mpf(1)/2 - FL)
    if lt > worst[0]: worst = (lt, ('tail', float(x)))
    x += W
print("max over boxes and spiders e != 4 of the unclipped l(S_e)/lam upper bound:", float(worst[0]), "at", worst[1])
