"""Exhaustive check (all planted branches with <= N vertices) of g(b) >= h(y_b) for the kinked small-lambda witness W2
(theta2 = 4/5), and of the ceiling log T_b <= |b| f*."""
import subprocess, sys
import mpmath as mp
from core import fstar_mp
N = int(sys.argv[1]) if len(sys.argv) > 1 else 18
lams = [float(x) for x in sys.argv[2:]] or [0.001, 0.01, 0.03, 0.06, 0.1, 0.1282, 0.15]
for lam in lams:
    mp.mp.dps = 40
    F, j = fstar_mp(lam, 40); L = mp.mpf(lam)
    t = L/(2+L); yC = 1/(2+L); c = 1+L/2
    eps = 2*F - mp.log(c); yd = (mp.e**F - 1)/L; y2 = 1/(3+2*t); kap = L*y2
    f2 = (2*mp.log(c) + mp.log(1+2*t/3))/5; h2 = mp.mpf(4)/5*5*(F-f2)
    sa = h2/(y2-yd); sb = (eps-h2)/(yC-y2)
    pieces = [(sa, -sa*yd), (sb, h2 - sb*y2), (kap, eps - kap*yC)]
    args = ["./brute", str(N), repr(lam), mp.nstr(F, 20), mp.nstr(eps, 20), mp.nstr(yd, 20), mp.nstr(kap, 20), str(j)]
    for a, b in pieces: args += [mp.nstr(a, 20), mp.nstr(b, 20)]
    out = subprocess.run(args, capture_output=True, text=True)
    print(f"[W2] j*={j} " + out.stdout.strip(), flush=True)
