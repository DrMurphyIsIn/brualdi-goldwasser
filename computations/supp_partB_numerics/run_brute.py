"""Driver for brute.c: exhaustive planted branches with <= N vertices at sample activities."""
import subprocess, sys
import mpmath as mp
from core import fstar_mp
N = int(sys.argv[1]) if len(sys.argv) > 1 else 18
lams = [float(x) for x in sys.argv[2:]] or [0.1282, 0.15, 0.25, 0.4305, 0.5, 0.75, 0.8725, 1.0, 1.25, 1.5, 1.75, 1.99, 2.5, 3.0, 3.22]
for lam in lams:
    mp.mp.dps = 40
    F, j = fstar_mp(lam, 40)
    L = mp.mpf(lam)
    eps = 2 * F - mp.log(1 + L / 2)
    yd = (mp.exp(F) - 1) / L
    t = L / (2 + L)
    kap = L / (3 + 2 * t)
    out = subprocess.run(["./brute", str(N), repr(lam), mp.nstr(F, 20), mp.nstr(eps, 20), mp.nstr(yd, 20), mp.nstr(kap, 20), str(j)],
                         capture_output=True, text=True)
    print(f"j*={j:4d} |A_j*|={2*j+1:4d}  " + out.stdout.strip(), flush=True)
