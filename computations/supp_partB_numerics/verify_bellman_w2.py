"""Dense numerical Bellman check for the kinked small-activity witness W2 (theta2 = 4/5) on (0, 3/20].
Same method as verify_bellman.py (double-precision scan + 50-digit refinement)."""
import sys, math
import numpy as np
import mpmath as mp
import verify_bellman as VB

class WS2(VB.WS):
    def __init__(self, lam, th2=mp.mpf(4)/5):
        super().__init__(lam)
        L = self.lamm; F = self.Fm
        t = L/(2+L); yC = 1/(2+L); c = 1+L/2
        eps = 2*F - mp.log(c); yd = (mp.e**F-1)/L; y2 = 1/(3+2*t); kap = L*y2
        f2 = (2*mp.log(c)+mp.log(1+2*t/3))/5; h2 = th2*5*(F-f2)
        sa = h2/(y2-yd); sb = (eps-h2)/(yC-y2)
        self.mp_pieces = [(sa, -sa*yd), (sb, h2-sb*y2), (kap, eps-kap*yC)]
        self.f_pieces = [(float(a), float(b)) for a, b in self.mp_pieces]
        self.kinks = [float(yd), float(y2), float(yC)]
    def h(self, y):
        out = np.zeros_like(np.asarray(y, dtype=float))
        for a, b in self.f_pieces: out = np.maximum(out, a*y+b)
        return out
    def Bmp(self, k, m, yb):
        lam = self.lamm; F = self.Fm
        h = lambda y: max([mp.mpf(0)] + [a*y+b for a, b in self.mp_pieces])
        yb = mp.mpf(yb); R = k+m*yb; d = k+m+1
        return (k+1)*F + m*h(yb) - mp.log(1+lam*R/d) - h(1/(d+lam*R))
    def grid(self, k, m, n=1500):
        g = np.linspace(0, 0.5, n); ks = self.kinks + [0.0, 0.5]
        if m > 0:
            for yk in self.kinks:
                yb = (((1/yk) - (k+m+1))/self.lam - k)/m
                if 0 <= yb <= 0.5: ks.append(yb)
        return np.unique(np.concatenate([g, ks]))

VB.WS = WS2
if __name__ == "__main__":
    lams = [float(x) for x in sys.argv[1:]] or [0.0005, 0.002, 0.005, 0.01, 0.02, 0.04, 0.06, 0.08, 0.1, 0.11, 0.12, 0.1282, 0.135, 0.14, 0.145, 0.15]
    bad = 0
    for lam in lams:
        W, worst, arm = VB.check(lam)
        if worst[0] <= 0: bad += 1
        print(f"[W2] lam={lam:.5f} j*={W.jstar} min margin (excl. equalities) = {worst[0]:.3e} at {worst[1]}  best-arm margin = {arm:.1e}", flush=True)
    print("violations:", bad)
