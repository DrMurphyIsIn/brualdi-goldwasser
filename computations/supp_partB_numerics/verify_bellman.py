"""Dense numerical check of the leaf-exempt Bellman inequality for the witness W_1 (W* in older notation)
   h = max(0, s1 (y - ydag), eps + kappa (y - yC)),  kappa = lam/(3+2t),  theta = 1,
at many activities in [0.1282, 1+sqrt5). Double precision scan over yb (grid + kinks + preimages of the kinks of h
under yb -> 1/(d + lam R)), all k <= KMAX, m <= MMAX; every local minimum below a threshold is re-evaluated in
mpmath (50 digits) and refined by golden section. Reports the smallest margin per lambda, excluding the two designed
equalities (cherry (1,0); best arm (0, j*, yC)), and separately the margin at the best arm.
Usage: python3 verify_bellman.py [N_lambda]
"""
import sys, math
import numpy as np
import mpmath as mp
from core import fstar_mp

KMAX, MMAX = 8, 6000


class WS:
    def __init__(self, lam):
        mp.mp.dps = 50
        F, j = fstar_mp(lam, 50)
        self.jstar = j
        self.lam = lam
        self.t = lam / (2 + lam)
        self.yC = 1 / (2 + lam)
        self.F = float(F)
        self.eps = float(2 * F - mp.log(1 + mp.mpf(lam) / 2))
        self.yd = float((mp.exp(F) - 1) / lam)
        self.s1 = self.eps / (self.yC - self.yd)
        self.kap = lam / (3 + 2 * self.t)
        self.Fm = F
        self.lamm = mp.mpf(lam)

    def h(self, y):
        return np.maximum(0.0, np.maximum(self.s1 * (y - self.yd), self.eps + self.kap * (y - self.yC)))

    def B(self, k, m, yb):
        R = k + m * yb
        d = k + m + 1
        return (k + 1) * self.F + m * self.h(yb) - np.log1p(self.lam * R / d) - self.h(1 / (d + self.lam * R))

    def Bmp(self, k, m, yb):
        lam = self.lamm
        F = self.Fm
        eps = 2 * F - mp.log(1 + lam / 2)
        yC = 1 / (2 + lam)
        yd = (mp.exp(F) - 1) / lam
        s1 = eps / (yC - yd)
        t = lam / (2 + lam)
        kap = lam / (3 + 2 * t)
        h = lambda y: max(mp.mpf(0), s1 * (y - yd), eps + kap * (y - yC))
        yb = mp.mpf(yb)
        R = k + m * yb
        d = k + m + 1
        return (k + 1) * F + m * h(yb) - mp.log(1 + lam * R / d) - h(1 / (d + lam * R))

    def grid(self, k, m, n=1500):
        g = np.linspace(0, 0.5, n)
        ks = [self.yC, self.yd, 0.0, 0.5]
        if m > 0:
            for yk in (self.yd, self.yC):
                yb = ((1 / yk) - (k + m + 1)) / self.lam - k
                yb /= m
                if 0 <= yb <= 0.5:
                    ks.append(yb)
        return np.unique(np.concatenate([g, ks]))


def check(lam):
    W = WS(lam)
    worst = (math.inf, None)
    arm = None
    for k in range(0, KMAX + 1):
        mmax = MMAX if k == 0 else 200
        for m in range(0, mmax + 1):
            if (k, m) in ((0, 0), (1, 0)):
                continue
            if m == 0:
                v = W.Bmp(k, 0, 0)
                if v < worst[0]:
                    worst = (float(v), (k, m, 0.0))
                continue
            ys = W.grid(k, m)
            v = W.B(k, m, ys)
            if k == 0 and m == W.jstar:
                arm = float(W.Bmp(0, m, W.yC))
                v = np.where(np.abs(ys - W.yC) < 1e-12, np.inf, v)
            i = int(np.argmin(v))
            if v[i] < worst[0] + 1e-9 or v[i] < 1e-6:
                # refine in mpmath around the minimizer
                a = ys[max(i - 1, 0)]
                b = ys[min(i + 1, len(ys) - 1)]
                f = lambda y: W.Bmp(k, m, y)
                lo, hi = mp.mpf(a), mp.mpf(b)
                for _ in range(60):
                    x1 = lo + (hi - lo) * mp.mpf('0.381966')
                    x2 = lo + (hi - lo) * mp.mpf('0.618034')
                    if f(x1) < f(x2):
                        hi = x2
                    else:
                        lo = x1
                cand = [f(mp.mpf(ys[i])), f(lo)]
                if k == 0 and m == W.jstar:
                    cand = [c for c in cand if True]
                    if abs(float(lo) - W.yC) < 1e-10:
                        cand = [f(mp.mpf(ys[i]))]
                val = float(min(cand))
                if val < worst[0]:
                    worst = (val, (k, m, float(ys[i])))
    return W, worst, arm


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    lc = 1 + math.sqrt(5)
    lams = sorted(set([0.1282, 0.13, 0.2, 0.4305, 0.4306, 0.8725, 1.0, 1.1924, 1.4356, 2.0, 3.0, 3.22, 3.23, 3.2359]
                      + list(np.round(np.linspace(0.1282, 3.2359, N), 5))))
    bad = 0
    for lam in lams:
        W, worst, arm = check(float(lam))
        flag = "" if worst[0] > 0 else "  <-- VIOLATION"
        if worst[0] <= 0:
            bad += 1
        print(f"lam={lam:.5f} j*={W.jstar:5d} min margin (excl. equalities) = {worst[0]:.3e} at (k,m,yb)={worst[1]}  "
              + (f"best-arm margin at yC = {arm:.1e}" if arm is not None else "best arm beyond MMAX") + flag, flush=True)
    print("violations:", bad)
