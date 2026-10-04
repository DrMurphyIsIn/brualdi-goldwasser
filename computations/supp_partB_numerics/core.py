"""Core quantities for the part (B) numerical checks (float64 and mpmath versions).

Notation follows sec:lambda of the paper:
  c = 1 + lam/2, t = lam/(2+lam), yC = 1/(2+lam), f_j = (j log c + log(1 + t j/(j+1)))/(2j+1),
  F = f* = max_j f_j, eps = 2F - log c, ydag = (e^F - 1)/lam.
Witness family W(theta, alpha):
  y0 = theta*ydag, s1 = eps/(yC - y0), kappa = alpha*F/t,
  h(y) = max(0, s1 (y - y0), eps + kappa (y - yC)).
alpha = 1, theta = 1 is the window witness of sec:lam-window (kappa = (F/2)/(1/2 - yC) = F/t).
Leaf-exempt Bellman margin:
  B_{k,m}(yb) = (k+1)F + m h(yb) - log(1 + lam (k + m yb)/(k+m+1)) - h(1/(k+m+1+lam(k+m yb))).
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "1")
import math
import numpy as np
import mpmath as mp


def arm_rates(lam, J=None):
    c = 1 + lam / 2
    t = lam / (2 + lam)
    if J is None:
        J = 50
    js = np.arange(1, J + 1, dtype=float)
    f = (js * math.log(c) + np.log1p(t * js / (js + 1))) / (2 * js + 1)
    return js, f


def fstar(lam):
    """float64 best arm rate and best arm index (unimodal in j)."""
    J = 64
    while True:
        js, f = arm_rates(lam, J)
        i = int(np.argmax(f))
        if i < J - 5:
            return float(f[i]), int(js[i])
        J *= 4


def fstar_mp(lam, dps=50):
    mp.mp.dps = dps
    lam = mp.mpf(lam)
    c = 1 + lam / 2
    t = lam / (2 + lam)
    def f(j):
        j = mp.mpf(j)
        return (j * mp.log(c) + mp.log(1 + t * j / (j + 1))) / (2 * j + 1)
    _, j0 = fstar(float(lam))
    best = max(range(max(1, j0 - 3), j0 + 4), key=lambda j: f(j))
    return f(best), best


class Wit:
    def __init__(self, lam, theta=1.0, alpha=1.0, F=None):
        self.lam = lam
        self.c = 1 + lam / 2
        self.t = lam / (2 + lam)
        self.yC = 1 / (2 + lam)
        if F is None:
            F, j = fstar(lam)
            self.jstar = j
        self.F = F
        self.eps = 2 * F - math.log(self.c)
        self.ydag = (math.exp(F) - 1) / lam
        self.y0 = theta * self.ydag
        self.w = self.yC - self.ydag
        self.s1 = self.eps / (self.yC - self.y0)
        self.kappa = alpha * F / self.t

    def h(self, y):
        y = np.asarray(y, dtype=float)
        return np.maximum(0.0, np.maximum(self.s1 * (y - self.y0), self.eps + self.kappa * (y - self.yC)))

    def B(self, k, m, yb):
        lam = self.lam
        yb = np.asarray(yb, dtype=float)
        R = k + m * yb
        d = k + m + 1
        return (k + 1) * self.F + m * self.h(yb) - np.log1p(lam * R / d) - self.h(1 / (d + lam * R))


def ygrid(W, n=4001):
    g = np.linspace(0, 0.5, n)
    extra = [W.yC, W.y0, W.ydag, 0.5]
    return np.unique(np.concatenate([g, extra]))
