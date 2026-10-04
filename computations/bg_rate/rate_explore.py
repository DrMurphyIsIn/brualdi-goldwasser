"""Explore the rate-eta Bellman potential H = h - eta*w under a cap on the number of children.
w(1)=1, w(1/3)=2, w(q)=11, linear on [q,1/3] and [1/3,1], slope -ap on [0,q] (w(x)=11+ap(q-x)).
Condition (per c<=C): PhiH_c(S) = lam - eta + c H(S/c) - log(1+S/(c+1)) - H(1/(c+1+S)) >= 0 on [0,c]."""
import os; os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np, math, sys
from core import lam, beta, kap, gam, qf

A = 9 / (1 / 3 - qf)
def make(eta, ap):
    def w(x):
        x = np.asarray(x, float)
        return np.where(x <= qf, 11 + ap * (qf - x), np.where(x <= 1/3, 11 - A * (x - qf), 2 - 1.5 * (x - 1/3)))
    def h(x):
        x = np.asarray(x, float)
        return np.where(x <= 1/3, kap * (x - qf) ** 2, beta + gam * (x - 1/3))
    def H(x):
        return h(x) - eta * w(x)
    return H, w

def minPhi(c, H, eta, npts=4001):
    if c == 0:
        return lam - eta - H(1.0)
    S = np.linspace(0, c, npts)
    v = lam - eta + c * H(S / c) - np.log1p(S / (c + 1)) - H(1 / (c + 1 + S))
    return v.min()

def ok(C, eta, ap):
    H, w = make(eta, ap)
    if eta * (A - 1.5) > gam - 2 * kap * (1/3 - qf):
        return False
    return all(minPhi(c, H, eta) >= -1e-12 for c in range(0, C + 1))

def best_eta(C, ap):
    lo, hi = 0.0, 0.01
    for _ in range(40):
        mid = (lo + hi) / 2
        if ok(C, mid, ap): lo = mid
        else: hi = mid
    return lo

if __name__ == "__main__":
    for C in [1, 2, 3, 4, 5, 6, 9, 12, 16, 22]:
        row = []
        for ap in [0, 10, 20, 30, A]:
            row.append(best_eta(C, ap))
        print(C, " ".join(f"{e:.6f}" for e in row))
