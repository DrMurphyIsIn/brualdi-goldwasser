"""Stability theorem check: for fixed k, find the range of n on which every tree with nu=k
that is NOT a connector-star is provably below the best connector-star.

Upper bound for non-connector-stars (see the proof of the structure theorem for the matching number):
    pi(T) <= 2^k (1 - G/(2k))^k <= 2^k exp(-G/2),
    G = min( (m+sqrt(m+1))^2 / (2(N+m)),  S_ns^2 / N ),   m = k-1, N = n-1,
    S_ns = min( (k-3)/sqrt2 + 2 sqrt(2/3) + sqrt((3k-5)/6),  (k-2)/sqrt2 + sqrt(2/3) + sqrt((3k-4)/6) )
(the first entry of G covers covers with e(C) >= 1 internal edges, the second e(C)=0 but some two
hubs with w >= 2/3).
Lower bound: exact best connector-star value (Fractions), and for the analytic tail the explicit
construction with equal peripheral degrees D = floor(y), y = N/(m+sqrt m).

Output: the list of n in [3k-2, N1] where the check fails (these must be covered by the exact DP),
and N1 beyond which the analytic argument applies.
"""
import sys, math
from fractions import Fraction as Fr
from mpmath import mp, mpf, sqrt as msqrt
mp.dps = 60


def cs_value(n, k, a):
    """exact pi of the balanced connector-star with a center leaves, or None if infeasible"""
    m = k - 1
    L = n - 1 - a - 2 * m
    if a < 0 or L < m:
        return None
    q, r = divmod(L, m)
    ls = [q + 1] * r + [q] * (m - r)
    D0 = a + m
    p = Fr(1)
    for l in ls:
        p *= Fr(4 * l + 3, 2 * (l + 1))
    p *= 2 - sum(Fr(2 * l + 2, 4 * l + 3) for l in ls) / D0
    return p


def cs_best(n, k):
    best = None; arg = []
    for a in range(0, n):
        v = cs_value(n, k, a)
        if v is None:
            if n - 1 - a - 2 * (k - 1) < k - 1:
                break
            continue
        if best is None or v > best:
            best, arg = v, [a]
        elif v == best:
            arg.append(a)
    return best, arg


def ub_nonstar(n, k):
    m = k - 1; N = mpf(n - 1)
    Ge = (m + msqrt(m + 1)) ** 2 / (2 * (N + m))
    s2 = msqrt(2)
    cands = [(k - 2) / s2 + msqrt(mpf(2) / 3) + msqrt(mpf(3 * k - 4) / 6)]
    if k >= 3:
        cands.append((k - 3) / s2 + 2 * msqrt(mpf(2) / 3) + msqrt(mpf(3 * k - 5) / 6))
    Sns = min(cands)
    G0 = Sns ** 2 / N
    G = min(Ge, G0) if k >= 3 else Ge
    return mpf(2) ** k * (1 - G / (2 * k)) ** k


def analytic_N1(k):
    """smallest N1 such that for all N >= N1 the explicit construction beats the exp-bound."""
    m = k - 1
    sm = math.sqrt(m)
    K = (m + sm) ** 2
    E = (m / 3 + sm / 11) * K
    s2 = math.sqrt(2)
    cands = [(k - 2) / s2 + math.sqrt(2 / 3) + math.sqrt((3 * k - 4) / 6)]
    if k >= 3:
        cands.append((k - 3) / s2 + 2 * math.sqrt(2 / 3) + math.sqrt((3 * k - 5) / 6))
    Sns = min(cands)
    branches = [((m + math.sqrt(m + 1)) ** 2 / 4, m)]
    if k >= 3:
        branches.append((Sns ** 2 / 2, 0))
    N1 = 0
    for c, s in branches:
        A = c - K / 4
        B = (c * c / 2 + E) + K * s / 4
        C = (c * c / 2 + E) * s
        assert A > 0
        root = (B + math.sqrt(B * B + 4 * A * C)) / (2 * A)
        N1 = max(N1, root)
    # construction validity: y >= 4, y >= sqrt(m) (so a >= 0), floor(y) >= 2
    N1 = max(N1, 4 * (m + sm), sm * (m + sm))
    # safety margin for the floating evaluation of the roots
    return int(math.ceil(N1 * 1.001)) + 1


if __name__ == "__main__":
    for k in [int(x) for x in sys.argv[1:]]:
        N1 = analytic_N1(k)
        fails = []
        for n in range(3 * k - 2, N1 + 2):
            b, arg = cs_best(n, k)
            if b is None or not (mpf(b.numerator) / b.denominator > ub_nonstar(n, k)):
                fails.append(n)
        print(f"k={k}: analytic tail N=n-1 >= {N1};  finite check fails at n = {fails}  (max {max(fails) if fails else None})")
        sys.stdout.flush()
