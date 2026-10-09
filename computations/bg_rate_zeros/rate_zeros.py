"""The two exact zeros of the rate potential at lambda = 1: the one-sided derivatives at (c, S) = (5, 5/3) and
(1, 1), their stated numerical ranges, and the local monotonicity argument near each zero.

Notation: h is the potential at lambda = 1, z(y) = 11 - (621/14)(y - q) on [0, 1/3] and
2 - (3/2)(y - 1/3) on [1/3, 1], h~ = h - eta z, and for c >= 1
    Phi~_c(S) = F* - eta + c h~(S/c) - log(1 + S/(c+1)) - h~(1/(c+1+S)).
For each cap K, eta = eta_K is the certified rational rate (eta_{k-1}, k = K+1).

Checks:
  [A] symbolic (sympy): the one-sided derivatives of Phi~_5 at S = 5/3 are
        D^- = s + (621/14) eta (1 + q^2) - q,     D^+ = gamma + (3/2) eta + (621/14) eta q^2 - q,
      with s = 2 kappa (1/3 - q); and on [1/3, 1] the derivative of Phi~_1 is
      (gamma + 3/2 eta)(1 + r^2) - r with r = 1/(2+S) in [1/3, 3/7], at most (10/9)(gamma + 3/2 eta) - 1/3.
      Also the exact zeros Phi~_1(1) = 0 and Phi~_5(5/3) = 0, from the identities 1 + z(1) = z(1/3),
      1 + 5 z(1/3) = z(q), F* + 5 beta = log(23/18) and 2F* - log(3/2) = beta.
  [B] rigorous enclosures (mpmath.iv, 256 bits, and python-flint arb, 300 bits) of D^-, D^+ and
      (10/9)(gamma + 3/2 eta) - 1/3 for all 22 rates; the stated ranges:
      -0.041 < D^- < -0.004 and D^+ = 0.17 (rounded to two decimals) for every eta_K, and
      (10/9)(gamma + 3/2 eta) - 1/3 < 0 for every eta_K, equal to -7.79e-6 (rounded) for K <= 5;
      the cap eta <= (3/10 - gamma)/(3/2) = 0.0011210...
  [C] the local argument, with 5/3 and 1 as exact rational endpoints: for every K >= 5, an enclosure of
      the derivative of Phi~_5 on [5/3 - 10^-4, 5/3] (the pieces S/c <= 1/3 and r <= 1/3) is <= 0, and
      on [5/3, 5/3 + 10^-4] (pieces S/c >= 1/3 and r <= 1/3) is >= 0; for every K, an enclosure of the
      derivative of Phi~_1 on [1 - 10^-4, 1] (pieces S >= 1/3 and r >= 1/3) is <= 0. Hence
      Phi~_c >= Phi~_c(S_0) = 0 on every box of width at most 10^-4 that contains the zero S_0, which
      is the local step of the branch-and-bound of ../bg_rate/certify.py.

Usage: python3 rate_zeros.py
"""
import json
import os
import sys
from fractions import Fraction as Fr

os.environ.setdefault("OMP_NUM_THREADS", "1")
import sympy as sp
from mpmath import iv
from mpmath.libmp import to_rational
import flint
from flint import arb

iv.prec = 256
flint.ctx.prec = 300
HERE = os.path.dirname(os.path.abspath(__file__))

# the certified rates eta_{k-1}, as stated, indexed by the cap K = k - 1
ETA = {1: "2791/2500000", 2: "2791/2500000", 3: "2791/2500000", 4: "2791/2500000", 5: "2791/2500000",
       6: "9387/10000000", 7: "4183/5000000", 8: "7507/10000000", 9: "1701/2500000", 10: "311/500000",
       11: "179/312500", 12: "5309/10000000", 13: "2473/5000000", 14: "463/1000000", 15: "34/78125",
       16: "2053/5000000", 17: "1943/5000000", 18: "461/1250000", 19: "351/1000000", 20: "837/2500000",
       21: "1/3125", 22: "613/2000000"}
ETA = {K: Fr(v) for K, v in ETA.items()}
FAILS = []


def check(label, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(label)


# ---------------------------------------------------------------------------------- [A] symbolic
def symbolic():
    print("[A] symbolic derivation (sympy)")
    S, eta = sp.symbols("S eta")
    L621, L64, L3, L2, L23 = sp.symbols("L621 L64 L3 L2 L23")   # placeholders for logs
    q = sp.Rational(3, 23)
    third = sp.Rational(1, 3)
    F = (sp.log(sp.Integer(621)) - sp.log(sp.Integer(64))) / 11
    beta = 2 * F - sp.log(sp.Rational(3, 2))
    kappa = beta / (third - q) ** 2
    gamma = sp.Rational(3, 2) * (F - beta)
    s_tan = 2 * kappa * (third - q)

    def zQ(y):
        return 11 - sp.Rational(621, 14) * (y - q)

    def zL(y):
        return 2 - sp.Rational(3, 2) * (y - third)

    def hQ(y):
        return kappa * (y - q) ** 2 - eta * zQ(y)

    def hL(y):
        return beta + gamma * (y - third) - eta * zL(y)

    def Phi(c, hy, hr):
        r = 1 / (c + 1 + S)
        return F - eta + c * hy(S / c) - sp.log(1 + S / (c + 1)) - hr(r)

    P5L = Phi(5, hQ, hQ)
    P5R = Phi(5, hL, hQ)
    Dm = sp.diff(P5L, S).subs(S, sp.Rational(5, 3))
    Dp = sp.diff(P5R, S).subs(S, sp.Rational(5, 3))
    Dm_claim = s_tan + sp.Rational(621, 14) * eta * (1 + q ** 2) - q
    Dp_claim = gamma + sp.Rational(3, 2) * eta + sp.Rational(621, 14) * eta * q ** 2 - q
    check("D^- = s + (621/14) eta (1+q^2) - q", sp.simplify(sp.expand(Dm - Dm_claim)) == 0)
    check("D^+ = gamma + (3/2) eta + (621/14) eta q^2 - q", sp.simplify(sp.expand(Dp - Dp_claim)) == 0)
    # values at the zeros; logs expanded into log 2, log 3, log 23
    v5 = sp.expand_log(sp.expand(P5L.subs(S, sp.Rational(5, 3))), force=True)
    v5r = sp.expand_log(sp.expand(P5R.subs(S, sp.Rational(5, 3))), force=True)
    P1 = Phi(1, hL, hL)
    v1 = sp.expand_log(sp.expand(P1.subs(S, 1)), force=True)
    check("Phi~_5(5/3) = 0 exactly (both pieces agree there), for every eta",
          sp.simplify(v5) == 0 and sp.simplify(v5r) == 0)
    check("Phi~_1(1) = 0 exactly, for every eta", sp.simplify(v1) == 0)
    check("1 + z(1) = z(1/3) and 1 + 5 z(1/3) = z(q)", 1 + zL(1) == zL(third) and 1 + 5 * zL(third) == zQ(q))
    # c = 1 on [1/3, 1]: derivative = (gamma + 3/2 eta)(1 + r^2) - r, r = 1/(2+S)
    d1 = sp.diff(P1, S)
    r = 1 / (2 + S)
    check("Phi~_1'(S) = (gamma + 3/2 eta)(1 + r^2) - r on [1/3, 1]",
          sp.simplify(d1 - ((gamma + sp.Rational(3, 2) * eta) * (1 + r ** 2) - r)) == 0)
    # (gamma + 3/2 eta)(1 + r^2) - r decreases in r on [1/3, 3/7] as 2 (gamma + 3/2 eta) r < 1 there;
    # its value at r = 1/3 is (10/9)(gamma + 3/2 eta) - 1/3 (checked numerically in [B]).
    return float(gamma.evalf(30))


# ---------------------------------------------------------------------------------- [B], [C] numerics
class Iv:
    name = "mpmath.iv (256 bits)"

    @staticmethod
    def q(fr):
        fr = Fr(fr)
        return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)

    @staticmethod
    def log(x):
        return iv.log(x)

    @staticmethod
    def hull(lo, hi):
        return iv.mpf([lo.a, hi.b])

    @staticmethod
    def lohi(x):
        a, b = x._mpi_
        return Fr(*to_rational(a)), Fr(*to_rational(b))


def _arb_exact(x):
    m, e = x.mid().man_exp()
    m, e = int(m), int(e)
    return Fr(m) * Fr(2) ** e if e >= 0 else Fr(m, 2 ** (-e))


class Ab:
    name = "python-flint arb (300 bits)"

    @staticmethod
    def q(fr):
        fr = Fr(fr)
        return arb(fr.numerator) / arb(fr.denominator)

    @staticmethod
    def log(x):
        return x.log()

    @staticmethod
    def hull(lo, hi):
        return lo.union(hi)

    @staticmethod
    def lohi(x):
        return _arb_exact(x.lower()), _arb_exact(x.upper())


def constants(B):
    F = B.log(B.q(Fr(621, 64))) / 11
    beta = 2 * F - B.log(B.q(Fr(3, 2)))
    q = Fr(3, 23)
    kappa = beta / B.q((Fr(1, 3) - q) ** 2)
    gamma = B.q(Fr(3, 2)) * (F - beta)
    s_tan = 2 * kappa * B.q(Fr(1, 3) - q)
    return F, beta, kappa, gamma, s_tan, q


def deriv5(B, kappa, gamma, eta, q, Sbox, side):
    """enclosure of Phi~_5'(S) on the box Sbox, with the piece of h~ at S/5 fixed by `side`
    ('left': S/5 <= 1/3, 'right': S/5 >= 1/3); r = 1/(6+S) is on the piece r <= 1/3."""
    E = B.q(eta)
    A = B.q(Fr(621, 14))
    Q = B.q(q)
    r = 1 / (6 + Sbox)
    hy = (2 * kappa * (Sbox / 5 - Q) + E * A) if side == "left" else (gamma + E * B.q(Fr(3, 2)))
    hr = 2 * kappa * (r - Q) + E * A
    return hy - r + hr * r * r


def deriv1(B, gamma, eta, Sbox):
    """enclosure of Phi~_1'(S) on Sbox within [1/3, 1]: both S and r = 1/(2+S) on the linear piece."""
    r = 1 / (2 + Sbox)
    a = gamma + B.q(eta) * B.q(Fr(3, 2))
    return a * (1 + r * r) - r


def box(B, lo, hi):
    return B.hull(B.q(lo), B.q(hi))


def sub_max(B, f, lo, hi, n=64):
    """upper bound of f over [lo, hi] (exact rational endpoints) by n sub-boxes"""
    best = None
    for i in range(n):
        a = lo + (hi - lo) * i / n
        b = lo + (hi - lo) * (i + 1) / n
        v = B.lohi(f(box(B, a, b)))[1]
        best = v if best is None or v > best else best
    return best


def sub_min(B, f, lo, hi, n=64):
    best = None
    for i in range(n):
        a = lo + (hi - lo) * i / n
        b = lo + (hi - lo) * (i + 1) / n
        v = B.lohi(f(box(B, a, b)))[0]
        best = v if best is None or v < best else best
    return best


def numerics(B):
    print("=" * 78)
    print("[B], [C] backend:", B.name)
    F, beta, kappa, gamma, s_tan, q = constants(B)
    W = Fr(1, 10 ** 4)
    S0 = Fr(5, 3)
    allDm, allDp = [], []
    print("   K  eta_K           D^- enclosure (lo, hi)              D^+ enclosure (lo, hi)              (10/9)(g+1.5eta)-1/3 (lo, hi)")
    for K in range(1, 23):
        eta = ETA[K]
        E = B.q(eta)
        Dm = s_tan + B.q(Fr(621, 14)) * E * B.q(1 + q * q) - B.q(q)
        Dp = gamma + B.q(Fr(3, 2)) * E + B.q(Fr(621, 14)) * E * B.q(q * q) - B.q(q)
        d11 = B.q(Fr(10, 9)) * (gamma + B.q(Fr(3, 2)) * E) - B.q(Fr(1, 3))
        dm, dp, dd = B.lohi(Dm), B.lohi(Dp), B.lohi(d11)
        allDm.append(dm)
        allDp.append(dp)
        print("  %2d  %-14s  [%+.6e, %+.6e]  [%+.6e, %+.6e]  [%+.6e, %+.6e]"
              % (K, eta, dm[0], dm[1], dp[0], dp[1], dd[0], dd[1]))
        if dd[1] >= 0:
            FAILS.append("(1,1) derivative bound not negative at K=%d" % K)
        if K <= 5:
            if not (Fr("-7.795e-6") <= dd[0] and dd[1] <= Fr("-7.785e-6")):
                FAILS.append("(1,1) value at K=%d does not round to -7.79e-6" % K)
        # [C] local monotonicity with exact endpoints
        if K >= 5:
            left = sub_max(B, lambda X: deriv5(B, kappa, gamma, eta, q, X, "left"), S0 - W, S0)
            right = sub_min(B, lambda X: deriv5(B, kappa, gamma, eta, q, X, "right"), S0, S0 + W)
            if not (left <= 0 and right >= 0):
                FAILS.append("local argument at (5,5/3) fails for K=%d" % K)
        lft1 = sub_max(B, lambda X: deriv1(B, gamma, eta, X), 1 - W, Fr(1))
        if not lft1 <= 0:
            FAILS.append("local argument at (1,1) fails for K=%d" % K)
    mn_lo = min(d[0] for d in allDm)
    mx_hi = max(d[1] for d in allDm)
    check("-0.041 < D^- < -0.004 for all 22 rates", mn_lo > Fr("-0.041") and mx_hi < Fr("-0.004"),
          "D^- ranges over [%.6f, %.6f]" % (mn_lo, mx_hi))
    p_lo = min(d[0] for d in allDp)
    p_hi = max(d[1] for d in allDp)
    check("D^+ rounds to 0.17 for all 22 rates", p_lo >= Fr("0.165") and p_hi < Fr("0.175"),
          "D^+ ranges over [%.6f, %.6f]" % (p_lo, p_hi))
    check("(10/9)(gamma + 3/2 eta_K) - 1/3 < 0 for every K, and rounds to -7.79e-6 for K <= 5",
          not any(f.startswith("(1,1)") for f in FAILS))
    cap = (B.q(Fr(3, 10)) - gamma) / B.q(Fr(3, 2))
    clo, chi = B.lohi(cap)
    check("eta cap (3/10 - gamma)/(3/2) = 0.0011210... and 2791/2500000 below it",
          Fr("0.0011210") <= clo and chi < Fr("0.0011211") and Fr(2791, 2500000) < clo, "[%.10f, %.10f]" % (clo, chi))
    check("local argument at (5, 5/3), K = 5..22: derivative <= 0 on [5/3 - 1e-4, 5/3], >= 0 on [5/3, 5/3 + 1e-4]",
          not any(f.startswith("local argument at (5") for f in FAILS))
    check("local argument at (1, 1), K = 1..22: derivative <= 0 on [1 - 1e-4, 1]",
          not any(f.startswith("local argument at (1") for f in FAILS))


def compare_with_certify():
    path = os.path.join(HERE, "..", "bg_rate", "certify_out.json")
    if not os.path.exists(path):
        print("(../bg_rate/certify_out.json not found; comparison with the certified rates skipped)")
        return
    etas = {int(k): Fr(v) for k, v in json.load(open(path))["etas"].items()}
    check("the 22 rates used here equal those certified by ../bg_rate/certify.py (certify_out.json)", etas == ETA)


def main():
    symbolic()
    compare_with_certify()
    numerics(Iv)
    numerics(Ab)
    print("=" * 78)
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
