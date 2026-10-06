"""Rigorous enclosures of the atom values (table tab:bg-atoms) and of the six atom margins of
prop:bg-high, together with g(A_4) < 1/960 (thm:bg-growth / lem:bg-sizeroot benchmark) and
delta_0 - mu_0^2/(4 kappa) > 0.012445 (prop:bg-high).

Everything is computed from the exact definitions at lambda = 1:
    F* = log(621/64)/11,  q = 3/23,  beta = 2F* - log(3/2),  kappa = beta/(1/3 - q)^2,
    gamma = (3/2)(F* - beta),
    h(y) = kappa (y - q)^2 on [0, 1/3],  beta + gamma (y - 1/3) on [1/3, 1],
    atoms: leaf (size 1, T = 1, y = 1), cherry (size 2, T = 3/2, y = 1/3),
           A_j (size 2j+1, T = (3/2)^j alpha_j, y = 3/(4j+3)), alpha_j = 4/3 - 1/(3(j+1)),
    g = size * F* - log T,  sigma = g - h(y),  mu_0 = 23/624 = 1/(24 (1+q)),  delta_0 = 0.01426.
Every quantity is a combination of logarithms of rational numbers; it is enclosed in two independent
ball/interval arithmetics: mpmath.iv (outward rounding, 256 bits) and python-flint arb (300 bits).
Each claim is decided on the endpoints of the enclosure, in both arithmetics. For a printed decimal
x with k digits after the point, "rounds to x" means the enclosure lies in [x - 5*10^-(k+1), x + 5*10^-(k+1)]
(we print k as used in the paper).

Usage: python3 atom_margins.py
"""
import os
import sys
from fractions import Fraction as Fr

os.environ.setdefault("OMP_NUM_THREADS", "1")
from mpmath import iv
from mpmath.libmp import to_rational
import flint
from flint import arb

iv.prec = 256
flint.ctx.prec = 300


class IvBackend:
    name = "mpmath.iv (256 bits)"

    @staticmethod
    def q(fr):
        fr = Fr(fr)
        return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)

    @staticmethod
    def log(x):
        return iv.log(x)

    @staticmethod
    def lohi(x):
        a, b = x._mpi_                 # raw binary endpoints: exact conversion to rationals
        return Fr(*to_rational(a)), Fr(*to_rational(b))


class ArbBackend:
    name = "python-flint arb (300 bits)"

    @staticmethod
    def q(fr):
        fr = Fr(fr)
        return arb(fr.numerator) / arb(fr.denominator)

    @staticmethod
    def log(x):
        return x.log()

    @staticmethod
    def lohi(x):
        lo, hi = x.lower(), x.upper()   # exact binary endpoints (radius 0) of the ball
        return _arb_exact(lo), _arb_exact(hi)


def _arb_exact(x):
    """exact rational value of an exact (radius 0) arb, from its mantissa and exponent."""
    assert x.rad() == 0
    m, e = x.mid().man_exp()
    m, e = int(m), int(e)
    return Fr(m) * (Fr(2) ** e) if e >= 0 else Fr(m, 2 ** (-e))


def compute(B):
    q = Fr(3, 23)
    F = B.log(B.q(Fr(621, 64))) / 11
    beta = 2 * F - B.log(B.q(Fr(3, 2)))
    kappa = beta / B.q((Fr(1, 3) - q) ** 2)
    gamma = B.q(Fr(3, 2)) * (F - beta)

    def h(y):
        y = Fr(y)
        if y <= Fr(1, 3):
            return kappa * B.q((y - q) ** 2)
        return beta + gamma * B.q(y - Fr(1, 3))

    atoms = [("leaf", 1, Fr(1), Fr(1)), ("cherry", 2, Fr(3, 2), Fr(1, 3))]
    for j in range(1, 8):
        alpha = Fr(4, 3) - Fr(1, 3 * (j + 1))
        atoms.append(("A%d" % j, 2 * j + 1, Fr(3, 2) ** j * alpha, Fr(3, 4 * j + 3)))
    vals = {}
    for name, size, T, y in atoms:
        g = size * F - B.log(B.q(T))
        hv = h(y)
        vals[name] = dict(size=size, T=T, y=y, g=g, h=hv, sigma=g - hv)
    return dict(F=F, beta=beta, kappa=kappa, gamma=gamma, q=q, atoms=vals)


FAILS = []


def check(label, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(label)


def fmt(lo, hi, d=12):
    return "[%.*e, %.*e]" % (d, float(lo), d, float(hi))


def rounds_to(B, x, printed, k):
    lo, hi = B.lohi(x)
    half = Fr(5, 10 ** (k + 1))
    p = Fr(printed)
    return (p - half <= lo) and (hi <= p + half), lo, hi


# values printed in table tab:bg-atoms (7 decimals); exact zeros are checked as identities
TABLE3 = {
    "leaf":   ("0.2065862", "0", "0.2065862"),
    "cherry": ("0.0077073", "0", "0.0077073"),
    "A1":     ("0.0361185", "0.0240242", "0.0601428"),
    "A2":     ("0.0037906", "0.0175394", "0.0213300"),
    "A3":     ("0.0009060", "0.0056584", "0.0065644"),
    "A4":     ("0.0001412", "0.0008853", "0.0010264"),
    "A6":     ("0.0000699", "0.0014454", "0.0015153"),
    "A7":     ("0.0002121", "0.0043915", "0.0046036"),
}
# margins g - mu_0 (y - q) in the proof of prop:bg-high, as printed (value, digits after the point)
MARGINS = [("leaf", "0.17453", 5), ("cherry", "0.000229", 6), ("A1", "0.04915", 5),
           ("A2", "0.01609", 5), ("A3", "0.00400", 5), ("A4", "0.0000143", 7)]


def run(B):
    print("=" * 78)
    print("backend:", B.name)
    C = compute(B)
    F, beta, kappa, gamma, q = C["F"], C["beta"], C["kappa"], C["gamma"], C["q"]
    A = C["atoms"]
    for nm, x in (("F*", F), ("beta", beta), ("kappa", kappa), ("gamma", gamma)):
        lo, hi = B.lohi(x)
        print("     %-6s in %s" % (nm, fmt(lo, hi, 15)))

    # exact identities behind the zeros of the table (independent of the arithmetic):
    #   g(leaf) = F* = h(1); g(cherry) = 2F* - log(3/2) = beta = h(1/3); g(A5) = 11F* - log(621/64) = 0, y(A5) = q.
    assert A["A5"]["T"] == Fr(621, 64) and A["A5"]["y"] == q
    check("identities: sigma(leaf) = 0, sigma(cherry) = 0, g(A5) = h(q) = sigma(A5) = 0 (exact, by definition)", True)

    # table 3
    for name, (hp, sp, gp) in TABLE3.items():
        a = A[name]
        okh, hlo, hhi = rounds_to(B, a["h"], hp, 7)
        okg, glo, ghi = rounds_to(B, a["g"], gp, 7)
        if sp == "0":
            oks, slo, shi = True, Fr(0), Fr(0)
        else:
            oks, slo, shi = rounds_to(B, a["sigma"], sp, 7)
        check("table tab:bg-atoms row %-6s y=%-5s h=%s sigma=%s g=%s are the rounded values" % (name, a["y"], hp, sp, gp),
              okh and oks and okg,
              "h in %s, g in %s" % (fmt(hlo, hhi, 9), fmt(glo, ghi, 9)))

    # the six margins of prop:bg-high
    mu0 = Fr(23, 624)
    assert mu0 == 1 / (24 * (1 + q))
    worst = None
    for name, printed, k in MARGINS:
        a = A[name]
        assert a["y"] > q
        m = a["g"] - B.q(mu0 * (a["y"] - q))
        lo, hi = B.lohi(m)
        okr, _, _ = rounds_to(B, m, printed, k)
        check("margin g - mu_0 (y - q) > 0 at %-6s (y - q = %s)" % (name, a["y"] - q), lo > 0,
              "enclosure %s; printed %s: %s" % (fmt(lo, hi, 6), printed, "rounds correctly" if okr else "DOES NOT ROUND"))
        if not okr:
            FAILS.append("rounding of margin " + name)
        if worst is None or lo < worst[1]:
            worst = (name, lo, hi)
    gA4lo, gA4hi = B.lohi(A["A4"]["g"])
    print("     smallest margin at %s; as a fraction of g(A4): [%.5f, %.5f]"
          % (worst[0], float(worst[1] / gA4hi), float(worst[2] / gA4lo)))
    check("y(A4) - q = 12/437", A["A4"]["y"] - q == Fr(12, 437))
    check("mu_0 = 23/624 rounds to 0.0368590", abs(Fr(mu0) - Fr("0.0368590")) <= Fr(5, 10 ** 8))

    # high degree: the minimum of h(y) - mu (y - q) lies on the quadratic piece
    gm = gamma - B.q(mu0)
    lo, hi = B.lohi(gm)
    check("gamma - mu_0 > 0 (slope on the linear piece)", lo > 0, fmt(lo, hi, 6))
    ymin = B.q(q) + B.q(mu0) / (2 * kappa)
    lo, hi = B.lohi(ymin)
    check("q + mu_0/(2 kappa) < 1/3 (printed ~0.229)", hi < Fr(1, 3) and abs((lo + hi) / 2 - Fr("0.229")) < Fr(5, 10 ** 4),
          fmt(lo, hi, 6))
    d0 = Fr("0.01426")
    val = B.q(d0) - B.q(mu0 ** 2) / (4 * kappa)
    lo, hi = B.lohi(val)
    check("delta_0 - mu_0^2/(4 kappa) > 0.012445", lo > Fr("0.012445"), fmt(lo, hi, 9))

    # g(A4) < 1/960 and the benchmark constant
    check("g(A4) < 1/960", gA4hi < Fr(1, 960), "g(A4) in %s, 1/960 = %.10f" % (fmt(gA4lo, gA4hi, 9), 1 / 960))
    bench = B.log(B.q(Fr(26, 23))) - B.q(Fr(10, 960))
    lo, hi = B.lohi(bench)
    check("log(26/23) - 10/960 > 0.11218 (benchmark, lem:bg-sizeroot)", lo > Fr("0.11218"), fmt(lo, hi, 9))
    lo, hi = B.lohi(B.log(B.q(Fr(26, 23))) - B.q(Fr("0.012445")))
    check("log(26/23) - 0.012445 < 0.1101574 (lem:bg-compare (iii))", hi < Fr("0.1101574"), fmt(lo, hi, 9))
    # the deficits quoted in rem:bgx-race (rounded) and cor:bgx-limits (truncated, written with dots)
    for name, rounded, truncated in (("A4", "0.0010264", "0.0010264"), ("A6", "0.0015153", "0.0015152")):
        lo, hi = B.lohi(A[name]["g"])
        okr, _, _ = rounds_to(B, A[name]["g"], rounded, 7)
        okt = Fr(truncated) <= lo and hi < Fr(truncated) + Fr(1, 10 ** 7)
        check("g(%s) ~ %s (rounded) and = %s... (leading digits)" % (name, rounded, truncated), okr and okt,
              fmt(lo, hi, 10))

def main():
    run(IvBackend)
    run(ArbBackend)
    print("=" * 78)
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CHECKS PASSED (both arithmetics)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
