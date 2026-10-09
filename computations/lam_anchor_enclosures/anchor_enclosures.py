"""Every numerical constant in the hand proof of the anchor (lambda_c = 1 + sqrt 5), enclosed
rigorously, and the exact identities it uses.

Setting (the weighted family pi_lambda): lambda_c = 1 + sqrt5 = 2 phi, phi = (1 + sqrt5)/2, f* = log phi,
y_C = 1/(2 + lambda_c) (the cherry message), kappa = phi log phi, the hinge h(y) = kappa (y - y_C)_+ on
[0, 1/2], and for a vertex of type (0, m) with pooled child message ybar,
    B_{0,m}(ybar) = log phi + m kappa (ybar - y_C)_+ - log(1 + lambda_c m ybar/(m+1)) - kappa (y_v - y_C)_+,
    y_v = 1/(m + 1 + lambda_c m ybar).

Checks:
  [A] exact identities (sympy): the identities of the anchor, 2 phi^-2 = 3 - sqrt5,
      h(1/2) = f*/2, y_v(y_C) = phi^-2 and y_v(1/2) = 1/(2+phi) for m = 1,
      1 + lambda_c m y_C/(m+1) = (m phi + 1)/(m+1), m phi + 1 > 2 phi^2 for m >= 3, the kink positions
      ybar_m = (1/y_C - (m+1))/(lambda_c m) of y_v = y_C, the form of B_{0,1} in D = 2 + lambda_c ybar and
      its second derivative (D - 2 kappa)/D^3.
  [B] every decimal enclosure of the anchor and of its proof, in mpmath.iv (256 bits) and python-flint
      arb (300 bits), decided on interval endpoints: the enclosures of log phi, kappa, 2 phi^-2;
      h(1) > 0.62 and f* < 0.49; the k = 2 bound; kappa < 2 and kappa - 2 phi^-2 > 0.0146; the kink
      placements for m = 1..4 and m >= 5; the m = 2 minimum and its two terms; the roots y_-, y_+, the
      points 1/(2+phi), phi^-2, ybar*; the convexity condition 2 > 2 kappa; at p = 216/625:
      B_{0,1}(p) in [0.056447, 0.056448], B_{0,1}'(p) in [-1.3e-5, 0], both hinges active,
      p - y_C < 0.155 and 1/2 - p < 0.155, and the tangent bound 0.056447 - 0.155 * 1.3e-5 > 0.05644.
  [C] a direct confirmation that min B_{0,1} over [0, 1/2] exceeds 0.05644: an interval
      branch-and-bound of B_{0,1} on [0, 1/2] (both arithmetics).

Usage: python3 anchor_enclosures.py
"""
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
FAILS = []


def check(label, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(label)


# ------------------------------------------------------------------------------------------ [A]
def exact_identities():
    print("[A] exact identities (sympy)")
    s5 = sp.sqrt(5)
    phi = (1 + s5) / 2
    lam = 1 + s5
    yC = 1 / (2 + lam)
    t = lam / (2 + lam)
    z = lambda e: sp.simplify(sp.radsimp(e)) == 0
    check("lambda_c = 2 phi, 1 + lambda_c/2 = phi^2, 1 + lambda_c = phi^3, 2 phi + 1 = phi^3",
          z(lam - 2 * phi) and z(1 + lam / 2 - phi ** 2) and z(1 + lam - phi ** 3) and z(2 * phi + 1 - phi ** 3))
    check("y_C = 1/(2 phi^2), lambda_c y_C = t = 1/phi, 1 + lambda_c y_C = phi, 1/2 - y_C = 1/(2 phi)",
          z(yC - 1 / (2 * phi ** 2)) and z(lam * yC - t) and z(t - 1 / phi) and z(1 + lam * yC - phi)
          and z(sp.Rational(1, 2) - yC - 1 / (2 * phi)))
    check("2 phi^-2 = 3 - sqrt5", z(2 / phi ** 2 - (3 - s5)))
    L = sp.log(phi)
    kap = phi * L
    check("h(1/2) = kappa (1/2 - y_C) = f*/2", z(sp.expand(kap * (sp.Rational(1, 2) - yC) - L / 2)))
    check("f_cherry = (1/2) log(phi^2) = log phi and cherry deficit 2 log phi - log phi^2 = 0",
          sp.simplify(sp.expand_log(sp.log(phi ** 2) / 2 - L, force=True)) == 0)
    yb = sp.symbols("ybar")
    m = sp.symbols("m", positive=True)
    yv1 = 1 / (2 + lam * yb)
    check("m = 1: y_v(y_C) = phi^-2 and y_v(1/2) = 1/(2+phi)",
          z(yv1.subs(yb, yC) - 1 / phi ** 2) and z(yv1.subs(yb, sp.Rational(1, 2)) - 1 / (2 + phi)))
    check("1 + lambda_c m y_C/(m+1) = (m phi + 1)/(m+1) and y_v(y_C) = 1/(m phi + 1)",
          z(sp.together(1 + lam * m * yC / (m + 1) - (m * phi + 1) / (m + 1)))
          and z(sp.together(1 / (m + 1 + lam * m * yC) - 1 / (m * phi + 1))))
    check("m phi + 1 > 2 phi^2 for m >= 3 (as (m - 2) phi > 1)",
          z(2 * phi ** 2 - (2 * phi + 2)) and bool(phi > 1))
    kinks = {}
    for mm in range(1, 9):
        kinks[mm] = sp.nsimplify((1 / yC - (mm + 1)) / (lam * mm))
    print("     kink of y_v = y_C at ybar_m = (1 + lambda_c - m)/(lambda_c m):",
          ", ".join("m=%d: %.6f" % (mm, float(kinks[mm])) for mm in kinks))
    D = sp.symbols("D", positive=True)
    kk = sp.symbols("kappa", positive=True)
    ybarD = (D - 2) / lam
    B = L + kk * (ybarD - yC) - sp.log(1 + lam * ybarD / 2) - kk * (1 / (2 + lam * ybarD) - yC)
    Bform = L + kk * (D - 2) / lam - sp.log(D / 2) - kk / D
    check("B_{0,1} on [y_C, 1/2] = log phi + kappa (D-2)/lambda_c - log(D/2) - kappa/D, D = 2 + lambda_c ybar",
          sp.simplify(sp.expand(B - Bform)) == 0)
    check("d^2 B_{0,1}/dD^2 = (D - 2 kappa)/D^3", sp.simplify(sp.diff(Bform, D, 2) - (D - 2 * kk) / D ** 3) == 0)
    yv = sp.symbols("y_v", positive=True)
    der = kk - lam * yv + kk * lam * yv ** 2
    check("B_{0,1}'(ybar) = kappa - lambda_c y_v + kappa lambda_c y_v^2 = lambda_c (kappa y_v^2 - y_v + kappa/lambda_c)",
          sp.simplify(der - lam * (kk * yv ** 2 - yv + kk / lam)) == 0)
    return kinks


# ------------------------------------------------------------------------------------------ [B], [C]
class Iv:
    name = "mpmath.iv (256 bits)"
    q = staticmethod(lambda fr: iv.mpf(Fr(fr).numerator) / iv.mpf(Fr(fr).denominator))
    sqrt = staticmethod(lambda x: iv.sqrt(x))
    log = staticmethod(lambda x: iv.log(x))
    hull = staticmethod(lambda a, b: iv.mpf([a.a, b.b]))

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
    q = staticmethod(lambda fr: arb(Fr(fr).numerator) / arb(Fr(fr).denominator))
    sqrt = staticmethod(lambda x: x.sqrt())
    log = staticmethod(lambda x: x.log())
    hull = staticmethod(lambda a, b: a.union(b))

    @staticmethod
    def lohi(x):
        return _arb_exact(x.lower()), _arb_exact(x.upper())


def inside(B, x, lo, hi):
    a, b = B.lohi(x)
    return Fr(lo) <= a and b <= Fr(hi), a, b


def show(a, b):
    return "[%.10f, %.10f]" % (a, b)


def numerics(B, kinks):
    print("=" * 78)
    print("[B] backend:", B.name)
    s5 = B.sqrt(B.q(5))
    phi = (1 + s5) / 2
    lam = 1 + s5
    L = B.log(phi)
    kap = phi * L
    yC = 1 / (2 + lam)

    def chk(label, x, lo, hi):
        ok, a, b = inside(B, x, lo, hi)
        check("%s in [%s, %s]" % (label, lo, hi), ok, show(a, b))
        return a, b

    chk("log phi", L, "0.48121", "0.48122")
    chk("kappa = phi log phi", kap, "0.77861", "0.77862")
    chk("2 phi^-2", 2 / phi ** 2, "0.76393", "0.76394")
    chk("3 - sqrt5", 3 - s5, "0.76393", "0.76394")
    a, _ = B.lohi(kap * (1 - yC))
    check("h(1) = kappa (1 - y_C) > 0.62", a > Fr("0.62"), "%.6f" % a)
    _, b = B.lohi(L)
    check("f* = log phi < 0.49", b < Fr("0.49"))
    chk("k = 2: log(phi^3/(1 + (2/3) lambda_c))", B.log(phi ** 3 / (1 + 2 * lam / 3)), "0.29389", "0.29390")
    _, b = B.lohi(kap)
    check("kappa < 2 (and kappa < 1, used for D >= 2 > 2 kappa)", b < 1)
    a, b = B.lohi(kap - 2 / phi ** 2)
    check("kappa - 2 phi^-2 > 0.0146", a > Fr("0.0146"), show(a, b))
    # the same from the printed enclosures, as in the text: 0.77861 - 0.76394
    check("from the printed enclosures: 0.77861 - 0.76394 > 0.0146", Fr("0.77861") - Fr("0.76394") > Fr("0.0146"))
    # kink placement
    ylo, yhi = B.lohi(yC)
    ok = True
    for mm in range(1, 9):
        kx = (1 / yC - (mm + 1)) / (lam * mm)
        a, b = B.lohi(kx)
        if mm == 1:
            ok &= a > Fr(1, 2)
        elif mm == 2:
            ok &= a > yhi and b < Fr(1, 2)
        elif mm in (3, 4):
            ok &= a > 0 and b < ylo
        else:
            ok &= b < 0
    a, b = B.lohi(1 + lam)
    check("kinks y_v = y_C: m = 2 in (y_C, 1/2), m = 3, 4 in (0, y_C), m = 1 above 1/2, m = 5..8 negative; "
          "and for all m >= 5 negative since m > 1 + lambda_c", ok and b < 5, "1 + lambda_c in " + show(a, b))
    # m = 2
    t1 = B.log(3 / phi ** 2)
    t2 = kap * (phi ** -3 - phi ** -2 / 2)
    chk("log(3 phi^-2)", t1, "0.13618", "0.13619")
    chk("kappa (phi^-3 - phi^-2/2)", t2, "0.03510", "0.03511")
    chk("m = 2 minimum log(3 phi^-2) - kappa(phi^-3 - phi^-2/2)", t1 - t2, "0.10107", "0.10109")
    m2 = B.log(3 * phi / (2 * phi + 1)) - kap * (1 / (2 * phi + 1) - yC)
    chk("m = 2 minimum from the general formula at the kink", m2, "0.10107", "0.10109")
    a, _ = B.lohi(1 / (2 * phi + 1) - yC)
    check("m = 2: 1/(2 phi + 1) = phi^-3 > y_C (hinge active)", a > 0)
    # m = 1
    disc = B.sqrt(1 - 4 * kap ** 2 / lam)
    ym = (1 - disc) / (2 * kap)
    yp = (1 + disc) / (2 * kap)
    yml, ymh = chk("y_-", ym, "0.32067", "0.32068")
    ypl, yph = chk("y_+", yp, "0.96365", "0.96366")
    al, ah = chk("1/(2 + phi)", 1 / (2 + phi), "0.27639", "0.27640")
    bl, bh = chk("phi^-2", phi ** -2, "0.38196", "0.38197")
    check("1/(2+phi) < y_- < phi^-2 < y_+", ah < yml and ymh < bl and bh < ypl)
    ys = (1 / ym - 2) / lam
    chk("ybar* = (1/y_- - 2)/lambda_c", ys, "0.34562", "0.34563")
    p = Fr(216, 625)
    P = B.q(p)
    yv = 1 / (2 + lam * P)
    a, _ = B.lohi(yv - yC)
    pl, ph = B.lohi(P - yC)
    check("p = 216/625: p > y_C and y_v(p) > y_C (both hinges active)", pl > 0 and a > 0)
    Bp = L + kap * (P - yC) - B.log(1 + lam * P / 2) - kap * (yv - yC)
    dBp = kap - lam * yv + kap * lam * yv ** 2
    bpl, bph = chk("B_{0,1}(216/625)", Bp, "0.056447", "0.056448")
    dl, dh = chk("B_{0,1}'(216/625)", dBp, "-0.000013", "0")
    check("p - y_C < 0.155 and 1/2 - p < 0.155", ph < Fr("0.155") and Fr(1, 2) - p < Fr("0.155"),
          "p - y_C <= %.6f, 1/2 - p = %.6f" % (ph, Fr(1, 2) - p))
    tangent = Fr("0.056447") - Fr("0.155") * Fr("0.000013")
    check("tangent bound 0.056447 - 0.155 * 1.3e-5 > 0.05644", tangent > Fr("0.05644"), "%.9f" % tangent)
    # the tangent bound from the enclosures themselves (stronger than the printed one)
    lowest = bpl - max(Fr("0.155"), Fr(0)) * (-dl)
    check("tangent bound from the enclosures > 0.05644", lowest > Fr("0.05644"), "%.9f" % lowest)
    return dict(phi=phi, lam=lam, L=L, kap=kap, yC=yC)


def b01_box(B, c, lo, hi):
    """enclosure of B_{0,1} on [lo, hi] (rational endpoints), with the hinges split exactly at their kinks"""
    phi, lam, L, kap, yC = c["phi"], c["lam"], c["L"], c["kap"], c["yC"]
    X = B.hull(B.q(lo), B.q(hi))
    yv = 1 / (2 + lam * X)
    a1 = kap * (X - yC)
    a2 = kap * (yv - yC)
    # (x)_+ for an interval: lower end max(0, lo), upper end max(0, hi)
    def pos(v):
        lo_, hi_ = B.lohi(v)
        if lo_ >= 0:
            return v
        if hi_ <= 0:
            return B.q(0)
        return B.hull(B.q(0), v)          # [0, hi]
    return L + pos(a1) - B.log(1 + lam * X / 2) - pos(a2)


def bb_min(B, c, lo, hi, target, depth=0):
    v = b01_box(B, c, lo, hi)
    if B.lohi(v)[0] > target:
        return True
    if depth > 40:
        return False
    mid = (lo + hi) / 2
    return bb_min(B, c, lo, mid, target, depth + 1) and bb_min(B, c, mid, hi, target, depth + 1)


def main():
    kinks = exact_identities()
    for Bk in (Iv, Ab):
        c = numerics(Bk, kinks)
        ok = bb_min(Bk, c, Fr(0), Fr(1, 2), Fr("0.05644"))
        check("[C] (%s) branch-and-bound: B_{0,1} > 0.05644 on [0, 1/2]" % Bk.name, ok)
    print("=" * 78)
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
