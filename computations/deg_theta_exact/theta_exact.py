"""The exact constants theta of the bounded-degree certificates (lem:deg-cert34, lem:deg-cert567), the
rounding of the values printed in the paper, and an independent enumeration of the rules with an
exact check that the target intervals cover every parent range.

Definitions (Section 9): for 3 <= Delta <= 7, t_Delta is the positive root of
s^2 - (4 Delta - 2)/(3 Delta) s - 1/Delta^2, mu_Delta = (3/2)^(Delta-2) t_Delta, F = log(mu_Delta)/(2 Delta - 3),
eta = 1/(Delta t_Delta), theta_L = F - log(1 + eta), theta_C = 2F - log(3/2) - log(1 + eta/3) and, for
Delta >= 6, theta_{A5} = g(A5) - log(1 + 3 eta/23) with g(A5) = 11 F - log(621/64). Interval types:
Delta = 3, 4: I_Delta and J_Delta with theta_J = theta_C and theta_I = -813/10000 (Delta = 3),
-391/10000 (Delta = 4); Delta = 5, 6, 7: the four-interval partitions and rational theta of the
certificate files ../deg_certificates/certificates/cert_D{5,6,7}_K4.json (there the cherry is called K,
A5 is called C5, the intervals of J_Delta are B0..B3 and those of I_Delta are A0..A3).

Checks:
  [1] theta_L, theta_C, theta_{A5} enclosed in Arb ball arithmetic (300 bits); the values printed in
      lem:deg-cert34 are their roundings to four decimals; for Delta = 6, 7 the definition of theta_{A5}
      makes the identity rule C^5 -> A5 an equality.
  [2] theta_I: the printed -0.0813 and -0.0391 are the exact rationals used by
      ../deg_certificates/explicit_small.py and indep_check.py (read from their source); cert34.py
      uses the double nearest to them (difference printed).
  [3] Delta = 5, 6, 7: the exact theta of every interval type, read from the certificates.
  [4] independent rule enumeration under the typing stated in the paper: the window partitions are
      contiguous with the exact window endpoints; for every multiset of 1..Delta-1 child types the
      exact parent range [1/(m+1+Rmax), 1/(m+1+Rmin)] lies in the window I_Delta (m = 1, non-leaf child)
      or J_Delta (m >= 2), and the targets (identity rules L -> C and C^5 -> A5; otherwise every interval
      type meeting the range) cover it exactly; the numbers of rules are 14, 34, 1116, 4505, 12753.

Usage: python3 theta_exact.py
"""
import itertools
import json
import os
import sys
from fractions import Fraction as Fr

import flint
from flint import arb

flint.ctx.prec = 300
HERE = os.path.dirname(os.path.abspath(__file__))
DEG = os.path.join(HERE, "..", "deg_certificates")
FAILS = []


def check(label, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(label)


def A(fr):
    fr = Fr(fr)
    return arb(fr.numerator) / arb(fr.denominator)


def exact_arb(x):
    m, e = x.mid().man_exp()
    m, e = int(m), int(e)
    return Fr(m) * Fr(2) ** e if e >= 0 else Fr(m, 2 ** (-e))


def lohi(x):
    return exact_arb(x.lower()), exact_arb(x.upper())


def params(D):
    s = arb((2 * D - 1) ** 2 + 9).sqrt()
    t = ((2 * D - 1) + s) / (3 * D)
    mu = (A(Fr(3, 2)) ** (D - 2)) * t
    F = mu.log() / (2 * D - 3)
    eta = 1 / (D * t)
    thL = F - (1 + eta).log()
    thC = 2 * F - A(Fr(3, 2)).log() - (1 + eta / 3).log()
    gA5 = 11 * F - A(Fr(621, 64)).log()
    thA5 = gA5 - (1 + 3 * eta / 23).log()
    return dict(F=F, eta=eta, L=thL, C=thC, A5=thA5)


def rounds4(x, printed):
    lo, hi = lohi(x)
    p = Fr(printed)
    return p - Fr(5, 10 ** 5) <= lo and hi <= p + Fr(5, 10 ** 5)


def dec(x, d=10):
    lo, hi = lohi(x)
    return "%.*f" % (d, float((lo + hi) / 2))


# ------------------------------------------------------------------------------------- [1], [2]
def part12():
    print("[1] theta_L, theta_C (and theta_A5) from their definitions, Arb 300 bits")
    printed = {3: ("-0.0476", "-0.1000"), 4: ("0.0149", "-0.0684")}
    for D in (3, 4, 5, 6, 7):
        p = params(D)
        line = "Delta=%d: F = %s, eta = %s, theta_L = %s, theta_C = %s" % (D, dec(p["F"], 12), dec(p["eta"], 12),
                                                                          dec(p["L"], 12), dec(p["C"], 12))
        if D >= 6:
            line += ", theta_A5 = %s" % dec(p["A5"], 12)
        print("     " + line)
        if D in printed:
            check("Delta=%d: printed theta_L = %s, theta_C = %s are the 4-decimal roundings" % ((D,) + printed[D]),
                  rounds4(p["L"], printed[D][0]) and rounds4(p["C"], printed[D][1]))
        if D >= 6:
            # the identity rule C^5 -> A5 holds with equality: theta_A5 = F + 5 theta_C - B_5(1/3, ..., 1/3)
            third = A(Fr(1, 3))
            B5 = (6 + p["eta"] + 5 * third).log() - arb(6).log() - 5 * (1 + p["eta"] * third).log()
            d = p["F"] + 5 * p["C"] - B5 - p["A5"]
            lo, hi = lohi(d)
            check("Delta=%d: theta_A5 = g(A5) - log(1 + 3 eta/23) equals F + 5 theta_C - B_5(1/3,...,1/3) "
                  "(identity rule C^5 -> A5 exact)" % D, lo <= 0 <= hi and hi - lo < Fr(1, 10 ** 80))
    print("[2] theta_I: the printed values and the values in the programs")
    src_small = open(os.path.join(DEG, "explicit_small.py")).read()
    src_indep = open(os.path.join(DEG, "indep_check.py")).read()
    src_c34 = open(os.path.join(DEG, "cert34.py")).read()
    ok1 = "KA = {3: Fr(-813, 10000), 4: Fr(-391, 10000)}" in src_small
    ok2 = '"-0.0813")' in src_indep and '"-0.0391")' in src_indep and "A(F(kA))" in src_indep
    check("explicit_small.py uses theta_I = -813/10000 (Delta=3), -391/10000 (Delta=4) exactly", ok1)
    check("indep_check.py uses theta_I = Fraction('-0.0813'), Fraction('-0.0391') exactly", ok2)
    ok3 = "check(3, -0.0813)" in src_c34 and "check(4, -0.0391)" in src_c34
    d3 = Fr(-0.0813) - Fr(-813, 10000)
    d4 = Fr(-0.0391) - Fr(-391, 10000)
    check("cert34.py uses the doubles nearest to -0.0813, -0.0391 (they differ from the decimals by %.2e, %.2e)"
          % (float(d3), float(d4)), ok3 and abs(d3) < Fr(1, 10 ** 17) and abs(d4) < Fr(1, 10 ** 17))


# ------------------------------------------------------------------------------------- types
def types_for(D):
    """list of (name, lo, hi, kind) and dict theta (arb) under the paper's typing"""
    p = params(D)
    Iw = (Fr(2, 5), Fr(2 * D - 1, 4 * D - 1))
    Jw = (Fr(1, 2 * D - 1), Fr(2 * D - 1, 6 * D - 1))
    if D in (3, 4):
        thI = Fr(-813, 10000) if D == 3 else Fr(-391, 10000)
        types = [("L", Fr(1), Fr(1), "point"), ("C", Fr(1, 3), Fr(1, 3), "point"),
                 ("I", Iw[0], Iw[1], "I"), ("J", Jw[0], Jw[1], "J")]
        th = {"L": p["L"], "C": p["C"], "I": A(thI), "J": p["C"]}
        exact = {"I": thI}
        return types, th, Iw, Jw, exact
    c = json.load(open(os.path.join(DEG, "certificates", "cert_D%d_K4.json" % D)))
    rename = {"K": "C", "C5": "A5"}
    types = []
    th = {}
    exact = {}
    for name, lo, hi in c["types"]:
        nm = rename.get(name, name)
        lo, hi = Fr(lo), Fr(hi)
        if nm in ("L", "C", "A5"):
            types.append((nm, lo, hi, "point"))
            th[nm] = p[nm]
            assert c["k"][name] == "exact"
        else:
            kind = "J" if hi < Fr(1, 3) else "I"
            types.append((nm, lo, hi, kind))
            exact[nm] = Fr(c["k"][name])
            th[nm] = A(exact[nm])
    return types, th, Iw, Jw, exact


def part3():
    print("[3] exact theta of the interval types, Delta = 5, 6, 7 (from the certificates)")
    for D in (5, 6, 7):
        types, th, Iw, Jw, exact = types_for(D)
        print("     Delta=%d" % D)
        for nm, lo, hi, kind in types:
            if nm in exact:
                print("       %-3s [%s, %s]  theta = %s = %s" % (nm, lo, hi, exact[nm], "%.10f" % float(exact[nm])))
            else:
                print("       %-3s {%s}  theta = (defined by logarithms) %s" % (nm, lo, dec(th[nm], 10)))


# ------------------------------------------------------------------------------------- [4]
def part4():
    print("[4] independent rule enumeration and exact coverage of the parent ranges")
    expected = {3: 14, 4: 34, 5: 1116, 6: 4505, 7: 12753}
    for D in (3, 4, 5, 6, 7):
        types, th, Iw, Jw, exact = types_for(D)
        names = [t[0] for t in types]
        lo = {t[0]: t[1] for t in types}
        hi = {t[0]: t[2] for t in types}
        kind = {t[0]: t[3] for t in types}
        ok = True
        # window partitions: contiguous, exact endpoints
        for win, k in ((Iw, "I"), (Jw, "J")):
            segs = sorted((lo[n], hi[n]) for n in names if kind[n] == k)
            ok &= segs[0][0] == win[0] and segs[-1][1] == win[1]
            ok &= all(segs[i][1] == segs[i + 1][0] for i in range(len(segs) - 1))
            ok &= all(a < b for a, b in segs)
        intervals = [n for n in names if kind[n] != "point"]
        nrules = 0
        bad = []
        for m in range(1, D):
            for ms in itertools.combinations_with_replacement(names, m):
                Rmin = sum(lo[x] for x in ms)
                Rmax = sum(hi[x] for x in ms)
                plo, phi = 1 / (m + 1 + Rmax), 1 / (m + 1 + Rmin)
                if ms == ("L",):
                    targets = ["C"]
                elif "A5" in names and ms == ("C",) * 5:
                    targets = ["A5"]
                else:
                    win = Iw if m == 1 else Jw
                    if not (win[0] <= plo and phi <= win[1]):
                        bad.append(("window", ms))
                    targets = [n for n in intervals if not (hi[n] < plo or lo[n] > phi)]
                    segs = sorted((lo[n], hi[n]) for n in targets)
                    cur = plo
                    for a, b in segs:
                        if a > cur:
                            break
                        cur = max(cur, b)
                    if not segs or segs[0][0] > plo or cur < phi:
                        bad.append(("coverage", ms))
                nrules += len(targets)
        ok &= not bad
        check("Delta=%d: partitions exact and contiguous; every parent range in its window and covered "
              "exactly by its targets; %d rules (paper: %d)" % (D, nrules, expected[D]),
              ok and nrules == expected[D], "problems: %s" % bad[:3] if bad else "")
        if D >= 6:
            ms = ("C", "C", "L", "L")
            plo = 1 / (5 + 2 * Fr(1, 3) + 2)
            tgt = [n for n in intervals if lo[n] <= plo <= hi[n]]
            check("Delta=%d: the branch L L C C has message 3/23 and an interval type (%s), not A5"
                  % (D, ", ".join(tgt)), plo == Fr(3, 23) and len(tgt) >= 1)


def main():
    part12()
    part3()
    part4()
    print("=" * 78)
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
