"""Exact check of the exchange polynomials of the local exchanges (M1)-(M7): the 15-row table (exchanges (M7)(ii), (iii)
and the 13 exchanges of (M7)(vi)), the positive factors listed in the proof, and the corner
polynomials of (M3).

Exchange criterion: replacing the old branches O by new branches N at a vertex whose
other D_0 branches have message sum R_0 changes pi by a positive multiple of
    E(D_0, R_0) = P_N (m_N + D_0 + R_N + R_0)(m_O + D_0) - P_O (m_O + D_0 + R_O + R_0)(m_N + D_0).
The weights T and messages y of all branches are computed here from the cavity recursion
(a root with children b_1..b_c has degree d = c + 1, T = (prod T_i)(d + R)/d, y = 1/(d + R),
R = sum y_i), not from closed forms, so the check is independent of the formulas in the text.

[A] the 15-row exchange table: for each of the 15 rows, E is affine in R_0 and of degree 2 in D_0; there is one
    positive rational c with E(D_0, 0) = c * (column 1) and 2 E(D_0, (D_0+1)/2) = c * (column 2) as
    polynomials; and both columns are positive for every integer D_0 >= 1 (after D_0 = 1 + t all
    coefficients are >= 0 and the constant term is > 0). Since E is affine in R_0, this gives E > 0 on
    0 <= R_0 <= (D_0+1)/2, which contains the admissible range when the rest has at most one leaf.
[B] the factors of the other exchanges: E = factor * (displayed polynomial) for (M1), (M2), (M5),
    (M6) (D_0 = 1, j = 5..12), (M7)(i) (i = 0..10), (M7)(iv) (j = 2, 3, 4, symbolic i), (M7)(v)
    (j = 1..4), and (M4) (balance; several i, j); the stalk values T(P_4) = 17/8, y(P_4) = 7/17,
    T(P_5) = 41/16, y(P_5) = 17/41.
[C] (M3): with P_O = (m+1+S)/(m+1), R_O = 1 + 1/(m+1+S), P_N = 3/2, R_N = S + 1/3, m_O = 2,
    m_N = m + 1, the displayed expression equals 2 (m+1) E, and its values at the eight corners are the
    displayed polynomials in t = D_0 - 1 and M = m - 2 (or m = 1), with nonnegative coefficients.

Usage: python3 m7_table.py
"""
import sys
from fractions import Fraction as Fr

import sympy as sp

D, R, t, I, M, S, i_ = sp.symbols("D0 R0 t I M S i")
FAILS = []


def check(label, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(label)


# ------------------------------------------------------------------ branches by the recursion
LEAF = ()


def br(*ch):
    return tuple(ch)


def Ty(b):
    """(T, y) of a planted branch given as nested tuples of children (leaf = empty tuple)."""
    if b == LEAF:
        return sp.Integer(1), sp.Integer(1)
    d = len(b) + 1
    P = sp.Integer(1)
    Rs = sp.Integer(0)
    for c in b:
        T, y = Ty(c)
        P *= T
        Rs += y
    return sp.nsimplify(P * (d + Rs) / d), sp.nsimplify(1 / (d + Rs))


def size(b):
    return 1 + sum(size(c) for c in b)


C = br(LEAF)


def Arm(j):
    return LEAF if j == 0 else br(*([C] * j))


def stalk(X):
    return br(X)


P4 = stalk(Arm(1))
P5 = stalk(P4)


def E(O, N):
    assert sum(size(b) for b in O) == sum(size(b) for b in N), (O, N)
    PO = sp.prod([Ty(b)[0] for b in O])
    PN = sp.prod([Ty(b)[0] for b in N])
    RO = sum(Ty(b)[1] for b in O)
    RN = sum(Ty(b)[1] for b in N)
    mO, mN = len(O), len(N)
    return sp.expand(PN * (mN + D + RN + R) * (mO + D) - PO * (mO + D + RO + R) * (mN + D))


def nonneg_shift(poly):
    """coefficients of poly(D0 = 1 + t) as a polynomial in t: all >= 0 and constant > 0"""
    p = sp.Poly(sp.expand(poly.subs(D, 1 + t)), t)
    co = p.all_coeffs()
    return all(c >= 0 for c in co) and p.eval(0) > 0, sp.expand(poly.subs(D, 1 + t))


# ------------------------------------------------------------------ [A] the 15-row exchange table
TABLE = [
    ("(ii)  {P4, C} -> {C^3}", [P4, C], [C, C, C], 3 * D**2 + 31 * D + 12, (D + 3) * (9 * D - 7)),
    ("(iii) {P4, P4} -> {C^4}", [P4, P4], [C] * 4, 35 * D**2 + 404 * D + 192, 105 * D**2 + 335 * D - 124),
    ("{[A2], C} -> {A1, A2}", [stalk(Arm(2)), C], [Arm(1), Arm(2)], D**2 + 2 * D, (D + 2) * (3 * D + 1)),
    ("{[A3], C} -> {A1, A3}", [stalk(Arm(3)), C], [Arm(1), Arm(3)], D**2 + 2 * D, (D + 2) * (3 * D + 1)),
    ("{[A4], C} -> {C, A2, A2}", [stalk(Arm(4)), C], [C, Arm(2), Arm(2)], 309 * D**2 + 2089 * D + 296,
     927 * D**2 + 1784 * D - 2111),
    ("{[A1], [A1]} -> N11 = C^4", [stalk(Arm(1))] * 2, [C] * 4, 35 * D**2 + 404 * D + 192,
     105 * D**2 + 335 * D - 124),
    ("{[A2], [A1]} -> N21 = C^5", [stalk(Arm(2)), stalk(Arm(1))], [C] * 5, 61 * D**2 + 875 * D + 420,
     183 * D**2 + 658 * D - 313),
    ("{[A2], [A2]} -> N22 = C^6", [stalk(Arm(2))] * 2, [C] * 6, 26 * D**2 + 435 * D + 216,
     78 * D**2 + 323 * D - 141),
    ("{[A3], [A1]} -> N31 = C^6", [stalk(Arm(3)), stalk(Arm(1))], [C] * 6, 29 * D**2 + 502 * D + 240,
     87 * D**2 + 343 * D - 210),
    ("{[A4], [A1]} -> N41 = C^7", [stalk(Arm(4)), stalk(Arm(1))], [C] * 7, 113 * D**2 + 2297 * D + 1092,
     339 * D**2 + 1448 * D - 1075),
    ("{[A3], [A2]} -> N32 = {L, A6}", [stalk(Arm(3)), stalk(Arm(2))], [LEAF, Arm(6)],
     19 * D**2 + 514 * D + 952, (D + 2) * (57 * D + 971)),
    ("{[A3], [A3]} -> N33 = {L, C, A6}", [stalk(Arm(3))] * 2, [LEAF, C, Arm(6)], 17 * D**2 + 563 * D + 288,
     3 * (17 * D**2 + 110 * D - 79)),
    ("{[A4], [A2]} -> N42 = {L, C, A6}", [stalk(Arm(4)), stalk(Arm(2))], [LEAF, C, Arm(6)],
     115 * D**2 + 4623 * D + 2304, 345 * D**2 + 2416 * D - 2337),
    ("{[A4], [A3]} -> N43 = {L, C, A7}", [stalk(Arm(4)), stalk(Arm(3))], [LEAF, C, Arm(7)],
     14 * D**2 + 321 * D + 172, 42 * D**2 + 233 * D - 79),
    ("{[A4], [A4]} -> N44 = {L, C, A8}", [stalk(Arm(4))] * 2, [LEAF, C, Arm(8)], 207 * D**2 + 3811 * D + 2120,
     621 * D**2 + 3200 * D - 389),
]


def part_A():
    print("[A] exchange table (15 rows)")
    for name, O, N, col1, col2 in TABLE:
        e = E(O, N)
        degR = sp.Poly(e, R).degree()
        degD = sp.Poly(e, D).degree()
        c1 = sp.simplify(e.subs(R, 0) / col1)
        c2 = sp.simplify(2 * e.subs(R, (D + 1) / 2) / col2)
        same = c1.is_Rational and c2.is_Rational and c1 == c2 and c1 > 0
        p1, s1 = nonneg_shift(col1)
        p2, s2 = nonneg_shift(col2)
        roots = [r for r in sp.Poly(col2, D).real_roots()]
        check("%-36s E affine in R0 (deg %d), deg %d in D0; factor c = %s; columns > 0 for D0 >= 1"
              % (name, degR, degD, c1), degR == 1 and degD == 2 and same and p1 and p2,
              "col2(1+t) = %s; real roots of col2: %s" % (s2, [float(r) for r in roots]))
        if roots and not all(r < 1 for r in roots):
            FAILS.append("root >= 1 in " + name)


# ------------------------------------------------------------------ [B] factors in the proof
def ratio_is(e, disp, factor):
    return sp.simplify(e - factor * sp.expand(disp)) == 0


def part_B():
    print("[B] displayed polynomials and positive factors of the exchanges (M1)-(M7)")
    check("stalk values T(P4) = 17/8, y(P4) = 7/17, T(P5) = 41/16, y(P5) = 17/41",
          Ty(P4) == (sp.Rational(17, 8), sp.Rational(7, 17)) and Ty(P5) == (sp.Rational(41, 16), sp.Rational(17, 41)))
    check("(M1) {L, L} -> {C}: E = (1/2)(D0^2 + D0 R0 + 4 R0)",
          ratio_is(E([LEAF, LEAF], [C]), D**2 + D * R + 4 * R, sp.Rational(1, 2)))
    check("(M2) {L, C} -> {A1}: E = (1/4)(D0(D0-2) + R0(D0+8))",
          ratio_is(E([LEAF, C], [Arm(1)]), D * (D - 2) + R * (D + 8), sp.Rational(1, 4)))
    check("(M5) {P5} -> {A2}: E = (1/16)(D0+1)(3D0+3R0-2)",
          ratio_is(E([P5], [Arm(2)]), (D + 1) * (3 * D + 3 * R - 2), sp.Rational(1, 16)))
    ok = True
    for j in range(5, 13):
        e = E([Arm(j)], [C, Arm(j - 1)]).subs(D, 1)
        ok &= ratio_is(e, 8 * j**2 - 3 * j - 2 - (12 * j**2 + 9 * j + 6) * R,
                       sp.Rational(3, 2) ** j / (9 * j * (j + 1)))
    check("(M6) {A_j} -> {C, A_{j-1}}, D0 = 1, j = 5..12: E = (3/2)^j/(9 j (j+1)) * display", ok)
    J = sp.symbols("J")
    check("(M6) display at R0 = 1/2, j = 5 + J equals 2J^2 + (25/2)J + 15/2",
          sp.expand((8 * J**2 - 3 * J - 2 - (12 * J**2 + 9 * J + 6) * sp.Rational(1, 2)).subs(J, 5 + J))
          == sp.expand(2 * J**2 + sp.Rational(25, 2) * J + sp.Rational(15, 2)))
    ok = True
    for i in range(0, 11):
        ok &= ratio_is(E([P4, Arm(i)], [C, Arm(i + 1)]),
                       (D + 2) * ((4 * i**2 + 11 * i + 24) * (D + R) + 4 * i**2 + 14 * i),
                       sp.Rational(3, 2) ** i / (24 * (i + 1) * (i + 2)))
    check("(M7)(i) {P4, A_i} -> {C, A_{i+1}}, i = 0..10: E = (3/2)^i/(24(i+1)(i+2)) * display", ok)
    ok = True
    for j in range(1, 5):
        ok &= ratio_is(E([stalk(Arm(j)), LEAF], [C, Arm(j)]), (D + 2) * (D + R),
                       sp.Rational(3, 2) ** (j - 1) * sp.Rational(j, j + 1))
    check("(M7)(v) {[A_j], L} -> {C, A_j}, j = 1..4: E = (3/2)^(j-1) j/(j+1) * (D0+2)(D0+R0)", ok)
    # (M7)(iv) with symbolic i: closed forms of the arm values are needed for symbolic i
    ok = True
    for j in (2, 3, 4):
        def arm(k):
            k = sp.sympify(k)
            return sp.Rational(3, 2) ** k * (4 * k + 3) / (3 * (k + 1)), 3 / (4 * k + 3)
        # the closed form agrees with the recursion for small k
        for k in range(0, 9):
            assert sp.simplify(arm(k)[0] - Ty(Arm(k))[0]) == 0 and sp.simplify(arm(k)[1] - Ty(Arm(k))[1]) == 0
        Ta, ya = arm(j)
        Ts, ys = Ta * (2 + ya) / 2, 1 / (2 + ya)
        Ti, yi = arm(i_)
        Tij, yij = arm(i_ + j)
        PO, RO, PN, RN = Ts * Ti, ys + yi, sp.Rational(3, 2) * Tij, sp.Rational(1, 3) + yij
        e = PN * (2 + D + RN + R) * (2 + D) - PO * (2 + D + RO + R) * (2 + D)
        disp = (D + 2) * (4 * I**2 * (R + t + 2) + I * ((4 * j + 15) * (R + t) + 8 * j + 33)
                          + (16 * j + 23) * (R + t) + 20 * j + 37)
        disp = disp.subs({I: i_ - 1, t: D - 1})
        fac = sp.Rational(3, 2) ** (i_ + j) * j / (18 * (i_ + 1) * (j + 1) * (i_ + j + 1))
        ok &= sp.simplify(sp.powsimp(sp.expand(e - fac * disp), force=True)) == 0
    check("(M7)(iv) {[A_j], A_i} -> {C, A_{i+j}}, j = 2, 3, 4, symbolic i: "
          "E = (3/2)^(i+j) j/(18(i+1)(j+1)(i+j+1)) * display", ok)
    ok = True
    for i in range(2, 9):
        for j in range(0, i - 1):
            e = E([Arm(i), Arm(j)], [Arm(i - 1), Arm(j + 1)])
            th = D + 2 + R
            disp = (D + 2) * (i - j - 1) * ((th - 3) * (4 * (i + j) + 7) + 3)
            ok &= ratio_is(e, disp, sp.Rational(3, 2) ** (i + j) / (9 * i * (i + 1) * (j + 1) * (j + 2)))
    check("(M4) balance {A_i, A_j} -> {A_{i-1}, A_{j+1}}, 2 <= i <= 8, 0 <= j <= i-2: "
          "E = (3/2)^(i+j)/(9 i (i+1)(j+1)(j+2)) * display", ok)


# ------------------------------------------------------------------ [C] (M3)
def part_C():
    print("[C] (M3): the bilinear expression and its eight corner values")
    m = sp.symbols("m", positive=True)
    PO = (m + 1 + S) / (m + 1)
    RO = 1 + 1 / (m + 1 + S)
    PN = sp.Rational(3, 2)
    RN = S + sp.Rational(1, 3)
    mO, mN = 2, m + 1
    # E divided by the weight product of ch(w); the old side is {E, leaf}: weights P_O, messages R_O
    e = PN * (mN + D + RN + R) * (mO + D) - PO * (mO + D + RO + R) * (mN + D)
    disp = (D**2 * (m + 1 - 2 * S) + D * (m**2 + 3 * m + (m - 5) * S)
            + R * (D * (m + 1 - 2 * S) - 2 * (m + 1) * S - 2 * m**2 + 2 * m + 4))
    check("2(m+1) E = displayed expression", sp.simplify(2 * (m + 1) * e - disp) == 0)
    claims = {
        1: [2 * t**2 + 8 * t + 6, 3 * t**2 + 12 * t + 9, t**2 + 4 * t + 3,
            sp.Rational(3, 2) * t**2 + 6 * t + sp.Rational(9, 2)],
        2: [M**2 * t + M**2 + M * t**2 + 9 * M * t + 8 * M + 3 * t**2 + 16 * t + 13,
            sp.Rational(3, 2) * M * t**2 + 7 * M * t + sp.Rational(11, 2) * M + sp.Rational(9, 2) * t**2 + 19 * t
            + sp.Rational(29, 2),
            sp.Rational(3, 2) * M**2 * t + sp.Rational(3, 2) * M**2 + 7 * M * t + 7 * M + sp.Rational(11, 2) * t
            + sp.Rational(11, 2),
            M * t + M + t + 1],
    }
    for case in (1, 2):
        mm = 1 if case == 1 else 2 + M
        Smax = sp.Rational(1, 2) if case == 1 else (mm + 1) / 2
        corners = [(0, 0), (0, D / 2), (Smax, 0), (Smax, D / 2)]
        ok = True
        consts = []
        for (s_, r_), cl in zip(corners, claims[case]):
            v = sp.expand(disp.subs(m, mm).subs({S: s_, R: r_}).subs(D, 1 + t))
            ok &= sp.expand(v - cl) == 0
            co = sp.Poly(v, t, M).coeffs() if case == 2 else sp.Poly(v, t).coeffs()
            ok &= all(c >= 0 for c in co)
            consts.append(v.subs({t: 0, M: 0}))
        check("(M3) m %s: corner values as displayed, nonnegative coefficients, constant terms %s"
              % ("= 1" if case == 1 else ">= 2", consts), ok)


def main():
    part_A()
    part_B()
    part_C()
    print("=" * 78)
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
