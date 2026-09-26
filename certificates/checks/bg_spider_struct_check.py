"""Exact-arithmetic validation of every inequality used in R3Cert/BGSpiderStruct.lean (StructProp 492).

For each exchange old -> new inside old ++ rest (D0 = |rest|, R0 = sum_rest r), the Lean proof uses a
rational gain bound gamma' <= G(new)/G(old) and the quadratic inequality
    (do + D0 + Ro + R0)(dn + D0) < gamma' (dn + D0 + Rn + R0)(do + D0)
on the region D0 >= d0, lo*D0 <= R0 <= hi*D0.  The form is affine in R0, so it suffices to check the two
endpoint quadratics; each is certified positive for all D0 >= d0 (shifted coefficients / discriminant).
Also checks the two global-comparison numbers.  Run: python3 bg_spider_struct_check.py
"""
from fractions import Fraction as Fr


def alpha(j): return Fr(4 * j + 3, 3 * (j + 1))
def bb(j): return Fr(3, 4 * j + 3)
def g(c): return Fr(3, 2) if c == 'P' else Fr(3, 2) ** c * alpha(c)
def r(c): return Fr(1, 3) if c == 'P' else bb(c)
def cost(c): return 2 if c == 'P' else 2 * c + 1


def prod(xs):
    p = Fr(1)
    for x in xs:
        p *= x
    return p


def certify(name, old, new, gp, lo, hi, d0):
    assert sum(map(cost, old)) == sum(map(cost, new)), name
    gam = prod(map(g, new)) / prod(map(g, old))
    assert 0 < gp <= gam, (name, float(gam), gp)
    do, dn, Ro, Rn = len(old), len(new), sum(map(r, old)), sum(map(r, new))
    for c in (lo, hi):
        a = (gp - 1) * (1 + c)
        b = gp * ((dn + Rn) + (1 + c) * do) - ((do + Ro) + (1 + c) * dn)
        k = gp * (dn + Rn) * do - (do + Ro) * dn
        A, B, K = a, 2 * a * d0 + b, a * d0 * d0 + b * d0 + k
        ok = (A >= 0 and B >= 0 and K > 0) or (A > 0 and K > 0 and B * B < 4 * A * K)
        assert ok, (name, c)
    print(f"{name:28s} gamma={float(gam):.6f} gamma'={gp}  D0>={d0}  R0/D0 in [{lo},{hi}]  OK")


Z, O, T, N = Fr(0), Fr(1), Fr(1, 3), Fr(1, 9)
gains = {1: Fr(1937, 1000), 2: Fr(158, 125), 3: Fr(537, 500), 7: Fr(1051, 1000), 8: Fr(11, 10),
         9: Fr(1161, 1000), 10: Fr(1231, 1000), 11: Fr(164, 125), 12: Fr(1403, 1000)}
for j, gp in gains.items():
    certify(f"11 A{j} -> {2*j+1} A5", [j] * 11, [5] * (2 * j + 1), gp, Z, O, 0)
certify("11 A6 -> 13 A5", [6] * 11, [5] * 13, Fr(1271, 1250), Z, T, 0)
certify("11 A4 -> 9 A5", [4] * 11, [5] * 9, Fr(10113, 10000), N, O, 27)
certify("9 P -> 2 A4", ['P'] * 9, [4, 4], Fr(1069, 1000), N, O, 27)

# split A_{u+13} -> A_{u+2} + 2 A5 (Lean: polynomial in u, proved for all u); spot check exactly here
for u in range(0, 300):
    J, k = u + 13, u + 2
    for D0 in list(range(0, 200)) + [10 ** 4, 10 ** 7]:
        for R0 in (Z, Fr(D0, 3)):
            lhs = g(J) * (1 + D0 + bb(J) + R0) * (3 + D0)
            rhs = g(k) * g(5) ** 2 * (3 + D0 + bb(k) + 2 * bb(5) + R0) * (1 + D0)
            assert lhs < rhs, (u, D0, R0)
print("split A_{u+13} -> A_{u+2} + 2 A5: OK for u < 300, D0 in [0,200] u {1e4,1e7}, R0 in {0, D0/3}")

hh = lambda j: alpha(j) ** 2 * Fr(2, 3)
W = Fr(10, 9) ** 2 * Fr(529, 486) ** 37
s1 = 4 * Fr(32, 27) ** 2
s3 = Fr(4, 3) ** 2 * hh(12) ** 20
assert s1 < W and s3 < W
print(f"global: step1 {float(s1):.3f} < {float(W):.3f};  step3 {float(s3):.3f} < {float(W):.3f}")
