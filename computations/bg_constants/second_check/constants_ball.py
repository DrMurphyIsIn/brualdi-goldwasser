"""Second check of the constants at lambda = 1, (a)-(d), and the junction table, in Arb ball arithmetic
(python-flint, 256 bits), from the definitions in the text:
    F* = log(621/64)/11,  q = 3/23,  beta = 2F* - log(3/2),  kappa = beta/(1/3 - q)^2,
    gamma = (3/2)(F* - beta),  s = 2 kappa (1/3 - q),  r_c = 3/(4c+3),  p = 1 + q,
    D_c^- = s - r_c + 2 kappa (r_c - q) r_c^2,   D_c^+ = gamma - r_c + 2 kappa (r_c - q) r_c^2,
    m_c = F* + c beta - log((4c+3)/(3c+3)) - kappa (r_c - q)^2,
    Q(c) = F* - kappa q^2 - log((1+pc)/(c+1)) - c/(4 kappa (1+pc)^2).
Every strict inequality of the lemma is decided on the balls (a ball that meets the bound counts as a
failure); m_5 = 0 is exact (F* + 5 beta = log(23/18)), and the program checks that its ball contains 0.
It does not use the programs of ../ or ../../bg_nonatom_gap/.

Written in October 2026 as an additional check.
Usage: python3 constants_ball.py
"""
from fractions import Fraction as Fr
import flint
from flint import arb

flint.ctx.prec = 256


def A(x):
    x = Fr(x)
    return arb(x.numerator) / arb(x.denominator)


def sq(x):
    return x * x   # arb powers are avoided: x ** 2 gives nan for an exact zero ball


Fs = A(Fr(621, 64)).log() / 11
q = A(Fr(3, 23))
beta = 2 * Fs - A(Fr(3, 2)).log()
kappa = beta / sq(A(Fr(1, 3)) - q)
gamma = A(Fr(3, 2)) * (Fs - beta)
s = 2 * kappa * (A(Fr(1, 3)) - q)
p = 1 + q
ok = True
lines = []


def lt(a, b, what):
    global ok
    good = bool(a < b)
    ok &= good
    lines.append(f"  {what}: {'OK' if good else 'FAIL'}")


def show(name, x):
    lines.append(f"  {name} = {x.str(12)}")


lines.append("(a)")
for name, x, lo, hi in (("F*", Fs, "0.2065861", "0.2065863"), ("beta", beta, "0.0077071", "0.0077074"),
                        ("kappa", kappa, "0.18721", "0.18722"), ("gamma", gamma, "0.29831", "0.29833")):
    show(name, x)
    lt(A(lo), x, f"{lo} < {name}")
    lt(x, A(hi), f"{name} < {hi}")
lt(A("0.18722"), A(Fr(1, 5)), "0.18722 < 1/5")
lines.append("(b)")
b1 = A(Fr(10, 9)) * gamma - A(Fr(1, 3)); show("(10/9)gamma - 1/3", b1); lt(b1, A("-0.0018"), "< -0.0018")
b2 = s - A(Fr(3, 7)) + gamma * A(Fr(9, 49)); show("s - 3/7 + gamma (3/7)^2", b2); lt(b2, A("-0.297"), "< -0.297")
b3 = 1 - 2 * kappa / 3 * (1 - 2 * q); show("1 - (2 kappa/3)(1-2q)", b3); lt(A("0.907"), b3, "> 0.907")
b4 = gamma - A(Fr(3, 43)) - 2 * kappa * q * A(Fr(9, 1849)); show("gamma - 3/43 - 2 kappa q (3/43)^2", b4); lt(A("0.228"), b4, "> 0.228")
lt(s, gamma, "gamma > s")
lines.append("(c) junction table")
TAB = {2: ("-0.1930", "-0.1925", "0.0293", "0.0298", "0.0173", "0.0178"),
       3: ("-0.1232", "-0.1228", "0.0991", "0.0997", "0.0054", "0.0059"),
       4: ("-0.0819", "-0.0814", "0.1404", "0.1410", "0.0007", "0.0011"),
       5: ("-0.0547", "-0.0542", "0.1676", "0.1682", None, None),
       6: ("-0.0355", "-0.0350", "0.1868", "0.1874", "0.0012", "0.0017"),
       7: ("-0.0212", "-0.0206", "0.2011", "0.2018", "0.0041", "0.0047"),
       8: ("-0.0102", "-0.0095", "0.2121", "0.2128", "0.0080", "0.0087"),
       9: ("-0.0014", "-0.0007", "0.2209", "0.2217", "0.0127", "0.0134")}
for c, (a1, a2, b1_, b2_, c1, c2) in TAB.items():
    r = A(Fr(3, 4 * c + 3))
    Dm = s - r + 2 * kappa * (r - q) * r * r
    Dp = gamma - r + 2 * kappa * (r - q) * r * r
    m = Fs + c * beta - A(Fr(4 * c + 3, 3 * c + 3)).log() - kappa * sq(r - q)
    good = bool(A(a1) < Dm and Dm < A(a2) and A(b1_) < Dp and Dp < A(b2_))
    if c1 is None:
        good &= bool(m.contains(0) and m.rad() < A(Fr(1, 10 ** 70)))
    else:
        good &= bool(A(c1) < m and m < A(c2))
    ok &= good
    lines.append(f"  c={c}: D-={Dm.str(6, radius=False)} D+={Dp.str(6, radius=False)} m={m.str(6, radius=False)}"
                 f"{' (ball contains 0, radius ' + m.rad().str(2, radius=False) + ')' if c1 is None else ''}  {'OK' if good else 'FAIL'}")
lines.append("(d)")
c = 10
Q = Fs - kappa * q * q - ((1 + p * c) / (c + 1)).log() - A(c) / (4 * kappa * sq(1 + p * c))
show("Q(10)", Q)
lt(A("0.0030"), Q, "0.0030 < Q(10)")
lt(Q, A("0.0033"), "Q(10) < 0.0033")
print("\n".join(lines))
print("constants at lambda = 1, (a)-(d):", "OK" if ok else "FAILED")
