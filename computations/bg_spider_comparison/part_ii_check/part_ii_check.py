"""Second check of part (ii) of the comparison with explicit spiders, from the printed rate table (ball arithmetic, Arb 256 bits).

Part (ii): for 3 <= k <= 23 and n >= 316,
    Psi_k - eta_{k-1} (n-1) < Lambda_sp(n)   for n <= 491,   and   Psi_k - eta_{k-1} (n-1) < 0.11218  for n >= 347,
where Lambda_sp(n) = log pi - (n-1) F*, F* = log(621/64)/11, for the spider listed for n in the table of maximizers
(its pi is the exact maximum M_n).  Given the upper bounds Psi_k and the exact rates eta_{k-1} of the
rate table, part (ii) is a finite comparison; this program makes it with:
  * Psi_k and eta_{k-1} as printed in the rate table (typed in below);
  * M_n (n <= 491) read as exact rationals from ../bg_hull_dp/results_dp_491.txt;
  * every logarithm and comparison in Arb ball arithmetic (python-flint, 256 bits); a comparison whose ball
    contains 0 counts as a failure.
The second bound is checked at n = 347; it then holds for every n >= 347, since eta_{k-1} > 0.
It also prints min Lambda_sp(n) over 25 <= n <= 315 (part (iii): >= 0.1206255).
It does not use the programs of ../bg_rate/ (section G of certify.py makes the first check of part (ii)).

Written in October 2026 as an additional check.
Usage: python3 part_ii_check.py      (run from this folder, inside computations/)
"""
import os, re
from fractions import Fraction as Fr
import flint
from flint import arb

flint.ctx.prec = 256
HERE = os.path.dirname(os.path.abspath(__file__))

# rate table: k -> (eta_{k-1}, Psi_k upper bound), as printed
TABLE = {
    2: ("2791/2500000", "0.29989"), 3: ("2791/2500000", "0.27126"), 4: ("2791/2500000", "0.26579"),
    5: ("2791/2500000", "0.26031"), 6: ("2791/2500000", "0.25484"), 7: ("9387/10000000", "0.24772"),
    8: ("4183/5000000", "0.24276"), 9: ("7507/10000000", "0.23873"), 10: ("1701/2500000", "0.23543"),
    11: ("311/500000", "0.23269"), 12: ("179/312500", "0.23036"), 13: ("5309/10000000", "0.22838"),
    14: ("2473/5000000", "0.22665"), 15: ("463/1000000", "0.22514"), 16: ("34/78125", "0.22381"),
    17: ("2053/5000000", "0.22263"), 18: ("1943/5000000", "0.22158"), 19: ("461/1250000", "0.22062"),
    20: ("351/1000000", "0.21977"), 21: ("837/2500000", "0.21898"), 22: ("1/3125", "0.21826"),
    23: ("613/2000000", "0.21761"),
}


def A(q):
    q = Fr(q)
    return arb(q.numerator) / arb(q.denominator)


def main():
    M = {}
    for line in open(os.path.join(HERE, "..", "..", "bg_hull_dp", "results_dp_491.txt")):
        m = re.match(r'n=(\d+) M=(\d+)/(\d+) ', line)
        if m:
            M[int(m.group(1))] = Fr(int(m.group(2)), int(m.group(3)))
    assert all(n in M for n in range(25, 492)), "missing M_n"
    Fstar = A(Fr(621, 64)).log() / 11
    Lam = {n: A(M[n]).log() - (n - 1) * Fstar for n in range(25, 492)}
    ok = True
    worst = None
    print(" k   min over 316<=n<=491 of Lambda_sp(n) - (Psi_k - eta_{k-1}(n-1))   at n   | 0.11218 - (Psi_k - eta_{k-1}*346)")
    for k in range(3, 24):
        eta, psi = A(TABLE[k][0]), A(TABLE[k][1])
        best = None
        for n in range(316, 492):
            mg = Lam[n] - (psi - eta * (n - 1))
            if not mg > 0:
                ok = False
                print(f"FAIL k={k} n={n}: margin {mg}")
            if best is None or mg.mid() < best[0].mid():
                best = (mg, n)
        tail = A("0.11218") - (psi - eta * 346)
        if not tail > 0:
            ok = False
            print(f"FAIL k={k}: tail margin {tail}")
        if worst is None or best[0].mid() < worst[0].mid():
            worst = (best[0], k, best[1])
        print(f"{k:2d}   {float(best[0].mid()):.6e}   {best[1]:4d}   | {float(tail.mid()):.6e}")
    print(f"smallest margin in (ii), 316 <= n <= 491: {float(worst[0].mid()):.4e} at k={worst[1]}, n={worst[2]}")
    lmin = min(range(25, 316), key=lambda n: Lam[n].mid())
    print(f"(iii) min Lambda_sp(n), 25 <= n <= 315: {Lam[lmin].mid().str(10)} at n={lmin}; >= 0.1206255: {Lam[lmin] >= A('0.1206255')}")
    ok &= bool(Lam[lmin] >= A("0.1206255"))
    print("comparison with explicit spiders, part (ii):", "OK" if ok else "FAILED")


if __name__ == "__main__":
    main()
