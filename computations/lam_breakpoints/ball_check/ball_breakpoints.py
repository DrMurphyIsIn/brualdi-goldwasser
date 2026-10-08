"""Second enclosure of the breakpoints lambda_j, 3 <= j <= 30, in Arb ball arithmetic (python-flint, 256 bits).

f_j(lam) = [ j log(1+lam/2) + log(1 + lam j y_c/(j+1)) ] / (2j+1),  y_c = 1/(2+lam),
and lambda_j is the activity where f_j = f_{j+1} (A_j and A_{j+1} tie); f_j - f_{j+1} > 0 below lambda_j and
< 0 above it (single crossing).  For each j the program bisects [1/10, 3] with exact rational endpoints,
deciding each sign by an Arb enclosure of f_j - f_{j+1} at the exact rational midpoint, until the bracket has
width < 2e-18; it then re-checks the two end signs and prints the bracket.  Every sign used must be decided
(the ball must not contain 0); otherwise the program stops with FAIL.  It does not use rates.py or
breakpoints.py; at the end it reads the enclosures printed by breakpoints.py in ../expected_output.txt and
checks that each overlaps the one found here (both contain the unique zero).

Written in October 2026 as an additional check.
Usage: python3 ball_breakpoints.py
"""
import os, re, sys
from fractions import Fraction as Fr
import flint
from decimal import Decimal, getcontext
from flint import arb

flint.ctx.prec = 256
HERE = os.path.dirname(os.path.abspath(__file__))


def dec(q, digits=22):
    getcontext().prec = 60
    return f"{Decimal(q.numerator) / Decimal(q.denominator):.{digits}f}"


def A(q):
    return arb(q.numerator) / arb(q.denominator)


def diff(j, lam):
    """Arb enclosure of f_j(lam) - f_{j+1}(lam) at the exact rational lam."""
    L = A(lam)
    c = (1 + L / 2).log()
    yc = 1 / (2 + L)
    fj = (j * c + (1 + L * j * yc / (j + 1)).log()) / (2 * j + 1)
    k = j + 1
    fk = (k * c + (1 + L * k * yc / (k + 1)).log()) / (2 * k + 1)
    return fj - fk


def sign(j, lam):
    d = diff(j, lam)
    if d > 0:
        return 1, d
    if d < 0:
        return -1, d
    print(f"FAIL: sign of f_{j}-f_{j+1} at {lam} not decided: {d}")
    sys.exit(1)


def read_reference():
    ref = {}
    fn = os.path.join(HERE, "..", "expected_output.txt")
    for line in open(fn):
        m = re.match(r'\s*(\d+)\s+\[\[([0-9.]+), [0-9.]+\], \[([0-9.]+), [0-9.]+\]\]\s+VERIFIED', line)
        if m:
            ref[int(m.group(1))] = (Fr(m.group(2)), Fr(m.group(3)))
    return ref


def main():
    WIDTH = Fr(2, 10 ** 18)
    ref = read_reference()
    allok = True
    print(" j   enclosure [lo, hi] of lambda_j (Arb, 256 bits)            width    |f_j-f_{j+1}| at lo, hi")
    enc = {}
    for j in range(3, 31):
        lo, hi = Fr(1, 10), Fr(3)
        assert sign(j, lo)[0] == 1 and sign(j, hi)[0] == -1
        while hi - lo >= WIDTH:
            mid = (lo + hi) / 2
            if sign(j, mid)[0] > 0:
                lo = mid
            else:
                hi = mid
        slo, dlo = sign(j, lo)
        shi, dhi = sign(j, hi)
        ok = slo == 1 and shi == -1
        allok &= ok
        enc[j] = (lo, hi)
        print(f"{j:2d}  [{dec(lo)}, {dec(hi)}]  {float(hi - lo):.1e}  "
              f"{float(abs(dlo.mid())):.2e} {float(abs(dhi.mid())):.2e}  {'VERIFIED' if ok else 'FAIL'}")
    over = 0
    for j, (a, b) in ref.items():
        lo, hi = enc[j]
        if max(a, lo) <= min(b, hi):
            over += 1
        else:
            allok = False
            print(f"j={j}: enclosure of breakpoints.py [{float(a)}, {float(b)}] does not meet this one")
    print(f"enclosures of breakpoints.py read: {len(ref)}; overlapping the ones found here: {over}")
    # the intervals of Lemma lam-bp
    lemma = {3: ("0.43050", "0.43051"), 4: ("0.87247", "0.87248"), 5: ("1.19239", "1.19240"), 6: ("1.43559", "1.43560")}
    for j, (p, q) in lemma.items():
        inside = Fr(p) < enc[j][0] and enc[j][1] < Fr(q)
        allok &= inside
        print(f"j={j}: enclosure inside the interval ({p}, {q}) of the lemma: {inside}")
    print("ALL VERIFIED" if allok else "FAILED")


if __name__ == "__main__":
    main()
