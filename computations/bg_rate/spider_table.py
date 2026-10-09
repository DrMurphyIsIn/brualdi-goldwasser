"""Parse the maximizer table (table_maximizers.tex, the table of maximizers for 4 <= n <= 491) and compute exact Phi*(n) = log pi(T_n) - (n-1) lambda
(a lower bound for the true Phi*(n) that does not depend on the table being optimal)."""
import os, re, math
from fractions import Fraction as Fr
from core import pi_rooted, CHERRY, LEAF, ARM, lam

def parse():
    txt = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'table_maximizers.tex')).read()
    rows = {}
    for line in txt.splitlines():
        if '&' not in line or 'maximizer' in line: continue
        cells = [c.strip() for c in line.replace('\\\\', '').split('&')]
        for i in range(0, len(cells) - 2, 3):
            try:
                n = int(cells[i])
            except ValueError:
                continue
            desc = cells[i + 1]
            ch = []
            for m in re.finditer(r'([CA])(?:_\{(\d+)\})?(?:\^\{(\d+)\})?', desc.replace('$', '').replace('\\,', ' ')):
                kind, j, e = m.group(1), m.group(2), m.group(3)
                e = int(e) if e else 1
                if kind == 'C':
                    ch += [CHERRY] * e
                else:
                    ch += [ARM(int(j))] * e
            rows[n] = ch
    return rows

def phistar():
    rows = parse()
    out = {}
    for n, ch in rows.items():
        size = 1 + sum(1 if c == LEAF else (2 if c == CHERRY else 2 * len(c) + 1) for c in ch)
        assert size == n, (n, size)
        p = pi_rooted(ch)
        out[n] = math.log(p.numerator) - math.log(p.denominator) - (n - 1) * lam
    return out

if __name__ == "__main__":
    ps = phistar()
    for n in [4, 10, 20, 21, 30, 50, 100, 149, 150, 200, 300, 400, 491]:
        print(n, round(ps[n], 6))
