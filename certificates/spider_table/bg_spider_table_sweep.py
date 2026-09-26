#!/usr/bin/env python3
"""
Exact sweep behind the Lean spider-table theorem (BGSpiderTable): for every n in [4, N], the table
maximizer Tab(n) (bg_spider_opt_4_2400.json) has canonical balanced form (C cherries; a arms of size s,
b arms of size s+1; leaves are arms of size 0) and F(Tab(n)) >= F of
  (i)  every balanced configuration (C, m): arm sizes {s, s+1} determined by the arm vertex count, and
  (ii) every configuration with at most 2 children.
Maximizers with >= 3 children are balanced (BGSpiderOpt.balanced_of_isMax), so (i)+(ii) cover a maximizer.
Exact integer arithmetic only (F = num/den, no gcd), mirroring the Lean checker.
"""
import json, sys
from fractions import Fraction as Fr

def g_nd(j):   # g(arm j) = 3^j (4j+3) / (2^j * 3 (j+1))
    return 3**j * (4*j + 3), 2**j * 3 * (j + 1)
def r_nd(j):
    return 3, 4*j + 3

def F_counts(C, s, a, b):
    """F of C cherries, a arms of size s, b arms of size s+1, as a Fraction."""
    gs, gt = Fr(*g_nd(s)), Fr(*g_nd(s + 1))
    P = Fr(3, 2)**C * gs**a * gt**b
    R = Fr(C, 3) + a * Fr(*r_nd(s)) + b * Fr(*r_nd(s + 1))
    D = C + a + b
    return P * (1 + R / D)

def F_list(ch):   # ch: list of ('P',) or ('A', j)
    P = Fr(1); R = Fr(0)
    for c in ch:
        if c[0] == 'P': P *= Fr(3, 2); R += Fr(1, 3)
        else: P *= Fr(*g_nd(c[1])); R += Fr(*r_nd(c[1]))
    return P * (1 + R / len(ch))

def balanced_configs(n):
    """All (C, s, a, b) with >= 3 children, arms of sizes s (a of them) and s+1 (b), 2C + sum(2j+1) = n-1."""
    out = []
    for C in range(0, (n - 1) // 2 + 1):
        V = n - 1 - 2 * C              # arm vertex budget
        for m in range(0, V + 1):
            if C + m < 3: continue
            if (V - m) % 2: continue
            if m == 0:
                if V == 0: out.append((C, 0, 0, 0))
                continue
            J = (V - m) // 2           # total cherries on arms
            s, b = divmod(J, m); a = m - b
            out.append((C, s, a, b))
    return out

def small_configs(n):
    kids = [('P',)] + [('A', j) for j in range(0, n)]
    cost = lambda c: 2 if c[0] == 'P' else 2 * c[1] + 1
    out = [[c] for c in kids if cost(c) == n - 1]
    for i, c1 in enumerate(kids):
        for c2 in kids[i:]:
            if cost(c1) + cost(c2) == n - 1: out.append([c1, c2])
    return out

def tab_canon(n, d):
    """Canonical (C, s, a, b) of a table maximizer (prefer a balanced representation)."""
    best = None
    for mx in d[str(n)]['maximizers']:
        arms = []
        for j, c in mx['arms'].items(): arms += [int(j)] * c
        arms += [0] * mx.get('L', 0)
        C = mx['C']
        if not arms:
            cand = (C, 0, 0, 0)
        else:
            s = min(arms)
            if max(arms) > s + 1: continue
            cand = (C, s, arms.count(s), arms.count(s + 1))
        if C + len(arms) >= 3:
            return cand
        best = best or cand
    return best

def main(N, opt_json='bg_spider_opt_4_2400.json', out_json=None):
    d = json.load(open(opt_json))
    tab = {}
    nconf = 0
    for n in range(4, N + 1):
        t = tab_canon(n, d)
        assert t is not None, f"no canonical table form at n={n}"
        C, s, a, b = t
        assert 1 + 2 * C + a * (2 * s + 1) + b * (2 * s + 3) == n, n
        Ft = F_counts(C, s, a, b) if C + a + b >= 1 else None
        assert Ft == Fr(d[str(n)]['max_exact']) if 'max_exact' in d[str(n)] and d[str(n)]['max_exact'] else True
        for (C2, s2, a2, b2) in balanced_configs(n):
            nconf += 1
            assert F_counts(C2, s2, a2, b2) <= Ft, (n, (C2, s2, a2, b2))
        for ch in small_configs(n):
            nconf += 1
            assert F_list(ch) <= Ft, (n, ch)
        tab[n] = t
    print(f"sweep OK for n = 4..{N}: {nconf} configurations checked exactly")
    json.dump({str(k): v for k, v in tab.items()}, open(out_json or f'bg_spider_table_canon_{N}.json', 'w'))

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 491, *(sys.argv[2:4]))
