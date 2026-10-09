"""Compare the best-spider rule with the table of maximizers (4 <= n <= 491), in exact arithmetic.

The rule (the best spider for n >= 492), applied verbatim to every n >= 4: with s = 6(n-1) mod 11 (so that
n-1 = 2s mod 11), the spider has only arms at its center, all A_5 except
    s = 0      : none,
    s in {1,2} : s arms A_6,
    s = 3      : eight arms A_4 if n <= 722, three arms A_6 if n >= 733,
    s = 4      : seven arms A_4 if n <= 2319, four arms A_6 if n >= 2330,
    s >= 5     : 11 - s arms A_4.
The number of A_5 is (n - 1 - 9 k_4 - 13 k_6)/11; when it is negative the rule names no spider.

Checks:
  [1] the rule computed in two ways (the case list above, and the two candidates X_s, Y_s of the
      best-spider comparison) agrees for every 4 <= n <= 5000;
  [2] the table of maximizers (../bg_hull_dp/table_maximizers.tex)
      is parsed; every entry has n - 1 vertices outside the center;
  [3] the value of every table spider, computed exactly from the closed formula for a spider, equals the exact maximum
      M_n printed by the hull computation (../bg_hull_dp/results_dp_491.txt);
  [4] rule = table (as multisets of center branches) exactly for 424 <= n <= 491, and not at n = 423;
      the full list of failures for n >= 300, and the stated list of these sizes;
  [5] at every failure the exact value of the rule spider (if it exists) is strictly below M_n.
All arithmetic is exact (integers and fractions.Fraction).

Usage: python3 rule_vs_table.py
"""
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = os.path.join(HERE, "..", "bg_hull_dp", "table_maximizers.tex")
DPOUT = os.path.join(HERE, "..", "bg_hull_dp", "results_dp_491.txt")


# ------------------------------------------------------------------ atoms (cherry and arms A_j)
def atom(x):
    """(T, y) of a center child: 'C' (cherry) or ('A', j) = arm A_j (A_0 = leaf)."""
    if x == "C":
        return Fr(3, 2), Fr(1, 3)
    j = x[1]
    alpha = Fr(4, 3) - Fr(1, 3 * (j + 1))
    return Fr(3, 2) ** j * alpha, 1 / ((j + 1) * alpha)


def cost(x):
    return 2 if x == "C" else 2 * x[1] + 1


def omega(spider):
    """pi of the spider = (prod T)(1 + R/D), the closed formula; spider = dict child -> multiplicity."""
    P = Fr(1)
    R = Fr(0)
    D = 0
    for x, k in spider.items():
        T, y = atom(x)
        P *= T ** k
        R += k * y
        D += k
    return P * (1 + R / D)


def size(spider):
    return 1 + sum(k * cost(x) for x, k in spider.items())


# ------------------------------------------------------------------ the rule, two ways
def rule_cases(n):
    s = (6 * (n - 1)) % 11
    k4 = k6 = 0
    if s in (1, 2):
        k6 = s
    elif s == 3:
        if n <= 722:
            k4 = 8
        else:
            k6 = 3
    elif s == 4:
        if n <= 2319:
            k4 = 7
        else:
            k6 = 4
    elif s >= 5:
        k4 = 11 - s
    rest = n - 1 - 9 * k4 - 13 * k6
    assert rest % 11 == 0
    k5 = rest // 11
    if k5 < 0:
        return None
    sp = {("A", 5): k5, ("A", 4): k4, ("A", 6): k6}
    sp = {x: k for x, k in sp.items() if k}
    return sp if sp else None


def rule_candidates(n):
    """The same rule via X_s = A6^s A5^a, Y_s = A4^(11-s) A5^(a+2s-9), n - 1 = 13 s + 11 a."""
    s = (6 * (n - 1)) % 11
    assert (n - 1 - 2 * s) % 11 == 0
    if s == 0:
        a = (n - 1) // 11
        return {("A", 5): a} if a > 0 else None
    a = (n - 1 - 13 * s) // 11
    X = {("A", 6): s, ("A", 5): a}
    Y = {("A", 4): 11 - s, ("A", 5): a + 2 * s - 9}
    if s in (1, 2):
        pick = X
    elif s == 3:
        pick = Y if n <= 722 else X
    elif s == 4:
        pick = Y if n <= 2319 else X
    else:
        pick = Y
    if any(k < 0 for k in pick.values()):
        return None
    pick = {x: k for x, k in pick.items() if k}
    return pick if pick else None


# ------------------------------------------------------------------ the table and the DP output
def parse_table(path):
    tab = {}
    for line in open(path):
        if not re.match(r"^\d+ & ", line):
            continue
        cells = [c.strip() for c in line.strip().rstrip("\\").split("&")]
        for i in range(0, len(cells) - 2, 3):
            if not cells[i]:
                continue
            n = int(cells[i])
            sp = {}
            for m in re.finditer(r"(C|A_\{(\d+)\})(\^\{(\d+)\})?", cells[i + 1]):
                key = "C" if m.group(1) == "C" else ("A", int(m.group(2)))
                sp[key] = sp.get(key, 0) + int(m.group(4) or 1)
            tab[n] = sp
    return tab


def parse_dp(path):
    M = {}
    for line in open(path):
        m = re.match(r"n=(\d+) M=(\d+)/(\d+) ", line) or re.match(r"n=(\d+) M=(\d+) ", line)
        if m:
            n = int(m.group(1))
            M[n] = Fr(int(m.group(2)), int(m.group(3))) if m.lastindex == 3 else Fr(int(m.group(2)))
    return M


def fmt(sp):
    if sp is None:
        return "(none)"
    order = sorted(sp, key=lambda x: (0, 0) if x == "C" else (1, -x[1]))
    out = []
    for x in order:
        name = "C" if x == "C" else "A%d" % x[1]
        out.append(name + ("^%d" % sp[x] if sp[x] > 1 else ""))
    return " ".join(out)


def main():
    ok = True

    # [1]
    for n in range(4, 5001):
        assert rule_cases(n) == rule_candidates(n), n
        r = rule_cases(n)
        if r is not None:
            assert size(r) == n, n
    print("[1] the rule computed from the case list and from the candidates X_s, Y_s agrees for 4 <= n <= 5000")

    # [2]
    tab = parse_table(TABLE)
    ns = sorted(tab)
    assert ns == list(range(4, 492)), (ns[:3], ns[-3:], len(ns))
    bad_size = [n for n in ns if size(tab[n]) != n]
    assert not bad_size, bad_size
    print("[2] table parsed: %d entries, n = %d..%d, every entry has n vertices" % (len(ns), ns[0], ns[-1]))

    # [3]
    M = parse_dp(DPOUT)
    missing = [n for n in ns if n not in M]
    assert not missing, missing[:5]
    neq = [n for n in ns if omega(tab[n]) != M[n]]
    assert not neq, neq[:10]
    print("[3] for every 4 <= n <= 491 the exact value of the table spider equals the exact M_n of the hull computation")

    # [4]
    fail = [n for n in ns if rule_cases(n) != tab[n]]
    agree_424 = all(rule_cases(n) == tab[n] for n in range(424, 492))
    fails_423 = rule_cases(423) != tab[423]
    print("[4] rule = table for every 424 <= n <= 491: %s" % agree_424)
    print("    rule != table at n = 423: %s   (rule: %s; table: %s)" % (fails_423, fmt(rule_cases(423)), fmt(tab[423])))
    ok &= agree_424 and fails_423
    big = [n for n in fail if n >= 300]
    print("    failures for n >= 300 (%d): %s" % (len(big), big))
    print("    last failure: n = %d" % max(fail))
    expected = sorted({300, 311, 322, 333} | {n for n in range(302, 424) if n % 11 == 5})
    claim = big == expected
    print("    = {300, 311, 322, 333} u {n = 5 mod 11, 302 <= n <= 423} (stated list): %s" % claim)
    ok &= claim
    small = [n for n in fail if n < 300]
    print("    failures for 4 <= n <= 299: %d of 296 sizes" % len(small))
    cher = [n for n in ns if "C" in tab[n]]
    print("    last table maximizer with a cherry at the center: n = %d (%s)" % (max(cher), fmt(tab[max(cher)])))
    ok &= max(cher) == 333
    print("    table at n = 311: %s" % fmt(tab[311]))
    ok &= tab[311] == {"C": 1, ("A", 5): 28}
    print("    detail for n >= 300:")
    for n in big:
        print("      n=%d  rule: %-16s table: %s" % (n, fmt(rule_cases(n)), fmt(tab[n])))

    # [5]
    worse = []
    for n in fail:
        r = rule_cases(n)
        if r is None:
            continue
        if not omega(r) < M[n]:
            worse.append(n)
    nonexist = [n for n in fail if rule_cases(n) is None]
    print("[5] at every failure the rule spider exists and is strictly worse than M_n, or does not exist: %s"
          % (not worse))
    print("    sizes where the rule names no spider (negative number of A_5): %s" % nonexist)
    ok &= not worse
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
