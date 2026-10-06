# SPDX-License-Identifier: Apache-2.0
"""Second, separate implementation of the rule-versus-table check.

Applies the rule of Theorem thm:bg-bestspider, as stated, to every n of the
appendix table (4 <= n <= 491) and compares the rule spider with the printed
maximizer as multisets of center branches.  Integers only.

Usage: python3 check_rule_table.py [path/to/table_maximizers.tex]
"""
import os
import re
import sys
from collections import Counter


def rule_spider(n):
    """Center branches of the rule spider, or None if it does not exist."""
    s = 6 * (n - 1) % 11
    k4, k6 = 0, 0
    if s in (1, 2):
        k6 = s
    elif s == 3:
        k4, k6 = (8, 0) if n <= 722 else (0, 3)
    elif s == 4:
        k4, k6 = (7, 0) if n <= 2319 else (0, 4)
    elif s >= 5:
        k4 = 11 - s
    rest = n - 1 - 9 * k4 - 13 * k6
    assert rest % 11 == 0
    if rest < 0:
        return None
    return +Counter({"A4": k4, "A5": rest // 11, "A6": k6})


def parse_table(path):
    """{n: Counter of center branches} from the rows of the printed table."""
    table = {}
    tok = re.compile(r"(C|A_\{(\d+)\})(?:\^\{?(\d+)\}?)?")
    for line in open(path, encoding="utf-8"):
        if not re.match(r"\s*\d", line):
            continue
        cells = [c.strip() for c in line.split("\\\\")[0].split("&")]
        for i in range(0, len(cells) - 2, 3):
            if not cells[i]:
                continue
            n, spider = int(cells[i]), Counter()
            for m in tok.finditer(cells[i + 1]):
                kind = "C" if m.group(1) == "C" else "A" + m.group(2)
                spider[kind] += int(m.group(3) or 1)
            size = sum(k * (2 if b == "C" else 2 * int(b[1:]) + 1)
                       for b, k in spider.items())
            assert size == n - 1, (n, cells[i + 1])
            assert n not in table
            table[n] = spider
    return table


def show(spider):
    if spider is None:
        return "(does not exist)"
    return " ".join(b if k == 1 else "%s^%d" % (b, k)
                    for b, k in sorted(spider.items(), key=lambda t: t[0]))


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "..", "bg_hull_dp", "table_maximizers.tex")
    if len(sys.argv) > 1:
        path = sys.argv[1]
    elif not os.path.exists(path):
        sys.exit("table not found at %s; pass its path as an argument" % path)
    table = parse_table(path)
    ok = True
    print("table rows parsed: %d (n = %d..%d)" % (len(table), min(table), max(table)))
    if sorted(table) != list(range(4, 492)):
        print("FAIL: table does not list every 4 <= n <= 491")
        ok = False

    fails = [n for n in sorted(table) if rule_spider(n) != table[n]]
    print("rule != table for 4 <= n <= 299: %d of %d sizes"
          % (sum(n < 300 for n in fails), sum(n < 300 for n in table)))
    print("rule != table for n >= 300:")
    for n in fails:
        if n >= 300:
            print("  n = %d: rule %s, table %s"
                  % (n, show(rule_spider(n)), show(table[n])))

    claimed = [300, 311, 322, 333] + list(range(302, 424, 11))
    late = [n for n in fails if n >= 300]
    print("failures for n >= 300: %d sizes %s" % (len(late), late))
    print("matches the paper's list of 16 sizes: %s" % (late == sorted(claimed)))
    ok &= late == sorted(claimed)

    for lo, hi in ((424, 456), (424, 491)):
        bad = [n for n in fails if lo <= n <= hi]
        print("rule == table for every %d <= n <= %d: %s" % (lo, hi, not bad))
        ok &= not bad
    print("n = 423 is a failure: %s" % (423 in fails))
    ok &= 423 in fails

    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
