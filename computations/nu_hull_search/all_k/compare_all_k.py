"""Compare the all-k runs of the matching-number search.

Reads (in this folder)
  dp120_allk.txt         output of  python3 ../hulldp2.py 120          (all k, n <= 120)
  independent_dp_60.txt  output of  python3 ../independent_dp.py 60    (all k, n <= 60; exact Fractions)
and, in the parent folder, ../dpk215_8.txt (k <= 8, n <= 215) and ../independent_dp_215_8.txt.
Checks that every value M(n,k) common to two files is the same exact rational, and that the numbers of
extremal trees in dp120_allk.txt and ../dpk215_8.txt agree; reports how many extremal trees are not unique.

Written in October 2026 as an additional check.
Usage: python3 compare_all_k.py
"""
import os, re
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))


def load(fn):
    out = {}
    for line in open(fn):
        m = re.match(r'n=(\d+) k=(\d+) max=(\S+)(?:.*count=(\d+))?', line)
        if m:
            out[(int(m.group(1)), int(m.group(2)))] = (Fr(m.group(3)), int(m.group(4)) if m.group(4) else None)
    return out


A = load(os.path.join(HERE, "dp120_allk.txt"))
I60 = load(os.path.join(HERE, "independent_dp_60.txt"))
K8 = load(os.path.join(HERE, "..", "dpk215_8.txt"))
I215 = load(os.path.join(HERE, "..", "independent_dp_215_8.txt"))
ok = True
print(f"dp120_allk.txt: {len(A)} pairs (n,k), n <= {max(n for n, k in A)}, k <= {max(k for n, k in A)}")
print(f"independent_dp_60.txt: {len(I60)} pairs")
for name, B, cond in (("independent_dp_60.txt (all k, n<=60)", I60, lambda n, k: True),
                      ("../dpk215_8.txt (k<=8)", K8, lambda n, k: k <= 8),
                      ("../independent_dp_215_8.txt (k<=8)", I215, lambda n, k: k <= 8)):
    common = [key for key in A if key in B and cond(*key)]
    bad = [key for key in common if A[key][0] != B[key][0]]
    ok &= not bad
    print(f"values vs {name}: {len(common)} common pairs, mismatches {len(bad)} {bad[:5]}")
# completeness for n <= 60
miss = [(n, k) for n in range(2, 61) for k in range(1, n // 2 + 1) if (n, k) not in A or (n, k) not in I60]
ok &= not miss
print(f"every (n,k), 2<=n<=60, 1<=k<=n/2, present in both all-k runs: {not miss}")
cnt = [key for key in A if key in K8 and key[1] <= 8 and A[key][1] != K8[key][1]]
ok &= not cnt
print(f"numbers of extremal trees vs ../dpk215_8.txt: {len([k for k in A if k in K8 and k[1] <= 8])} pairs, differences {len(cnt)}")
nonuniq = sorted(key for key in A if A[key][1] != 1)
print(f"pairs with more than one extremal tree in dp120_allk.txt: {len(nonuniq)} {nonuniq[:20]}")
print("RESULT:", "PASS" if ok else "FAIL")
