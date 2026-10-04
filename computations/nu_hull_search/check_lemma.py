"""Check of lem:nu-small-cv from the output of the exact hull search.

Reads dpk215_8.txt (written by `python3 hulldp2.py 215 8 > dpk215_8.txt`) and checks:
  [A] for 2 <= k <= 8 and 3k-2 <= n <= 215, the exact maximum M(n,k) equals the best
      balanced connector-star value max_a F_k(n,a) (stability.cs_best, exact rationals),
      except exactly at (n,k) = (7,3) and (10,3);
  [B] M(7,3) = 9/2 and M(10,3) = 50/9, and the connector-star values there are 35/8 and 265/48;
  [C] if independent_dp_215_8.txt is present (output of the independent implementation
      independent_dp.py), every value M(n,k), k <= 8, n <= 215, agrees with it exactly.
The parsing and the comparison in [A] are taken from the project's original checking script.
"""
import os, re, sys
from fractions import Fraction as Fr
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
from stability import cs_best


def load(fn):
    data = {}
    for l in open(os.path.join(here, fn)):
        m = re.match(r'n=(\d+) k=(\d+) max=(\S+)', l)
        if m:
            data[(int(m.group(1)), int(m.group(2)))] = Fr(m.group(3))
    return data


data = load("dpk215_8.txt")
bad = []
cnt = 0
for (n, k), v in sorted(data.items()):
    if k < 2 or k > 8 or n < 3 * k - 2:
        continue
    b, arg = cs_best(n, k)
    cnt += 1
    if b != v:
        bad.append((n, k))
expected_pairs = sum(215 - (3 * k - 2) + 1 for k in range(2, 9))
assert cnt == expected_pairs, (cnt, expected_pairs)
assert bad == [(7, 3), (10, 3)], bad
print(f"[A] connector-star formula = exact M(n,k) on {cnt} pairs (2<=k<=8, 3k-2<=n<=215); exceptions {bad}")
assert data[(7, 3)] == Fr(9, 2) and data[(10, 3)] == Fr(50, 9)
assert cs_best(7, 3)[0] == Fr(35, 8) and cs_best(10, 3)[0] == Fr(265, 48)
print("[B] M(7,3) = 9/2 (connector-star 35/8), M(10,3) = 50/9 (connector-star 265/48)")
ind = os.path.join(here, "independent_dp_215_8.txt")
if os.path.exists(ind):
    ref = load("independent_dp_215_8.txt")
    # hulldp2.py with KMAX = 8 also prints a line for nu = KMAX + 1; those values are not used
    mine = {key: v for key, v in data.items() if key[1] <= 8}
    common = [key for key in mine if key in ref]
    mism = [key for key in common if mine[key] != ref[key]]
    assert not mism and len(common) == len(mine) == len(ref), (len(common), len(mine), len(ref), mism[:5])
    print(f"[C] all {len(common)} values M(n,k), k<=8, n<=215, agree with the independent implementation")
print("LEMMA nu-small-cv: OK")
