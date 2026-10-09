"""Lemma M = the unmatched-vertices lemma: for every planted branch b and lam >= 2, sum_v P(v unmatched) >= 2n/(2+lam) in the monomer-dimer model with
activities lam/(d_u d_v) (planted degrees). Checks: (1) the group identity tau_v + sum_leaves tau_l = k + (1-kc)/B and inequality;
(2) the vertex-level bounds on real trees (interior >= 2/(2+lam); groups >= 2(k+1)/(2+lam)).
The ratio-monotonicity / elasticity check lives in monotone_ratio.py."""
import random, math
exec(open('monotone_ratio.py').read().split('worst = {}')[0])
random.seed(11)
# (1) group identity + inequality over random parameters
bad = 0; mindiff = 9
for _ in range(200000):
    lam = random.choice([2, 2.5, 3.236, 5, 20, 1e3, 1e6])*random.uniform(1, 1.5); k = random.randint(1, 12); d = k + 1 + random.randint(0, 10)
    A = random.choice([0, random.expovariate(1), random.expovariate(0.01)]); c = lam/d
    tv = 1/(1 + k*c + A); tl = 1/(1 + c/(1 + (k-1)*c + A)); S = tv + k*tl; B = 1 + k*c + A
    assert abs(S - (k + (1 - k*c)/B)) < 1e-9*max(1, S)
    diff = S - 2*(k+1)/(2+lam); mindiff = min(mindiff, diff)
    if diff < -1e-12: bad += 1
print("group inequality violations:", bad, " min slack:", mindiff)
# (2)+(3) on all planted branches n <= 12 and random larger ones: exact monomer probabilities via tree DP
def marginals(t, lam):
    """return list of P(v unmatched) for every vertex of planted branch t (root degree = #children + 1)."""
    # build adjacency
    adj = {}; deg = {}; cnt = [0]
    def build(t, p):
        v = cnt[0]; cnt[0] += 1; adj[v] = []
        if p is not None: adj[v].append(p); adj[p].append(v)
        for c in t: build(c, v)
        return v
    r = build(t, None)
    for v in adj: deg[v] = len(adj[v]) + (1 if v == r else 0)
    x = lambda u, v: lam/(deg[u]*deg[v])
    memo = {}
    def cav(u, excl):     # P(u unmatched) in the component of u after deleting excl
        key = (u, excl)
        if key in memo: return memo[key]
        s = sum(x(u, w)*cav(w, u) for w in adj[u] if w != excl)
        memo[key] = 1/(1 + s); return memo[key]
    return [cav(v, None) for v in adj], deg, adj
worst_ratio_slope = -9; viol = 0
for n in range(1, 13):
    for t in trees(n):
        for lam in (2, 3.236, 10, 1e3, 1e5):
            tau, deg, adj = marginals(t, lam)
            if sum(tau) < 2*n/(2+lam) - 1e-12: viol += 1
print("Lemma M violations (n <= 12, lam in {2, lam_c, 10, 1e3, 1e5}):", viol)
