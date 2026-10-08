"""Direct exact sweep over spiders, 4 <= n <= NMAX (default 491), compared with the hull computation.

A spider is a center whose children are leaves (A_0), cherries (C) and arms A_j (a vertex carrying j
cherries).  With C cherries and k_j arms A_j,
    n = 1 + 2C + sum_j k_j (2j+1),   D = C + sum_j k_j  (center degree),
    pi = (3/2)^C prod_j ((3/2)^j alpha_j)^{k_j} * (1 + R/D),
    alpha_j = (4j+3)/(3(j+1)),  R = C/3 + sum_j k_j * 3/(4j+3).
By the balance exchange (Lemma bgx-balance), a best spider with D >= 3 has all arm sizes (leaves counted
as A_0) in {s, s+1}; it is then determined by C and the number m of arms.  For every n the program
enumerates (i) all configurations with D <= 2 and (ii) all balanced configurations with D >= 3, takes the
maximum of pi, and compares it, and the set of maximizers, with the exact hull computation
(../results_dp_491.txt: the value M_n and its maximizers, which agree with the table of the appendix).
Maximizers are compared as trees up to isomorphism (canonical AHU encoding).

Arithmetic: a float log-prefilter (margin 1e-9) selects the candidates near the float maximum; all of
them are evaluated and compared in exact Fraction arithmetic.  The prefilter is not certified, so this
sweep is a confirmation, not a proof.

Adapted in October 2026, as a single-process program, from an earlier multi-process sweep over the same
family (same formulas and enumeration); the counts and the comparison with the table are new.
Usage: python3 spider_sweep.py [NMAX]
"""
import os, re, sys, math, time
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
H = Fr(3, 2)
LN15 = math.log(1.5)
_LA = [j * LN15 + math.log((4 * j + 3) / (3 * (j + 1))) for j in range(0, 1000)]
_B = [3 / (4 * j + 3) for j in range(0, 1000)]
MARGIN = 1e-9


def alpha(j):
    return Fr(4 * j + 3, 3 * (j + 1))


def F_exact(C, arms):
    D = C + sum(arms.values())
    G = H ** C
    R = Fr(C, 3)
    for j, k in arms.items():
        G *= (H ** j * alpha(j)) ** k
        R += k * Fr(3, 4 * j + 3)
    return G * (1 + R / D)


def label(C, arms):
    """Notation of ../results_dp_491.txt, e.g. 'C^5 A5^4 A4^5', 'C A0'."""
    parts = []
    if C:
        parts.append("C" if C == 1 else f"C^{C}")
    for j in sorted(arms, reverse=True):
        k = arms[j]
        if k:
            parts.append(f"A{j}" if k == 1 else f"A{j}^{k}")
    return " ".join(parts)


def parse_label(lab):
    C, arms = 0, {}
    for tok in lab.split():
        base, _, e = tok.partition("^")
        k = int(e) if e else 1
        if base == "C":
            C += k
        else:
            arms[int(base[1:])] = arms.get(int(base[1:]), 0) + k
    return C, arms


def build_tree(C, arms):
    adj = [[]]

    def new(p):
        adj.append([p]); adj[p].append(len(adj) - 1)
        return len(adj) - 1

    for _ in range(C):
        new(new(0))
    for j, k in sorted(arms.items()):
        for _ in range(k):
            a = new(0)
            for _ in range(j):
                new(new(a))
    return adj


def canon(adj):
    """Canonical string of an unrooted tree (AHU encoding rooted at the center or bicenter)."""
    n = len(adj)
    deg = [len(a) for a in adj]
    layer = [v for v in range(n) if deg[v] <= 1]
    left = n
    while left > 2:
        left -= len(layer)
        nxt = []
        for v in layer:
            for w in adj[v]:
                deg[w] -= 1
                if deg[w] == 1:
                    nxt.append(w)
        layer = nxt

    def enc(v, p):
        return "(" + "".join(sorted(enc(w, v) for w in adj[v] if w != p)) + ")"
    return min(enc(c, -1) for c in layer)


def configs_D_le_2(n):
    out = []
    N = n - 1
    types = [('P', 2)] + [(j, 2 * j + 1) for j in range(0, N + 1) if 2 * j + 1 <= N]
    for t, c in types:
        if c == N:
            out.append((1, {}) if t == 'P' else (0, {t: 1}))
    for i, (t1, c1) in enumerate(types):
        for t2, c2 in types[i:]:
            if c1 + c2 == N:
                C = (t1 == 'P') + (t2 == 'P')
                arms = {}
                for t in (t1, t2):
                    if t != 'P':
                        arms[t] = arms.get(t, 0) + 1
                out.append((C, arms))
    return out


def balanced(n):
    """Every balanced configuration with D >= 3: (float log pi, C, arms)."""
    out = []
    for C in range(0, (n - 1) // 2 + 1):
        V = n - 1 - 2 * C
        if V == 0:
            if C >= 3:
                out.append((C * LN15 + math.log1p((C / 3) / C), C, {}))
            continue
        for m in range(1, V + 1):
            if (V - m) % 2 or C + m < 3:
                continue
            J = (V - m) // 2
            s, t = divmod(J, m)
            arms = {}
            if m - t:
                arms[s] = m - t
            if t:
                arms[s + 1] = arms.get(s + 1, 0) + t
            D = C + m
            R = C / 3 + (m - t) * _B[s] + t * _B[s + 1]
            v = C * LN15 + (m - t) * _LA[s] + t * _LA[s + 1] + math.log1p(R / D)
            out.append((v, C, arms))
    return out


def flog(C, arms):
    D = C + sum(arms.values())
    R = C / 3 + sum(k * _B[j] for j, k in arms.items())
    return C * LN15 + sum(k * _LA[j] for j, k in arms.items()) + math.log1p(R / D)


def load_table(fn):
    tab = {}
    for line in open(fn):
        m = re.match(r'n=(\d+) M=(\d+)/(\d+) .*count=(\d+) maximizers: (.*?)( table=| \|H_n\|)', line)
        if m:
            n = int(m.group(1))
            tab[n] = (Fr(int(m.group(2)), int(m.group(3))), sorted(x.strip() for x in m.group(5).split("|")))
    return tab


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 491
    tab = load_table(os.path.join(HERE, "..", "results_dp_491.txt"))
    t0 = time.time()
    tot_bal = tot_d2 = max_bal = 0
    max_bal_n = None
    bad = []
    for n in range(4, NMAX + 1):
        d2 = [(flog(C, a), C, a) for C, a in configs_D_le_2(n)]
        bal = balanced(n)
        tot_d2 += len(d2); tot_bal += len(bal)
        if len(bal) > max_bal:
            max_bal, max_bal_n = len(bal), n
        allc = d2 + bal
        fmax = max(v for v, _, _ in allc)
        exact = [(F_exact(C, a), label(C, a), C, a) for v, C, a in allc if v >= fmax - MARGIN]
        top = max(e[0] for e in exact)
        # maximizers up to isomorphism (a spider with one leaf and one arm can be read at two centers)
        classes = {}
        for e, l, C, a in exact:
            if e == top:
                classes.setdefault(canon(build_tree(C, a)), []).append((C + sum(a.values()), l))
        # print each class by its reading with the largest center degree
        winners = sorted(max(ls)[1] for ls in classes.values())
        status = "no table entry"
        if n in tab:
            tclasses = set(canon(build_tree(*parse_label(l))) for l in tab[n][1])
            ok = (tab[n][0] == top and tclasses == set(classes) and len(tab[n][1]) == len(classes))
            status = "MATCH" if ok else "MISMATCH"
            if not ok:
                bad.append((n, winners, tab[n][1]))
        print(f"n={n} spiders: D<=2 {len(d2)}, balanced D>=3 {len(bal)}; max pi = {float(top):.12g} "
              f"maximizers: {' | '.join(winners)} (up to isomorphism: {len(classes)}) {status}", flush=True)
    print(f"# balanced spiders with D>=3, 4<=n<={NMAX}: {tot_bal} (at most {max_bal} for one n, at n={max_bal_n})")
    print(f"# spiders with D<=2, 4<=n<={NMAX}: {tot_d2}")
    print(f"# compared with ../results_dp_491.txt: {sum(1 for n in range(4, NMAX + 1) if n in tab)} values of n, "
          f"mismatches: {len(bad)}")
    for b in bad:
        print("# MISMATCH", b)
    print("# RESULT:", "PASS" if not bad else "FAIL")
    print(f"# time {time.time() - t0:.0f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
