"""Rigorous check of Lemma nu-stab-cv (matching number: finite range of the stability comparison).
Arb ball arithmetic (python-flint, 256 bits); exact rationals for F_k(n,a).
Run with OMP_NUM_THREADS=1."""
from fractions import Fraction as Fr
from flint import arb, ctx

ctx.prec = 256


def A(q):
    return arb(q.numerator) / arb(q.denominator)


def t(l):
    return Fr(4 * l + 3, 2 * l + 2)


def Fmax(n, k):
    """max over a of F_k(n,a), balanced legs l_i >= 1, n = 1 + a + sum(l_i + 2)."""
    best = None
    for a in range(0, n - 3 * k + 3):
        L = n - 1 - a - 2 * (k - 1)
        q, r = divmod(L, k - 1)
        if q < 1:
            continue
        ls = [q + 1] * r + [q] * (k - 1 - r)
        P = Fr(1)
        for l in ls:
            P *= t(l)
        val = P * (2 - Fr(1, a + k - 1) * sum(Fr(2 * l + 2, 4 * l + 3) for l in ls))
        if best is None or val > best:
            best = val
    return best


def cases(k):
    m = k - 1
    out = [((arb(m) + arb(m + 1).sqrt()) ** 2 / 4, m)]
    if k >= 3:
        s2 = arb(2).sqrt()
        Aa = arb(k - 3) / s2 + 2 * (arb(2) / 3).sqrt() + (arb(3 * k - 5) / 6).sqrt()
        Bb = arb(k - 2) / s2 + (arb(2) / 3).sqrt() + (arb(3 * k - 4) / 6).sqrt()
        if Aa < Bb:
            sig = Aa
        elif Bb < Aa:
            sig = Bb
        else:
            raise SystemExit("undecided min at k=%d" % k)
        out.append((sig ** 2 / 2, 0))
    return out


N1tab = {2: 10, 3: 255, 4: 322, 5: 464, 6: 655, 7: 894, 8: 1184, 9: 1526, 10: 1924}
n0tab = {2: 4, 3: 24, 4: 32, 5: 60, 6: 99, 7: 149, 8: 211, 9: 289, 10: 380}
allok = True
for k in range(2, 11):
    m = k - 1
    sm = arb(m).sqrt()
    K = (arb(m) + sm) ** 2
    E = (arb(m) / 3 + sm / 11) * K
    roots = []
    for (c, s) in cases(k):
        a2 = c - K / 4
        a1 = -(K * s / 4 + c * c / 2 + E)
        a0 = -E * s
        assert a2 > 0
        roots.append((-a1 + (a1 * a1 - 4 * a2 * a0).sqrt()) / (2 * a2))
    extra = max(float((4 * (m + sm)).upper()), float((sm * (m + sm)).upper()))
    N1 = N1tab[k]
    okN1 = all(arb(N1) > r for r in roots) and N1 >= extra
    fails, undecided, minrel, argmin = [], [], None, None
    for n in range(3 * k - 2, N1 + 2):
        N = n - 1
        F = A(Fmax(n, k))
        fail = False
        for (c, s) in cases(k):
            B = arb(2) ** k * (1 - c / (k * (N + s))) ** k
            d = F - B
            if d > 0:
                rel = float((d / B).lower())
                if n > n0tab[k] and (minrel is None or rel < minrel):
                    minrel, argmin = rel, n
            elif d < 0:
                fail = True
            else:
                undecided.append(n)
        if fail:
            fails.append(n)
    exact = fails == list(range(3 * k - 2, n0tab[k] + 1))
    allok &= exact and okN1 and not undecided
    print(f"k={k}: largest roots <= {[round(float(r.upper()), 2) for r in roots]}, "
          f"size term {extra:.2f}, N1={N1} valid={okN1}; failures n={fails[0] if fails else None}.."
          f"{fails[-1] if fails else None} ({len(fails)}), equals [3k-2, n0]: {exact}; "
          f"undecided: {undecided}; min rel margin for n>n0: {minrel:.3e} at n={argmin}")
print("ALL OK" if allok else "MISMATCH")
