"""Independent checker for the bounded-degree Bellman certificates.

Written from the mathematical statement only (does not import or copy verify.py / upper.py).

Statement checked.  For a planted branch R with children messages x_1..x_c (c <= Delta-1),
  Z(R)(1 + b x(R)) = prod Z(R_i) * (c+1+b+S)/(c+1),  x(R) = 1/(c+1+S).
With h(x) = +log(1 + b x) + k(type) and g(R) = lam |R| - log Z(R):
  g(R) - h(x(R)) = sum_i (g(R_i) - h(x_i)) + [lam + sum k_i - k_parent - G_c(x)],
  G_c(x) = log((c+1+b+S)/(c+1)) - sum log(1 + b x_i).
Needed: bracket >= 0 for every achievable configuration (c = 0: the leaf).
Corner lemma (proved in the paper): for fixed other coordinates G_c is monotone in x_i,
so sup over a box is attained at a vertex; we evaluate every vertex in Arb.
Types: L (leaf), K (cherry), C5 (five cherries, if listed), else interval containing x.
Rules: every multiset of 1..Delta-1 child types; targets = all interval types meeting the exact
parent range [1/(c+1+Smax), 1/(c+1+Smin)], except {L}->K and {5K}->C5 (identity branches).
Coverage of the parent range by the target intervals is checked exactly.
Spine rules ((Delta-2) K + port I) at the exact lambda: bracket = k_I - k_t + E, E == 0 identically
(Lemma spine identity, see the paper); used only as fallback when corner check is not > 0,
and E is also checked to contain 0 at the corners.
"""
import json, sys, itertools
from fractions import Fraction as F
import flint
from flint import arb

flint.ctx.prec = 300


def A(q):
    q = F(q)
    return arb(q.numerator) / arb(q.denominator)


def exact_params(D):
    s = arb(( 2 * D - 1) ** 2 + 9).sqrt()
    b = (s - (2 * D - 1)) / 3
    mu = arb(3) ** (D - 2) / arb(2) ** (D - 2) * ((2 * D - 1) + s) / (3 * D)
    lam = mu.log() / (2 * D - 3)
    return lam, b, mu


def G(c, xs, b):
    S = sum(xs, arb(0))
    val = (c + 1 + b + S).log() - arb(c + 1).log()
    for x in xs:
        val -= (1 + b * x).log()
    return val


def check(D, lam, b, types, k, exact_mode, label):
    names = [t[0] for t in types]
    lo = {t[0]: F(t[1]) for t in types}
    hi = {t[0]: F(t[2]) for t in types}
    singles = {"L", "K", "C5"}
    intervals = [n for n in names if n not in singles]
    has_C5 = "C5" in names
    # windows coverage sanity
    Bw = (F(1, 2 * D - 1), F(2 * D - 1, 6 * D - 1))
    Aw = (F(2, 5), F(2 * D - 1, 4 * D - 1))
    out = []
    fails = 0
    worst = None
    worst_ng = [1e9]
    nrules = 0
    nchain = 0
    # c = 0 (leaf) base
    s0 = lam - k["L"] - (1 + b).log()
    if exact_mode:
        ok0 = True  # k_L defined as equality
    else:
        ok0 = s0 > 0
    if not ok0:
        fails += 1
        out.append("FAIL leaf base slack %s" % s0.str(5))
    for c in range(1, D):
        for ms in itertools.combinations_with_replacement(names, c):
            ms = list(ms)
            Smin = sum((lo[t] for t in ms), F(0))
            Smax = sum((hi[t] for t in ms), F(0))
            plo, phi = F(1) / (c + 1 + Smax), F(1) / (c + 1 + Smin)
            if ms == ["L"]:
                targets = ["K"]
            elif has_C5 and c == 5 and ms == ["K"] * 5:
                targets = ["C5"]
            else:
                targets = [t for t in intervals if not (hi[t] < plo or lo[t] > phi)]
                # exact coverage of [plo, phi] by the chosen targets
                segs = sorted((lo[t], hi[t]) for t in targets)
                cur = plo
                for a_, b_ in segs:
                    if a_ > cur:
                        break
                    cur = max(cur, b_)
                if cur < phi or not segs or segs[0][0] > plo:
                    fails += 1
                    out.append("FAIL coverage %s range [%s,%s]" % ("+".join(ms), plo, phi))
            # corners up to permutation: for a type of multiplicity m choose how many copies sit at hi
            per_type = []
            for t in sorted(set(ms)):
                m = ms.count(t)
                if lo[t] == hi[t]:
                    per_type.append([[lo[t]] * m])
                else:
                    per_type.append([[lo[t]] * (m - j) + [hi[t]] * j for j in range(m + 1)])
            corners = [sum(p, []) for p in itertools.product(*per_type)]
            Gs = [G(c, [A(v) for v in cn], b) for cn in corners]
            ksum = sum((k[t] for t in ms), arb(0))
            is_chain = exact_mode and c == D - 1 and ms.count("K") >= D - 2
            for tgt in targets:
                nrules += 1
                identity = (ms == ["L"]) or (tgt == "C5" and ms == ["K"] * 5)
                slacks = [lam + ksum - k[tgt] - g for g in Gs]
                mn = min(slacks, key=lambda z: float(z.mid()) - float(z.rad()))
                if identity and exact_mode:
                    if not all(z.contains(0) for z in slacks):
                        fails += 1
                        out.append("FAIL identity %s->%s %s" % ("+".join(ms), tgt, mn.str(5)))
                    continue
                if all(z > 0 for z in slacks):
                    lb = min(float(z.mid()) - float(z.rad()) for z in slacks)
                    if not (c == D - 1 and ms.count("K") >= D - 2):
                        worst_ng[0] = min(worst_ng[0], lb)
                    worst = lb if worst is None or lb < worst[0] else worst
                    if worst is not None and worst == lb:
                        worst = (lb, "+".join(ms) + "->" + tgt)
                    continue
                if is_chain:
                    # port = the non-K element (or K if all K)
                    rest = list(ms)
                    for _ in range(D - 2):
                        rest.remove("K")
                    port = rest[0]
                    E = [lam + (D - 2) * k["K"] - g for g in Gs]
                    if not all(z.contains(0) for z in E) or not all(abs(z) < arb(10) ** -60 for z in E):
                        fails += 1
                        out.append("FAIL chain identity %s" % "+".join(ms))
                        continue
                    diff = k[port] - k[tgt]
                    nchain += 1
                    if diff >= 0 or (port == tgt) or (k[port] is k[tgt]):
                        continue
                    fails += 1
                    out.append("FAIL chain %s->%s: k[%s]-k[%s]=%s" % ("+".join(ms), tgt, port, tgt, diff.str(5)))
                    continue
                fails += 1
                out.append("FAIL generic %s->%s min slack %s" % ("+".join(ms), tgt, mn.str(5)))
    # window coverage sanity for intervals
    bi = sorted((lo[t], hi[t]) for t in intervals if hi[t] < F(1, 3))
    ai = sorted((lo[t], hi[t]) for t in intervals if lo[t] > F(1, 3))
    cov = (bi[0][0] <= Bw[0] and bi[-1][1] >= Bw[1] and all(bi[i][1] >= bi[i + 1][0] for i in range(len(bi) - 1))
           and ai[0][0] <= Aw[0] and ai[-1][1] >= Aw[1] and all(ai[i][1] >= ai[i + 1][0] for i in range(len(ai) - 1)))
    if not cov:
        fails += 1
        out.append("FAIL window coverage")
    print("%s Delta=%d rules=%d (chain fallbacks %d) fails=%d worst generic lower bound=%s" % (
        label, D, nrules, nchain, fails, worst), flush=True)
    print("    min slack over non-spine-shaped multisets: %.4e" % worst_ng[0])
    for line in out[:30]:
        print("   ", line)
    return fails


def exact_k(D, lam, b, kstr, names):
    k = {}
    k["L"] = lam - (1 + b).log()
    k["K"] = 2 * lam - A(F(3, 2)).log() - (1 + b / 3).log()
    if "C5" in names:
        k["C5"] = lam + 5 * k["K"] - G(5, [A(F(1, 3))] * 5, b)
    for n, v in kstr.items():
        if v != "exact":
            k[n] = A(F(v))
    return k


if __name__ == "__main__":
    import os
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates") + os.sep
    total = 0
    # hand potentials Delta = 3, 4 as stated in the paper (lem:deg-cert34)
    for D, Bt, At, kA in [(3, ("1/5", "5/17"), ("2/5", "5/11"), "-0.0813"),
                          (4, ("1/7", "7/23"), ("2/5", "7/15"), "-0.0391")]:
        lam, b, mu = exact_params(D)
        types = [["L", "1", "1"], ["K", "1/3", "1/3"], ["B", Bt[0], Bt[1]], ["A", At[0], At[1]]]
        k = exact_k(D, lam, b, {}, ["L", "K", "B", "A"])
        k["B"] = k["K"]
        k["A"] = A(F(kA))
        total += check(D, lam, b, types, k, True, "tex-hand")
    for D in (5, 6, 7):
        c = json.load(open(base + "cert_D%d_K4.json" % D))
        lam, b, mu = exact_params(D)
        names = [t[0] for t in c["types"]]
        k = exact_k(D, lam, b, c["k"], names)
        total += check(D, lam, b, c["types"], k, True, "cert")
    if len(sys.argv) > 1 and sys.argv[1] == "upper":
        for D, f in [(8, "upper_D8_K4.json"), (9, "upper_D9_K3.json"), (10, "upper_D10_K3.json"),
                     (11, "upper_D11_K3.json"), (12, "upper_D12_K3.json")]:
            c = json.load(open(base + f))
            rp = F(c["rho_prime"]) if "rho_prime" in c else None
            lam = A(rp).log()
            b = A(F(c["b"]))
            names = [t[0] for t in c["types"]]
            k = {n: A(F(v)) for n, v in zip(names, c["k"])}
            print("  rho' =", float(rp))
            total += check(D, lam, b, c["types"], k, False, "upper")
    print("TOTAL FAILS", total)
