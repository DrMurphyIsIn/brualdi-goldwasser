#!/usr/bin/env python3
"""Certificates for R3Cert.BGSpiderRule.CandProp 492 (spider certificate, part L2, 2026-09-25).

A candidate (Cand) is fixed by its counts (C, k4, k5, k6): C <= 8 cherries, k4 <= 10 arms of 4, k6 <= 10 arms
of 6, k4*k6 = 0, and k5 arms of 5, with n - 1 = 2C + 9k4 + 11k5 + 13k6.  Its residue class is
s = 6(n-1) mod 11 = (C - k4 + k6) mod 11, and the rule winner W(n) = (0, w4, w5, w6) is fixed by s (and, for
s = 3, 4, by n <= 722 / n <= 2319).  Per (combo, regime), k5 - w5 = delta is a constant, so with
m = min(k5, w5), k5 = m + k1, w5 = m + k2, the comparison F(combo) <= F(W) is the sign of the quadratic

    P(x) = A2 (D2 + R2) D1 - A1 (D1 + R1) D2          (x = m; see BGSpiderCandBase.P)

on the integer range L <= m (<= U) forced by n >= 492 and the regime.  A certificate is either
  * mono: P(L + t) = c0 + c1 t + c2 t^2 with c0, c1, c2 >= 0, or
  * bern: P(L + t) = b0 (T-t)^2 + b1 t (T-t) + b2 t^2 with b0, b1, b2 >= 0 and T = U - L.
Everything is exact (fractions.Fraction).  The script re-checks every certificate (the polynomial identity by
coefficients, the signs, the range bookkeeping against the rule), cross-checks CandProp by brute force for
n in 492..3000, and with --emit writes the Lean files

    proof/formalization/R3Cert/BGSpiderCandCells{C}.lean   (C = 0..8)
    proof/formalization/R3Cert/BGSpiderCand.lean

Usage:  python3 bg_spider_cand_certs.py            # check only
        python3 bg_spider_cand_certs.py --emit     # check and write the Lean files
"""
import os
import sys
from fractions import Fraction as Fr

G = {4: Fr(513, 80), 5: Fr(621, 64), 6: Fr(6561, 448)}
B = {4: Fr(3, 19), 5: Fr(3, 23), 6: Fr(1, 9)}
for j in (4, 5, 6):
    assert G[j] == Fr(3, 2) ** j * Fr(4 * j + 3, 3 * (j + 1)) and B[j] == Fr(3, 4 * j + 3)

N0 = 492
COMBOS = [(c, a, d) for c in range(9) for (a, d) in [(a, 0) for a in range(11)] + [(0, d) for d in range(1, 11)]]


def sres(n):
    return (6 * (n - 1)) % 11


def w_rule(n):
    """(w4, w6) exactly as BGSpiderRule.w4 / w6."""
    s = sres(n)
    if s == 0:
        return 0, 0
    if s <= 4 and not ((s == 3 and n <= 722) or (s == 4 and n <= 2319)):
        return 0, s
    return 11 - s, 0


def regimes(s):
    """(kind, w4, w6, n_lo, n_hi) covering all n >= N0 in class s."""
    if s == 0:
        return [("zero", 0, 0, N0, None)]
    if s in (1, 2):
        return [("six", 0, s, N0, None)]
    if s == 3:
        return [("four", 8, 0, N0, 722), ("six", 0, 3, 723, None)]
    if s == 4:
        return [("four", 7, 0, N0, 2319), ("six", 0, 4, 2320, None)]
    return [("four", 11 - s, 0, N0, None)]


def Phi(c, a, b, d):
    return Fr(3, 2) ** c * G[4] ** a * G[5] ** b * G[6] ** d * (
        1 + (Fr(c, 3) + a * B[4] + b * B[5] + d * B[6]) / (c + a + b + d))


def P(c, a, d, k1, w4, w6, k2, x):
    A1 = Fr(3, 2) ** c * G[4] ** a * G[5] ** k1 * G[6] ** d
    A2 = G[4] ** w4 * G[5] ** k2 * G[6] ** w6
    D1 = c + a + d + k1 + x
    R1 = Fr(c, 3) + a * B[4] + d * B[6] + (k1 + x) * B[5]
    D2 = w4 + w6 + k2 + x
    R2 = w4 * B[4] + w6 * B[6] + (k2 + x) * B[5]
    return A2 * (D2 + R2) * D1 - A1 * (D1 + R1) * D2


def build():
    certs = []
    for (c, a, d) in COMBOS:
        s = (c - a + d) % 11
        base = 2 * c + 9 * a + 13 * d
        assert (6 * base) % 11 == s
        for ri, (kind, w4, w6, nlo, nhi) in enumerate(regimes(s)):
            wb = 9 * w4 + 13 * w6
            assert (wb - base) % 11 == 0
            delta = (wb - base) // 11  # k5 - w5
            k1, k2 = max(delta, 0), max(-delta, 0)
            # n - 1 = base + 11 (m + k1);  n >= nlo  <=>  m >= L ;  n <= nhi  <=>  m <= U
            L = max(0, -(-(nlo - 1 - base - 11 * k1) // 11))
            U = None if nhi is None else (nhi - 1 - base - 11 * k1) // 11
            assert L >= 1 and (U is None or U >= L)
            # coefficients of P(L + t) (degree <= 2)
            p = [P(c, a, d, k1, w4, w6, k2, Fr(L + i)) for i in range(4)]
            c2 = (p[2] - 2 * p[1] + p[0]) / 2
            c1 = p[1] - p[0] - c2
            c0 = p[0]
            assert p[3] == c0 + 3 * c1 + 9 * c2  # really degree <= 2
            cert = dict(c=c, a=a, d=d, s=s, ri=ri, kind=kind, w4=w4, w6=w6, nlo=nlo, nhi=nhi,
                        k1=k1, k2=k2, L=L, U=U)
            if c0 >= 0 and c1 >= 0 and c2 >= 0:
                cert.update(shape="mono", coef=(c0, c1, c2))
            else:
                assert U is not None, ("unbounded range needs mono", cert)
                T = U - L
                b0 = c0 / T ** 2
                b1 = (c1 * T + 2 * c0) / T ** 2
                b2 = (c0 + c1 * T + c2 * T * T) / T ** 2
                assert b0 >= 0 and b1 >= 0 and b2 >= 0, ("certificate fails", cert)
                cert.update(shape="bern", coef=(b0, b1, b2), T=T)
            certs.append(cert)
    return certs


def check(certs):
    for ct in certs:
        c, a, d, k1, k2, w4, w6, L = ct["c"], ct["a"], ct["d"], ct["k1"], ct["k2"], ct["w4"], ct["w6"], ct["L"]
        e0, e1, e2 = ct["coef"]
        for t in range(-3, 4):  # identity of two quadratics at 7 points
            t = Fr(t)
            lhs = P(c, a, d, k1, w4, w6, k2, L + t)
            if ct["shape"] == "mono":
                rhs = e0 + e1 * t + e2 * t * t
            else:
                T = ct["T"]
                rhs = e0 * (T - t) ** 2 + e1 * t * (T - t) + e2 * t * t
            assert lhs == rhs
        assert min(ct["coef"]) >= 0
        # range bookkeeping: every m in range gives an n in the regime with the right rule winner
        base = 2 * c + 9 * a + 13 * d
        mt = [L, L + 1] + ([ct["U"] - 1, ct["U"]] if ct["U"] is not None else [L + 1000])
        for m in mt:
            n = 1 + base + 11 * (m + k1)
            assert n >= ct["nlo"] and (ct["nhi"] is None or n <= ct["nhi"])
            assert w_rule(n) == (w4, w6) and (n - 1 - 9 * w4 - 13 * w6) // 11 == m + k2
            assert Phi(c, a, m + k1, d) <= Phi(0, w4, m + k2, w6)
        n = 1 + base + 11 * (L - 1 + k1)
        assert n < ct["nlo"]
        if ct["U"] is not None:
            assert 1 + base + 11 * (ct["U"] + 1 + k1) > ct["nhi"]
    # brute force
    for n in range(N0, 3001):
        w4, w6 = w_rule(n)
        fw = Phi(0, w4, (n - 1 - 9 * w4 - 13 * w6) // 11, w6)
        for (c, a, d) in COMBOS:
            r = n - 1 - 2 * c - 9 * a - 13 * d
            if r >= 0 and r % 11 == 0:
                assert Phi(c, a, r // 11, d) <= fw, (n, c, a, d)


def q(x):
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


def nexpr(c, a, d, b="b"):
    return f"1 + 2 * {c} + 9 * {a} + 11 * {b} + 13 * {d}"


def cert_name(ct):
    return f"cert_{ct['c']}_{ct['a']}_{ct['d']}_{ct['ri']}"


def emit_cert(ct):
    c, a, d, k1, k2, w4, w6, L = ct["c"], ct["a"], ct["d"], ct["k1"], ct["k2"], ct["w4"], ct["w6"], ct["L"]
    e0, e1, e2 = ct["coef"]
    hyps = f"(hm : {L} ≤ m)" + (f" (hmU : m ≤ {ct['U']})" if ct["U"] is not None else "")
    out = [f"theorem {cert_name(ct)} (m : ℕ) {hyps} :",
           f"    Φ {c} {a} (m + {k1}) {d} ≤ Φ 0 {w4} (m + {k2}) {w6} := by",
           f"  apply Φ_le_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)"]
    if ct["shape"] == "mono":
        rhs = f"{q(e0)} + {q(e1)} * t + {q(e2)} * t ^ 2"
    else:
        T = ct["T"]
        rhs = f"{q(e0)} * ({T} - t) ^ 2 + {q(e1)} * (t * ({T} - t)) + {q(e2)} * t ^ 2"
    out += [f"  have key : ∀ t : ℚ, P {c} {a} {d} {k1} {w4} {w6} {k2} ({L} + t) =",
            f"      {rhs} := by",
            f"    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring",
            f"  have hm' : ({L} : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm",
            f"  have e := key ((m : ℚ) - {L})",
            f"  rw [show ({L} : ℚ) + ((m : ℚ) - {L}) = m by ring] at e",
            f"  rw [e]"]
    if ct["shape"] == "mono":
        out += [f"  exact mono_nonneg (by norm_num) (by norm_num) (by norm_num) (by linarith)"]
    else:
        out += [f"  have hmU' : (m : ℚ) ≤ ({ct['U']} : ℚ) := by exact_mod_cast hmU",
                f"  exact bern_nonneg (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)"]
    return "\n".join(out) + "\n"


def emit_regime(ct, indent):
    c, a, d, k1, k2, w4, w6, s = ct["c"], ct["a"], ct["d"], ct["k1"], ct["k2"], ct["w4"], ct["w6"], ct["s"]
    # with k1 = 0 keep the variable `b` (a `rfl` on `b = m + 0` would eliminate `m` instead)
    v = "b" if k1 == 0 else "m"
    n = nexpr(c, a, d, "b" if k1 == 0 else f"(m + {k1})")
    p = " " * indent
    if ct["kind"] == "zero":
        hw = "w_zero _ hs"
    elif ct["kind"] == "six":
        hw = f"w_six _ {s} hs (by omega) (by omega) (by omega)"
    else:
        hw = f"w_four _ {s} hs (by omega) (by omega)"
    hyps = "(by omega)" + (" (by omega)" if ct["U"] is not None else "")
    out = [f"{p}have hw := {hw}"]
    if k1 != 0:
        out.append(f"{p}obtain ⟨m, rfl⟩ : ∃ m, b = m + {k1} := by exact ⟨b - {k1}, by omega⟩")
    out += [f"{p}have h4 : w4 ({n}) = {w4} := by have := hw.1; omega",
            f"{p}have h6 : w6 ({n}) = {w6} := by have := hw.2; omega",
            f"{p}have h5 : w5 ({n}) = {v} + {k2} := by unfold w5; rw [h4, h6]; omega",
            f"{p}rw [h4, h5, h6]",
            f"{p}exact {cert_name(ct)} {v} {hyps}"]
    return out


def emit_combo(cts):
    c, a, d, s = cts[0]["c"], cts[0]["a"], cts[0]["d"], cts[0]["s"]
    n = nexpr(c, a, d)
    out = [f"theorem combo_{c}_{a}_{d} (b : ℕ) (hn : 492 ≤ {n}) :",
           f"    Φ {c} {a} b {d} ≤ Φ 0 (w4 ({n})) (w5 ({n})) (w6 ({n})) := by",
           f"  have hs : sres ({n}) = {s} := by unfold sres; omega"]
    if len(cts) == 1:
        out += emit_regime(cts[0], 2)
    else:
        out += [f"  rcases Nat.lt_or_ge ({n}) {cts[0]['nhi'] + 1} with hlo | hhi"]
        for ct in cts:
            lines = emit_regime(ct, 4)
            lines[0] = "  · " + lines[0].lstrip()
            out += lines
    return "\n".join(out) + "\n"


HEADER_CELLS = """/-
  R3Cert.BGSpiderCandCells{C} -- GENERATED by proof/verification/bg_spider_cand_certs.py; do not edit.

  Per-combo certificates for `CandProp 492` with {C} cherries at the centre: for each (k4, k6) the
  comparison `Φ C k4 k5 k6 ≤ F (W n)` for every n >= 492 in the combo's residue class.
-/
import Mathlib
import R3Cert.BGSpiderCandBase

namespace R3Cert
namespace BGSpiderCand

open BGSpiderOpt BGSpiderRule

"""


def emit(certs, root):
    by_combo = {}
    for ct in certs:
        by_combo.setdefault((ct["c"], ct["a"], ct["d"]), []).append(ct)
    for C in range(9):
        body = [HEADER_CELLS.replace("{C}", str(C))]
        for (c, a, d) in COMBOS:
            if c != C:
                continue
            for ct in by_combo[(c, a, d)]:
                body.append(emit_cert(ct) + "\n")
            body.append(emit_combo(by_combo[(c, a, d)]) + "\n")
        body.append("end BGSpiderCand\nend R3Cert\n")
        with open(os.path.join(root, f"R3Cert/BGSpiderCandCells{C}.lean"), "w") as f:
            f.write("".join(body))
    # dispatcher + main theorem
    n = nexpr("c", "a", "d")
    lines = ["""/-
  R3Cert.BGSpiderCand -- GENERATED by proof/verification/bg_spider_cand_certs.py; do not edit.

  **`candProp_492 : CandProp 492`** (spider certificate, part L2, 2026-09-25): inside the bounded candidate
  set `Cand` (<= 8 cherries, arms of 4/5/6 only, never both 4- and 6-arms, <= 10 of each), the rule winner
  `W n` maximizes `F` at every size `n >= 492`.

  A candidate is fixed by its counts (C, k4, k5, k6); `F_eq_Φ` gives `F` in closed form `Φ` from the counts.
  The 189 combos (C, k4, k6) are dispatched to `combo_C_k4_k6` (files `BGSpiderCandCells{C}`), each of which
  reads off the residue class and the rule winner and applies a quadratic certificate: 223 certificates
  (221 with nonnegative coefficients in t = m - L on [L, oo), 2 Bernstein on a bounded range).
  Exact rational arithmetic; no `sorry`, no `native_decide`; axioms propext, Classical.choice, Quot.sound.
-/
import Mathlib
"""]
    lines += [f"import R3Cert.BGSpiderCandCells{C}\n" for C in range(9)]
    lines += ["""
namespace R3Cert
namespace BGSpiderCand

open BGSpiderOpt BGSpiderRule

/-- The count-level statement: every combo loses to (or equals) the rule winner. -/
"""]
    lines += [f"""theorem cand_counts (c a b d : ℕ) (hc : c ≤ 8) (ha : a ≤ 10) (hd : d ≤ 10) (had : a = 0 ∨ d = 0)
    (hn : 492 ≤ {n}) :
    Φ c a b d ≤ Φ 0 (w4 ({n})) (w5 ({n})) (w6 ({n})) := by
  rcases had with rfl | rfl
  · interval_cases c
"""]
    for C in range(9):
        lines.append("    · interval_cases d\n")
        for D in range(11):
            lines.append(f"      · exact combo_{C}_0_{D} b hn\n")
    lines.append("  · interval_cases c\n")
    for C in range(9):
        lines.append("    · interval_cases a\n")
        for A in range(11):
            lines.append(f"      · exact combo_{C}_{A}_0 b hn\n")
    lines.append("""
/-- **`CandProp 492`.**  Inside `Cand`, the rule winner `W n` is optimal at every size `n ≥ 492`. -/
theorem candProp_492 : CandProp 492 := by
  intro l hl hcand
  obtain ⟨hC, hmem, h46, ha, hd⟩ := hcand
  have hadm : Adm l := hmem
  have had : c4 l = 0 ∨ c6 l = 0 := by
    rcases Nat.eq_zero_or_pos (c4 l) with h | h
    · exact Or.inl h
    · refine Or.inr (Nat.eq_zero_of_not_pos fun h' => h46 ?_)
      exact ⟨List.count_pos_iff.mp h, List.count_pos_iff.mp h'⟩
  have hnv := nv_eq l hadm
  rw [F_eq_Φ l hadm, F_W_eq, hnv]
  rw [hnv] at hl
  exact cand_counts _ _ _ _ hC ha hd had hl

end BGSpiderCand
end R3Cert
""")
    with open(os.path.join(root, "R3Cert/BGSpiderCand.lean"), "w") as f:
        f.write("".join(lines))


def main():
    certs = build()
    check(certs)
    mono = sum(1 for ct in certs if ct["shape"] == "mono")
    print(f"combos: {len(COMBOS)}  certificates: {len(certs)}  (mono {mono}, bern {len(certs) - mono})")
    for ct in certs:
        if ct["shape"] == "bern":
            print("  bern:", {k: ct[k] for k in ("c", "a", "d", "s", "w4", "w6", "L", "U")})
    print("all certificates re-checked exactly; brute force n = 492..3000 agrees: CandProp 492 certified")
    if "--emit" in sys.argv:
        root = os.environ.get("BG_FORMAL_ROOT") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "formalization")
        emit(certs, root)
        print("Lean files written under", os.path.normpath(root))


if __name__ == "__main__":
    main()
