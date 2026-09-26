/-
  General-case infrastructure, piece 4: THE ASSEMBLY — `Φ ≤ 1` conditional on a tree-free inequality.

  `DeficitNonneg` is the classification-reduced per-node super-solution: a statement about three
  naturals and one real, with NO trees.  Via `classify_reduce` + `eroot_plain_node` + `cav_plain_node`
  it implies `ValidPotentialPlain Pval`, hence (telescoping + plainification, both machine-checked)
  `logPhi b ≤ 0` for EVERY branch — the Brualdi–Goldwasser conjecture.

  So after this file the ENTIRE remaining mathematical content of the conjecture is `DeficitNonneg`.

  Genuine proofs (no `sorry`).  `DeficitNonneg` itself is NOT proven here — it is the remaining crux
  (to be established in slices: `m = 0`, then `m ≥ 1` via the finite `(a, nl, m)` analysis).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.PlainFormula
import R3Cert.Potential
import R3Cert.PotentialBound
import R3Cert.PotentialReduce

namespace R3Cert

open Real

/-- **The remaining crux, tree-free.**  For all `a, nl, m : ℕ` (arm, leaf, generic-child counts) and
    `Sg ∈ [0, m/2]` (generic cavity mass):
    `−L + log(1 + S/(N+1)) + Pval(1/(N+1+S)) ≤ a·(−ω) + nl·L + (11/50)·(Sg − m·T0)₊`,
    where `S = a/3 + nl + Sg` and `N = a + nl + m`. -/
def DeficitNonneg : Prop :=
  ∀ (a nl m : ℕ) (Sg : ℝ), 0 ≤ Sg → Sg ≤ (m : ℝ) / 2 →
    -Lval + Real.log (1 + ((a : ℝ) / 3 + nl + Sg) / ((a : ℝ) + nl + m + 1))
        + Pval (1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg)))
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval
        + (11 / 50) * max 0 (Sg - (m : ℝ) * T0)

/-- The per-node super-solution at an arbitrary plain node, conditional on `DeficitNonneg`. -/
theorem superSol_of_deficit (hD : DeficitNonneg) (ch : List Branch) (hch : IsPlainList ch) :
    eroot 0 ch ≤ ((ch.map (fun b => Pval (cav b))).sum) - Pval (cav (Branch.node 0 ch)) := by
  obtain ⟨a, nl, m, Sg, hlen, hsum, hSg0, hSgh, hPle⟩ := classify_reduce ch hch
  have he : eroot 0 ch
      = -Lval + Real.log (1 + ((a : ℝ) / 3 + nl + Sg) / ((a : ℝ) + nl + m + 1)) := by
    rw [eroot_plain_node, hsum, hlen]
  have hc : cav (Branch.node 0 ch)
      = 1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg)) := by
    rw [cav_plain_node, hsum, hlen]
  have hkey := hD a nl m Sg hSg0 hSgh
  rw [he, hc]
  linarith [hkey, hPle]

/-- `DeficitNonneg` gives the full valid plain potential. -/
theorem validPlain_of_deficit (hD : DeficitNonneg) : ValidPotentialPlain Pval :=
  ⟨Pval_nonneg, fun ch hch => superSol_of_deficit hD ch hch⟩

/-- **Brualdi–Goldwasser conditional on the tree-free deficit inequality:** `DeficitNonneg`
    implies `logPhi b ≤ 0` (`Φ ≤ 1`) for EVERY branch. -/
theorem phi_le_one_of_deficitNonneg (hD : DeficitNonneg) (b : Branch) : logPhi b ≤ 0 :=
  phi_le_one_of_validPlain Pval (validPlain_of_deficit hD) b

end R3Cert
