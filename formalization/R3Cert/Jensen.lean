/-
  The Jensen reduction, formalized in Lean: the worst multi-child DEC node is the ALL-EQUAL node.

  A DEC node with `j` children of cavities `mu_l` and amplitudes `ell_l <= H(mu_l)` (H the concave hull of the
  amplitude menu) has amplitude at most `Q(s, j, mubar)`, the all-children-equal node at the mean cavity
  `mubar = (sum mu_l)/j`.  Two facts: (i) Jensen -- for concave `H`, `sum H(mu_l) <= j H(mubar)`; (ii) the
  log-coupling term depends on the children ONLY through `sum mu_l = j mubar`.  This is the concavity argument
  behind the finite sweep (`adversary_sweep.py`), now machine-checked.
-/
import Mathlib
import R3Cert.Sweep

namespace R3Cert

open Finset

/-- **Jensen (core):** for a concave `H`, the sum of `H` over the children is at most `j * H(mean)`. -/
theorem jensen_sum {j : ℕ} (hj : 0 < j) {I : Set ℝ} {H : ℝ → ℝ} (hH : ConcaveOn ℝ I H)
    (mu : Fin j → ℝ) (hmem : ∀ i, mu i ∈ I) :
    (∑ i, H (mu i)) ≤ (j : ℝ) * H ((∑ i, mu i) / j) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjr
  have hsum1 : (∑ _i : Fin j, (1 : ℝ) / j) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div, div_self hjne]
  have key := hH.le_map_sum (t := Finset.univ) (w := fun _ => (1 : ℝ) / j) (p := mu)
    (fun i _ => by positivity) hsum1 (fun i _ => hmem i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at key
  have hm : (1 / (j : ℝ)) * ∑ i, mu i = (∑ i, mu i) / j := by ring
  rw [hm] at key
  have hexp : (∑ i, H (mu i)) = (j : ℝ) * ((1 / j) * ∑ i, H (mu i)) := by field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left key (le_of_lt hjr)

/-- The DEC node amplitude with `j` children of cavities `mu` and amplitudes `ell`. -/
noncomputable def nodeAmp (s j : ℕ) (ell mu : Fin j → ℝ) : ℝ :=
  gVal (s + j) - (j : ℝ) * omegaVal + (∑ i, ell i)
    + Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * ∑ i, mu i) / (4 * ((s : ℝ) + j) + 3))

/-- The all-children-equal node amplitude at mean cavity `m` (children amplitudes bounded by `H m`). -/
noncomputable def Qeq (s j : ℕ) (H : ℝ → ℝ) (m : ℝ) : ℝ :=
  gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * H m
    + Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3))

/-- **The Jensen reduction:** the multi-child node is at most the all-equal node at the mean cavity.  Uses
    `jensen_sum` (`∑ ell_l <= ∑ H(mu_l) <= j H(mubar)`) and that the log-coupling depends on the children only
    through `∑ mu_l = j mubar`. -/
theorem node_jensen_reduction {s j : ℕ} (hj : 0 < j) {I : Set ℝ} {H : ℝ → ℝ} (hH : ConcaveOn ℝ I H)
    (ell mu : Fin j → ℝ) (hmem : ∀ i, mu i ∈ I) (hell : ∀ i, ell i ≤ H (mu i)) :
    nodeAmp s j ell mu ≤ Qeq s j H ((∑ i, mu i) / j) := by
  have hjne : (j : ℝ) ≠ 0 := by positivity
  unfold nodeAmp Qeq
  have hmean : (4 * (s : ℝ) + 3 * j + 3 + 3 * ∑ i, mu i)
      = (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * ((∑ i, mu i) / j)) := by
    field_simp
  rw [hmean]
  have hsum : (∑ i, ell i) ≤ (j : ℝ) * H ((∑ i, mu i) / j) :=
    le_trans (Finset.sum_le_sum (fun i _ => hell i)) (jensen_sum hj hH mu hmem)
  linarith [hsum]

end R3Cert
