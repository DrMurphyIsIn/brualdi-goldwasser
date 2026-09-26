/-
  The `m ≥ 1` slice, part 3: PIECE INTERPOLATION — `StarBound ⟸ E1 ∧ E2 ∧ E3`.

  `StarBound`'s left side (fold form) is `α·Sg + β + (11/50)·(1/(K+Sg) − T0)₊` — linear plus a
  convex fold — while its right side is linear on each piece `[0, m·T0]` and `[m·T0, m/2]`.  So the
  bound follows from the three ENDPOINT families by convex interpolation (`linfold_interp`, built on
  `inv_combo` and `posPart_combo`), plus `Pval_le_fold` to upgrade `Pval` to the fold form.

  After this file the remaining mathematical content of the conjecture is `E1Bound ∧ E2Bound ∧
  E3Bound` — three families of rational inequalities in `(a, nl, m)` and `rhoB`.

  Genuine proofs (no `sorry`).  E1/E2/E3 are NOT proven here.
-/
import Mathlib
import R3Cert.Potential
import R3Cert.PotentialAux
import R3Cert.PotentialM1
import R3Cert.PotentialM1Fold

namespace R3Cert

open Real

/-- **Generic linear-plus-fold interpolation:** if the bound holds at the two ends of a segment it
    holds throughout (the left side is convex in `Sg`, the right side linear). -/
theorem linfold_interp {α β c γ δ K T p q Sg : ℝ} (hc : 0 ≤ c)
    (hKp : 0 < K + p) (hKq : 0 < K + q) (hpq : p < q) (hSp : p ≤ Sg) (hSq : Sg ≤ q)
    (hp : α * p + β + c * max 0 (1 / (K + p) - T) ≤ γ * p + δ)
    (hq : α * q + β + c * max 0 (1 / (K + q) - T) ≤ γ * q + δ) :
    α * Sg + β + c * max 0 (1 / (K + Sg) - T) ≤ γ * Sg + δ := by
  have hqp : (0 : ℝ) < q - p := by linarith
  set θ := (q - Sg) / (q - p) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hqp.le
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hqp]; linarith
  have hθmul : θ * (q - p) = q - Sg := by
    rw [hθdef]; exact div_mul_cancel₀ _ hqp.ne'
  have hSgeq : Sg = θ * p + (1 - θ) * q := by linarith [hθmul]
  have hinv := inv_combo hKp hKq hθ0 hθ1
  rw [← hSgeq] at hinv
  have he : θ * (1 / (K + p) - T) + (1 - θ) * (1 / (K + q) - T)
      = θ / (K + p) + (1 - θ) / (K + q) - T := by ring
  have hcomb : 1 / (K + Sg) - T ≤ θ * (1 / (K + p) - T) + (1 - θ) * (1 / (K + q) - T) := by
    linarith [hinv, he.le, he.ge]
  have hfold : max 0 (1 / (K + Sg) - T)
      ≤ θ * max 0 (1 / (K + p) - T) + (1 - θ) * max 0 (1 / (K + q) - T) :=
    le_trans (max_le_max le_rfl hcomb) (posPart_combo hθ0 hθ1)
  have hcfold := mul_le_mul_of_nonneg_left hfold hc
  have hpθ := mul_le_mul_of_nonneg_left hp hθ0
  have hqθ := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 1 - θ)
  calc α * Sg + β + c * max 0 (1 / (K + Sg) - T)
      ≤ α * Sg + β
          + c * (θ * max 0 (1 / (K + p) - T) + (1 - θ) * max 0 (1 / (K + q) - T)) := by
        linarith [hcfold]
    _ = θ * (α * p + β + c * max 0 (1 / (K + p) - T))
          + (1 - θ) * (α * q + β + c * max 0 (1 / (K + q) - T)) := by
        rw [hSgeq]; ring
    _ ≤ θ * (γ * p + δ) + (1 - θ) * (γ * q + δ) := by linarith [hpθ, hqθ]
    _ = γ * Sg + δ := by rw [hSgeq]; ring

/-- The fold-form left side of `StarBound` at generic cavity mass `S`. -/
noncomputable def starLHS (a nl m : ℕ) (S : ℝ) : ℝ :=
  (((a : ℝ) / 3 + nl + S) / ((a : ℝ) + nl + m + 1) - T0) / rhoB
    + (11 / 50) * max 0 (1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + S)) - T0)

/-- **Endpoint family `E1`** (`Sg = 0`). -/
def E1Bound : Prop := ∀ a nl m : ℕ, 1 ≤ m →
  starLHS a nl m 0 ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval

/-- **Endpoint family `E2`** (`Sg = m·T0`, the fold kink — contains the accumulating tie). -/
def E2Bound : Prop := ∀ a nl m : ℕ, 1 ≤ m →
  starLHS a nl m ((m : ℝ) * T0) ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval

/-- **Endpoint family `E3`** (`Sg = m/2`). -/
def E3Bound : Prop := ∀ a nl m : ℕ, 1 ≤ m →
  starLHS a nl m ((m : ℝ) / 2)
    ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval + (11 / 50) * ((m : ℝ) / 2 - (m : ℝ) * T0)

/-- `starLHS` in the `α·S + β + c·(1/(K+S) − T)₊` shape of `linfold_interp`. -/
theorem starLHS_shape (a nl m : ℕ) (S : ℝ) :
    starLHS a nl m S
      = (1 / (((a : ℝ) + nl + m + 1) * rhoB)) * S
          + (((a : ℝ) / 3 + nl) / ((a : ℝ) + nl + m + 1) - T0) / rhoB
          + (11 / 50) * max 0
              (1 / (((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + S) - T0) := by
  unfold starLHS
  have hN : ((a : ℝ) + nl + m + 1) ≠ 0 := by positivity
  have hr : rhoB ≠ 0 := ne_of_gt rhoB_pos
  have hlin : (((a : ℝ) / 3 + nl + S) / ((a : ℝ) + nl + m + 1) - T0) / rhoB
      = (1 / (((a : ℝ) + nl + m + 1) * rhoB)) * S
          + (((a : ℝ) / 3 + nl) / ((a : ℝ) + nl + m + 1) - T0) / rhoB := by
    field_simp [hN, hr]
    try ring
  have hK : (a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + S)
      = ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + S := by ring
  rw [hlin, hK]

/-- **`StarBound ⟸ E1 ∧ E2 ∧ E3`.** -/
theorem starBound_of_endpoints (hE1 : E1Bound) (hE2 : E2Bound) (hE3 : E3Bound) : StarBound := by
  intro a nl m Sg hm hSg0 hSgh
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT0 : (0 : ℝ) < T0 := lt_trans (by norm_num) T0_gt_fifth
  have hT2 : T0 < 1 / 2 := lt_trans T0_lt_third (by norm_num)
  have hKpos : (0 : ℝ) < (a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl) := by positivity
  -- upgrade Pval to the fold form
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hnl0 : (0 : ℝ) ≤ (nl : ℝ) := Nat.cast_nonneg nl
  have ha3 : (0 : ℝ) ≤ (a : ℝ) / 3 := by linarith
  have hcav1 : 1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg)) < 1 := by
    have hden : (0 : ℝ) < (a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg) := by
      linarith [hSg0, hmR]
    rw [div_lt_one hden]
    linarith [hSg0, hmR]
  have hPf := Pval_le_fold hcav1
  -- it suffices to bound the fold form
  have hmain : starLHS a nl m Sg
      ≤ (a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval + (11 / 50) * max 0 (Sg - (m : ℝ) * T0) := by
    rcases le_total Sg ((m : ℝ) * T0) with hple | hpge
    · -- piece 1: [0, m·T0], right side constant
      have hfold0 : max 0 (Sg - (m : ℝ) * T0) = 0 := max_eq_left (by linarith)
      rw [hfold0, mul_zero, add_zero]
      have hpq : (0 : ℝ) < (m : ℝ) * T0 := mul_pos (by linarith : (0 : ℝ) < (m : ℝ)) hT0
      have hp : starLHS a nl m 0 ≤ 0 * (0 : ℝ)
          + ((a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval) := by
        have := hE1 a nl m hm; linarith [this]
      have hq : starLHS a nl m ((m : ℝ) * T0) ≤ 0 * ((m : ℝ) * T0)
          + ((a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval) := by
        have := hE2 a nl m hm; linarith [this]
      rw [starLHS_shape] at hp hq ⊢
      have hres := linfold_interp (by norm_num : (0 : ℝ) ≤ 11 / 50)
        (by linarith : (0 : ℝ) < ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + 0)
        (by linarith [mul_pos (by linarith : (0:ℝ) < (m:ℝ)) hT0] :
          (0 : ℝ) < ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0)
        hpq hSg0 hple hp hq
      linarith [hres]
    · -- piece 2: [m·T0, m/2], right side slope 11/50
      have hfold1 : max 0 (Sg - (m : ℝ) * T0) = Sg - (m : ℝ) * T0 := max_eq_right (by linarith)
      rw [hfold1]
      have hpq : (m : ℝ) * T0 < (m : ℝ) / 2 := by
        have := mul_lt_mul_of_pos_left hT2 (by linarith : (0 : ℝ) < (m : ℝ))
        linarith [this]
      have hp : starLHS a nl m ((m : ℝ) * T0)
          ≤ (11 / 50) * ((m : ℝ) * T0)
            + ((a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval - (11 / 50) * ((m : ℝ) * T0)) := by
        have := hE2 a nl m hm; linarith [this]
      have hq : starLHS a nl m ((m : ℝ) / 2)
          ≤ (11 / 50) * ((m : ℝ) / 2)
            + ((a : ℝ) * (-omegaVal) + (nl : ℝ) * Lval - (11 / 50) * ((m : ℝ) * T0)) := by
        have := hE3 a nl m hm; linarith [this]
      have hT0nn : (0 : ℝ) ≤ (m : ℝ) * T0 := (mul_pos (by linarith : (0 : ℝ) < (m : ℝ)) hT0).le
      rw [starLHS_shape] at hp hq ⊢
      have hres := linfold_interp (by norm_num : (0 : ℝ) ≤ 11 / 50)
        (by linarith : (0 : ℝ) < ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) * T0)
        (by linarith : (0 : ℝ) < ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl)) + (m : ℝ) / 2)
        hpq hpge hSgh hp hq
      linarith [hres]
  -- assemble: Pval form ≤ fold form ≤ bound
  have hshape : starLHS a nl m Sg
      = (((a : ℝ) / 3 + nl + Sg) / ((a : ℝ) + nl + m + 1) - T0) / rhoB
        + (11 / 50) * max 0 (1 / ((a : ℝ) + nl + m + 1 + ((a : ℝ) / 3 + nl + Sg)) - T0) := rfl
  rw [hshape] at hmain
  linarith [hPf, hmain]

end R3Cert
