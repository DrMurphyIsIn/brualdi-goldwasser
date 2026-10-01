/-
LeanCherry.Basic -- constants of the cherry anchor at lam_c = 1 + sqrt 5 = 2 phi.

  lam = 2 phi,  1 + lam/2 = phi^2,  1 + lam = phi^3,  y_ch = 1/(2 phi^2) = 1/(2 + lam),  lam * y_ch = 1/phi,
  L = log phi (the cherry rate F*),  kap = phi * L (hinge slope),  U y = min 0 (kap * (y_ch - y)).

Numerics: 2/phi^3 < L < 1/2.
-/
import Mathlib

open Real

namespace LeanCherry

noncomputable section

/-- the golden ratio -/
abbrev φ : ℝ := goldenRatio

lemma φ_pos : 0 < φ := goldenRatio_pos
lemma φ_sq : φ ^ 2 = φ + 1 := goldenRatio_sq
lemma φ_gt_one : 1 < φ := one_lt_goldenRatio
lemma φ_lt_two : φ < 2 := goldenRatio_lt_two

lemma sqrt5_bounds : (2.236 : ℝ) < √5 ∧ √5 < 2.2361 := by
  have h5 : (0:ℝ) ≤ 5 := by norm_num
  constructor
  · rw [show (2.236:ℝ) = √(2.236^2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (2.2361:ℝ) = √(2.2361^2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma φ_bounds : (1.618 : ℝ) < φ ∧ φ < 1.61806 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold φ goldenRatio
  constructor <;> linarith

/-- the cherry threshold lam_c = 1 + sqrt 5 = 2 phi -/
def lam : ℝ := 2 * φ
/-- cherry message -/
def ych : ℝ := 1 / (2 * φ ^ 2)
/-- the cherry rate F* = L = log phi -/
def L : ℝ := Real.log φ
/-- hinge slope -/
def kap : ℝ := φ * L
/-- the hinge witness -/
def U (y : ℝ) : ℝ := min 0 (kap * (ych - y))

lemma lam_eq : lam = 1 + √5 := by unfold lam φ goldenRatio; ring
lemma lam_pos : 0 < lam := by unfold lam; linarith [φ_pos]
lemma one_add_half_lam : 1 + lam / 2 = φ ^ 2 := by unfold lam; rw [φ_sq]; ring
lemma one_add_lam : 1 + lam = φ ^ 3 := by
  unfold lam; have := φ_sq; nlinarith [φ_sq]
lemma two_add_lam : 2 + lam = 2 * φ ^ 2 := by unfold lam; rw [φ_sq]; ring
lemma ych_eq : ych = 1 / (2 + lam) := by rw [two_add_lam]; rfl
lemma ych_pos : 0 < ych := by unfold ych; have := φ_pos; positivity
lemma lam_ych : lam * ych = 1 / φ := by
  unfold lam ych; have := φ_pos.ne'; field_simp
lemma lam_ych' : lam * ych = φ - 1 := by
  rw [lam_ych, div_eq_iff φ_pos.ne']; linear_combination (-1 : ℝ) * φ_sq

lemma L_pos : 0 < L := Real.log_pos φ_gt_one
lemma kap_pos : 0 < kap := mul_pos φ_pos L_pos

/-- L < 1/2, via exp(1/2) >= 1 + 1/2 + 1/8 = 1.625 > phi -/
lemma L_lt_half : L < 1 / 2 := by
  unfold L
  rw [Real.log_lt_iff_lt_exp φ_pos]
  have h := Real.quadratic_le_exp_of_nonneg (x := (1:ℝ)/2) (by norm_num)
  have := φ_bounds.2
  linarith [show (1:ℝ) + 1/2 + (1/2)^2/2 = 1.625 by norm_num]

/-- 2/phi^3 < L, via exp(0.4722) <= 1.6037 < phi and 2/phi^3 = 2 sqrt 5 - 4 < 0.4722 -/
lemma two_div_φ_cube_lt_L : 2 / φ ^ 3 < L := by
  have hφ3 : φ ^ 3 = 2 + √5 := by
    have : φ ^ 3 = 2 * φ + 1 := by nlinarith [φ_sq]
    rw [this]; unfold φ goldenRatio; ring
  have hinv : 2 / φ ^ 3 = 2 * √5 - 4 := by
    rw [hφ3]
    have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
    have hne : (2 + √5) ≠ 0 := by positivity
    field_simp
    nlinarith [h5]
  rw [hinv]
  obtain ⟨s1, s2⟩ := sqrt5_bounds
  have hr : 2 * √5 - 4 < 0.4722 := by linarith
  have hexp : Real.exp 0.4722 < φ := by
    have hb := Real.exp_bound' (x := (0.4722:ℝ)) (by norm_num) (by norm_num) (n := 5) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 5, (0.4722:ℝ) ^ m / m.factorial) +
        (0.4722:ℝ) ^ 5 * (5 + 1) / (Nat.factorial 5 * 5) < 1.618 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [φ_bounds.1]
  have : (0.4722:ℝ) < L := by
    unfold L; rw [Real.lt_log_iff_exp_lt φ_pos]; exact hexp
  linarith

lemma kap_lt_two : kap < 2 := by
  unfold kap
  have := φ_bounds.2; have := L_lt_half; have := L_pos
  nlinarith

/-- the region-A gap: 2/phi^2 < kap (equivalently lam/phi^3 < kap) -/
lemma two_div_φ_sq_lt_kap : 2 / φ ^ 2 < kap := by
  have h := two_div_φ_cube_lt_L
  unfold kap
  have hp := φ_pos
  have : 2 / φ ^ 2 = φ * (2 / φ ^ 3) := by field_simp
  rw [this]
  exact mul_lt_mul_of_pos_left h hp

end

end LeanCherry
