/-
  R3Cert.BGEnvCert.LogBound -- rational enclosures of `log` checkable by the kernel (2026-09-25).

  For `|x| < 1`: `|Σ_{i<n} x^(i+1)/(i+1) + log(1-x)| ≤ |x|^(n+1)/(1-|x|)` (Mathlib
  `Real.abs_log_sub_add_sum_range_le`).  Writing `z = 2^m z'` and `x = 1 - 1/z'` gives the rational
  bounds `logLB z m ≤ log z ≤ logUB z m` (the `m log 2` part uses the same series at `x = 1/2`).
  Every bound is a computable `ℚ`, compared by `decide +kernel`.  No `sorry`; standard axioms only.
-/
import Mathlib

namespace R3Cert
namespace EnvCert

/-- `Σ_{i<n} x^(i+1)/(i+1)`. -/
def lser (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lser x n + x ^ (n + 1) / (n + 1)

/-- The remainder bound `|x|^(n+1)/(1-|x|)`. -/
def lerr (x : ℚ) (n : ℕ) : ℚ := |x| ^ (n + 1) / (1 - |x|)

theorem lser_cast (x : ℚ) : ∀ n : ℕ,
    ((lser x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (i + 1) / (i + 1)
  | 0 => by simp [lser]
  | n + 1 => by rw [lser, Finset.sum_range_succ, ← lser_cast x n]; push_cast; ring

/-- `-log(1-x)` lies within `lerr` of the partial sum. -/
theorem neglog_bounds (x : ℚ) (hx : |x| < 1) (n : ℕ) :
    ((lser x n - lerr x n : ℚ) : ℝ) ≤ -Real.log (1 - x) ∧
      -Real.log (1 - x) ≤ ((lser x n + lerr x n : ℚ) : ℝ) := by
  have hxr : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have h := Real.abs_log_sub_add_sum_range_le hxr n
  rw [← lser_cast] at h
  have he : ((lerr x n : ℚ) : ℝ) = |(x : ℝ)| ^ (n + 1) / (1 - |(x : ℝ)|) := by
    unfold lerr; push_cast; rfl
  rw [← he] at h
  have h2 := abs_le.mp h
  push_cast
  constructor <;> linarith [h2.1, h2.2]

/-- Enclosure of `log 2`. -/
def L2up : ℚ := lser (1 / 2) 60 + lerr (1 / 2) 60
def L2lo : ℚ := lser (1 / 2) 60 - lerr (1 / 2) 60

theorem log_two_bounds : ((L2lo : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((L2up : ℚ) : ℝ) := by
  have h := neglog_bounds (1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num) 60
  have e : -Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = Real.log 2 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = 2⁻¹ by push_cast; norm_num, Real.log_inv, neg_neg]
  rw [e] at h
  exact ⟨h.1, h.2⟩

/-- `2^m` for an integer `m`, as a rational. -/
def pw2 (m : ℤ) : ℚ := if 0 ≤ m then (2 : ℚ) ^ m.toNat else 1 / (2 : ℚ) ^ (-m).toNat

theorem pw2_pos (m : ℤ) : 0 < pw2 m := by unfold pw2; split_ifs <;> positivity

theorem log_pw2 (m : ℤ) : Real.log ((pw2 m : ℚ) : ℝ) = (m : ℝ) * Real.log 2 := by
  unfold pw2
  split_ifs with h
  · push_cast
    rw [Real.log_pow]
    have : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    rw [this]
  · push_cast
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
    have : (((-m).toNat : ℕ) : ℝ) = -(m : ℝ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ -m by omega); exact_mod_cast this
    rw [this]; ring

theorem mul_log_two_le (m : ℤ) :
    (m : ℝ) * Real.log 2 ≤ (((m : ℚ) * (if 0 ≤ m then L2up else L2lo) : ℚ) : ℝ) := by
  obtain ⟨hlo, hup⟩ := log_two_bounds
  push_cast
  split_ifs with h
  · have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left hup this
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    exact mul_le_mul_of_nonpos_left hlo this

theorem le_mul_log_two (m : ℤ) :
    (((m : ℚ) * (if 0 ≤ m then L2lo else L2up) : ℚ) : ℝ) ≤ (m : ℝ) * Real.log 2 := by
  obtain ⟨hlo, hup⟩ := log_two_bounds
  push_cast
  split_ifs with h
  · have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left hlo this
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    exact mul_le_mul_of_nonpos_left hup this

/-- Number of series terms for a reduced logarithm. -/
def NL : ℕ := 30

/-- Upper bound for `log z`, with the reduction `z = 2^m z'`. -/
def logUB (z : ℚ) (m : ℤ) : ℚ :=
  (m : ℚ) * (if 0 ≤ m then L2up else L2lo) + (lser (1 - pw2 m / z) NL + lerr (1 - pw2 m / z) NL)

/-- Lower bound for `log z`. -/
def logLB (z : ℚ) (m : ℤ) : ℚ :=
  (m : ℚ) * (if 0 ≤ m then L2lo else L2up) + (lser (1 - pw2 m / z) NL - lerr (1 - pw2 m / z) NL)

/-- The side condition of the reduction. -/
def logOK (z : ℚ) (m : ℤ) : Bool := decide (0 < z) && decide (|1 - pw2 m / z| < 1)

theorem log_split (z : ℚ) (hz : 0 < z) (m : ℤ) :
    Real.log (z : ℝ) = (m : ℝ) * Real.log 2 + -Real.log (1 - ((1 - pw2 m / z : ℚ) : ℝ)) := by
  have hp := pw2_pos m
  have e : (1 : ℝ) - ((1 - pw2 m / z : ℚ) : ℝ) = ((pw2 m : ℚ) : ℝ) / (z : ℝ) := by push_cast; ring
  rw [e, Real.log_div (by exact_mod_cast hp.ne') (by exact_mod_cast hz.ne'), log_pw2]
  ring

theorem log_le_logUB (z : ℚ) (m : ℤ) (h : logOK z m = true) : Real.log (z : ℝ) ≤ (logUB z m : ℝ) := by
  unfold logOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hz, hx⟩ := h
  rw [log_split z hz m]
  have h1 := mul_log_two_le m
  have h2 := (neglog_bounds _ hx NL).2
  unfold logUB; push_cast at h1 h2 ⊢
  linarith

theorem logLB_le_log (z : ℚ) (m : ℤ) (h : logOK z m = true) : (logLB z m : ℝ) ≤ Real.log (z : ℝ) := by
  unfold logOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hz, hx⟩ := h
  rw [log_split z hz m]
  have h1 := le_mul_log_two m
  have h2 := (neglog_bounds _ hx NL).1
  unfold logLB; push_cast at h1 h2 ⊢
  linarith

end EnvCert
end R3Cert
