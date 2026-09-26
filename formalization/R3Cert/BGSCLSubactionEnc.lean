/-
  Tight-route log-enclosure for the degree-2 node / degree-3 child SUBACTION cell (2026-09-03).

  The analytic core the deg-3-child cell needs, where log x <= x-1 is TOO LOOSE
  (fold X=(7/9)^11*(621/64) ~ 0.611, need log X <= -11/24 ~ -0.458, but x-1 ~ -0.389).
  Telperion emit_log_combination route='tight': log X <= Q via X <= exp Q + degree-3
  Taylor exp upper (Real.exp_bound').  Kernel-checked against R3Cert.BGSCLInduction.
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

open Real

theorem log79_add_fstar : Real.log (7/9 : ℝ) - (-1 * FSTAR : ℝ) ≤ (-1/24 : ℝ) := by
  rw [FSTAR]
  have hXpos : (0 : ℝ) < (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) := by positivity
  have hsplit : Real.log ((7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)))
      = 11 * Real.log (7/9 : ℝ) + 1 * Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_pow]
    push_cast; ring
  have hexp := Real.exp_bound' (x := (11/24 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  have hU : (∑ m ∈ Finset.range 3, (11/24 : ℝ) ^ m / m.factorial)
      + (11/24 : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ (98585/62208 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexpU : Real.exp (11/24 : ℝ) ≤ (98585/62208 : ℝ) := le_trans hexp hU
  have hexppos : (0 : ℝ) < Real.exp (11/24 : ℝ) := Real.exp_pos _
  have hprod : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * Real.exp (11/24 : ℝ) ≤ 1 := by
    have hmono : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * Real.exp (11/24 : ℝ)
        ≤ (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * (98585/62208 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpU (le_of_lt hXpos)
    have hXU : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * (98585/62208 : ℝ) ≤ 1 := by norm_num
    linarith
  have hXle : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) ≤ Real.exp (-(11/24) : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    rw [le_div_iff₀ hexppos]
    linarith [hprod]
  have hlogle : Real.log ((7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ))) ≤ (-11/24 : ℝ) := by
    rw [Real.log_le_iff_le_exp hXpos]
    have hEq : (-(11/24) : ℝ) = (-11/24 : ℝ) := by norm_num
    rw [hEq] at hXle; exact hXle
  rw [hsplit] at hlogle
  linarith

end BGSCL
end R3Cert
