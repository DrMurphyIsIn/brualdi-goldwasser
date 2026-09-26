/-
  Bridge STEP 4 (core): the cherry-HUB DECOUPLING LIMIT.  See ../BRIDGE_DESIGN.md.

  The DEC amplitude `Phi` is DEFINED as a `p -> infinity` cherry-hub limit: `Phi(G) = lim_p amp(hub + p arms
  + G)/amp(hub + p arms)`.  The mechanism that makes this well-defined and multiplicative over branches is the
  DECOUPLING: as the hub gains arms (`p -> infinity`), its cavity ratio `rho0` converges to a constant that is
  INDEPENDENT of the attached branches.

  This file proves that core analytic fact in the `cav`/`rho0` framework (Bridge.lean): for a hub
  `node cH (replicate p arm ++ branches)`,
      rho0 (hub_p)  ->  1 / (1 + cav arm)      as  p -> infinity,
  for ANY `branches` (the limit does not see them).  Verified numerically (exact Fraction): both with and
  without branches the ratio converges to `1/(1+cav arm)` (e.g. `= 7/10` for the cherry-arm).

  HONEST SCOPE: this is the decoupling mechanism -- the analytic heart of Step 4.  The FULL Step 4 (tying
  `logPhi <= 0` all the way back to `per(L(T))/prod deg` via the amplitude ratio, with the uniform `O(1/p^2)`
  error constant) is a larger analytic development and remains open (as `branch_multiplicativity.py` itself
  notes the uniform constant is unwritten).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.Bridge
import R3Cert.NearStar

namespace R3Cert
namespace Step4

open Filter Topology

/-- Sum of child cavities splits over list append. -/
theorem cavSum_append (l1 l2 : List Branch) : cavSum (l1 ++ l2) = cavSum l1 + cavSum l2 := by
  induction l1 with
  | nil => simp [cavSum]
  | cons b rest ih => rw [List.cons_append, cavSum, cavSum, ih]; ring

/-- **STEP 4 core -- the cherry-hub decoupling limit.**  A hub with `p` arms plus any fixed `branches` has
    `rho0 -> 1/(1 + cav arm)` as `p -> infinity`, INDEPENDENT of the branches. -/
theorem hub_rho0_limit (cH : ℕ) (arm : Branch) (branches : List Branch) :
    Tendsto (fun p : ℕ => rho0 (Branch.node cH (List.replicate p arm ++ branches)))
      atTop (𝓝 (1 / (1 + cav arm))) := by
  have hmpos : 0 < cav arm := cav_pos arm
  set m : ℝ := cav arm with hm
  set Sb : ℝ := cavSum branches with hSb
  set D : ℝ := 3 * (branches.length : ℝ) + 3 + 4 * (cH : ℝ) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hdenpos : ∀ p : ℕ, 0 < 3 * (p : ℝ) + D := fun p => by positivity
  -- rewrite rho0 (hub_p) into `1 / (1 + g p)`, g p = 3*(p*m + Sb)/(3p + D)
  have hrho : ∀ p : ℕ, rho0 (Branch.node cH (List.replicate p arm ++ branches))
      = 1 / (1 + 3 * ((p : ℝ) * m + Sb) / (3 * (p : ℝ) + D)) := by
    intro p
    rw [rho0_node]
    have hl : (List.replicate p arm ++ branches).length = p + branches.length := by simp
    have hc : cavSum (List.replicate p arm ++ branches) = (p : ℝ) * m + Sb := by
      rw [cavSum_append, cavSum_replicate, hm, hSb]
    rw [hl, hc, zc, hD]; push_cast; ring
  simp_rw [hrho]
  -- the denominator tends to atTop
  have hden : Tendsto (fun p : ℕ => 3 * (p : ℝ) + D) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  -- g p -> m
  have hg : Tendsto (fun p : ℕ => 3 * ((p : ℝ) * m + Sb) / (3 * (p : ℝ) + D)) atTop (𝓝 m) := by
    have heq : (fun p : ℕ => 3 * ((p : ℝ) * m + Sb) / (3 * (p : ℝ) + D))
        = fun p : ℕ => m + (3 * Sb - m * D) / (3 * (p : ℝ) + D) := by
      ext p
      have hne := (hdenpos p).ne'
      field_simp
      ring
    rw [heq]
    have h0 : Tendsto (fun p : ℕ => (3 * Sb - m * D) / (3 * (p : ℝ) + D)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hden
    simpa using tendsto_const_nhds.add h0
  -- rho0 = 1/(1+g) -> 1/(1+m)
  have h1m : (1 : ℝ) + m ≠ 0 := by positivity
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hg).inv₀ h1m

end Step4
end R3Cert
