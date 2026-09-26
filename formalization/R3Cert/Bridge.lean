/-
  Bridge (WIP): connect the three representations Branch (Reach.lean) / RTree (CavityTree.lean) /
  SimpleGraph (Matching.lean).  See ../BRIDGE_DESIGN.md for the full derivation and roadmap.

  STEP 1 (this file): the Branch-internal cavity-structure identity `cav = z(d,c) * rho0`, exposing the
  DEC cavity recursion `rho0 = 1/(1 + z(d,c)*S)` (S = sum of child cavities) that underlies `Branch.cav`.
  This is the anchor any `Branch -> RTree` matching-cavity map must reproduce.  Pure real-field algebra
  on the existing `Reach` definitions -- no permanent / Mathlib graph machinery yet.

  Numerically validated (exact Fraction, 400/400 random branches).  The naive `rho0 = raw 1/(deg*deg)
  cavity` bridge was empirically REFUTED (cherries fold into z(d,c), not into rho0's child-sum) -- see
  BRIDGE_DESIGN.md.  Steps 2-4 (cherry-folding, RTree<->SimpleGraph realization, the rho_B amplitude
  normalization / hub limit) remain OPEN.
-/
import Mathlib
import R3Cert.Reach
import R3Cert.CavityTree

namespace R3Cert

open Real

/-- The DEC cavity ratio `rho0(node c ch) = 1 / (1 + z(d,c) * S)`, `S = cavSum ch`, `d = nch+1+c`.
    Cherries are ABSENT from the child-sum here -- they are folded into `z(d,c) = 3/(3d+c)`. -/
noncomputable def rho0 : Branch → ℝ
  | .node c ch => 1 / (1 + zc c ch.length * cavSum ch)

theorem rho0_node (c : ℕ) (ch : List Branch) :
    rho0 (Branch.node c ch) = 1 / (1 + zc c ch.length * cavSum ch) := rfl

theorem zc_pos (c nch : ℕ) : 0 < zc c nch := by
  unfold zc
  have h1 : (0:ℝ) ≤ (nch : ℝ) := Nat.cast_nonneg _
  have h2 : (0:ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  positivity

theorem rho0_pos (b : Branch) : 0 < rho0 b := by
  cases b with
  | node c ch =>
    have hS : 0 ≤ cavSum ch := cavSum_nonneg ch
    have hz : 0 < zc c ch.length := zc_pos c ch.length
    have hden : (0:ℝ) < 1 + zc c ch.length * cavSum ch := by
      have := mul_nonneg hz.le hS; linarith
    rw [rho0]
    exact one_div_pos.mpr hden

/-- **STEP 1 -- the cavity-structure bridge lemma.**  The DEC child-contribution `cav` factors as
    `z(d,c) * rho0`, i.e. `Branch.cav` is exactly `z(d,c)` times the DEC cavity ratio.  Reproduces the
    closed form `cav = 3/(3+3nch+4c+3S)` from `rho0 = 1/(1 + z(d,c)*S)` by pure algebra. -/
theorem cav_eq_zc_mul_rho0 (c : ℕ) (ch : List Branch) :
    cav (Branch.node c ch) = zc c ch.length * rho0 (Branch.node c ch) := by
  have hS : 0 ≤ cavSum ch := cavSum_nonneg ch
  have h1 : (0:ℝ) ≤ (ch.length : ℝ) := Nat.cast_nonneg _
  have h2 : (0:ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  -- abbreviate the denominator t = 3d + c = 3(nch+1+c)+c, so zc = 3/t (definitionally)
  set t : ℝ := 3 * ((ch.length : ℝ) + 1 + (c : ℝ)) + (c : ℝ) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hzeq : zc c ch.length = 3 / t := rfl
  rw [cav_eq, rho0_node, hzeq]
  -- the closed-form denominator equals t + 3S
  have hkey : (3:ℝ) + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch = t + 3 * cavSum ch := by
    rw [ht]; ring
  rw [hkey]
  have h3S : 0 ≤ 3 / t * cavSum ch := mul_nonneg (by positivity) hS
  have htS : (0:ℝ) < t + 3 * cavSum ch := by linarith
  have hinner : (0:ℝ) < 1 + 3 / t * cavSum ch := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have htSne : t + 3 * cavSum ch ≠ 0 := htS.ne'
  have hinne : 1 + 3 / t * cavSum ch ≠ 0 := hinner.ne'
  field_simp

end R3Cert
