/-
  Bridge STEP 2 (cherry-folding / dressed realization): `Branch.rho0` IS a matching cavity of an `RTree`.

  See ../BRIDGE_DESIGN.md.  Step 1 (Bridge.lean) exposed `cav = z(d,c) * rho0`, `rho0 = 1/(1 + z(d,c)*S)`.
  This file realizes a `Branch` as a DEC-DRESSED `RTree` -- the cherries FOLDED into `z(d,c) = 3/(3d+c)`
  (no explicit cherry vertices), with edge weight `w = z(d,c) * z(d_child,c_child)` -- and proves the
  matching cavity `Zopen/Ztot` of that RTree equals `rho0`:

      q_realize_eq_rho0 :  Zopen (realize b) / Ztot (realize b) = rho0 b.

  So `Branch.rho0` (hence `cav = z(d,c)*rho0`) is exactly a DEC-weighted matching cavity, connecting the
  `Branch` capstone layer to the `RTree` matching partition functions (CavityTree.tree_cavity_recursion).
  Numerically validated (exact Fraction): `q(realize b) = rho0 b` and `z(d,c)*q = cav`, 500/500.

  HONEST SCOPE: this is the DRESSED realization (z-weights).  It does NOT yet realize the RTree as a literal
  SimpleGraph with `1/(deg*deg)` weights (the naive raw-cavity bridge is FALSE -- cherries fold into z, not
  into rho0's child-sum).  Step 3 (RTree -> SimpleGraph) and Step 4 (rho_B amplitude / hub limit) remain
  OPEN.  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.Bridge

namespace R3Cert

open RTree

/-- A branch's own DEC z-value `z(d,c) = zc c (children.length)`. -/
noncomputable def branchZ : Branch → ℝ
  | .node c ch => zc c ch.length

theorem branchZ_pos (b : Branch) : 0 < branchZ b := by
  cases b with
  | node c ch => rw [branchZ]; exact zc_pos c ch.length

/- Realize a `Branch` as a DEC-dressed `RTree`: edge weight `= z(d,c) * z(d_child,c_child)`, cherries
   folded into `z` (no explicit cherry vertices). -/
mutual
/-- Realize a `Branch` as a DEC-dressed `RTree` (edge weight `z(d,c)·z(d_child,c_child)`). -/
noncomputable def realize : Branch → RTree
  | .node c ch => RTree.node (realizeCh (zc c ch.length) ch)
noncomputable def realizeCh : ℝ → List Branch → List (ℝ × RTree)
  | _, [] => []
  | zp, K :: rest => (zp * branchZ K, realize K) :: realizeCh zp rest
end

theorem realize_node (c : ℕ) (ch : List Branch) :
    realize (Branch.node c ch) = RTree.node (realizeCh (zc c ch.length) ch) := by rw [realize]

/-! ### Positivity of the realized matching partition functions -/

mutual
theorem Zopen_realize_pos (b : Branch) : 0 < Zopen (realize b) := by
  cases b with
  | node c ch => rw [realize_node, Zopen]; exact Popen_realizeCh_pos (zc c ch.length) ch
theorem Ztot_realize_pos (b : Branch) : 0 < Ztot (realize b) := by
  cases b with
  | node c ch =>
    rw [realize_node, Ztot]
    have hP := Popen_realizeCh_pos (zc c ch.length) ch
    have hM := Matched_realizeCh_nonneg (zc c ch.length) (zc_pos c ch.length).le ch
    linarith
theorem Popen_realizeCh_pos (zp : ℝ) (ch : List Branch) : 0 < Popen (realizeCh zp ch) := by
  cases ch with
  | nil => rw [realizeCh, Popen]; norm_num
  | cons K rest =>
    rw [realizeCh, Popen]
    exact mul_pos (Ztot_realize_pos K) (Popen_realizeCh_pos zp rest)
theorem Matched_realizeCh_nonneg (zp : ℝ) (hzp : 0 ≤ zp) (ch : List Branch) :
    0 ≤ Matched (realizeCh zp ch) := by
  cases ch with
  | nil => rw [realizeCh, Matched]
  | cons K rest =>
    rw [realizeCh, Matched]
    have h1 : 0 ≤ zp * branchZ K * Zopen (realize K) * Popen (realizeCh zp rest) :=
      mul_nonneg (mul_nonneg (mul_nonneg hzp (branchZ_pos K).le) (Zopen_realize_pos K).le)
        (Popen_realizeCh_pos zp rest).le
    have h2 : 0 ≤ Ztot (realize K) * Matched (realizeCh zp rest) :=
      mul_nonneg (Ztot_realize_pos K).le (Matched_realizeCh_nonneg zp hzp rest)
    linarith [h1, h2]
end

theorem Ztot_realize_ne (b : Branch) : Ztot (realize b) ≠ 0 := (Ztot_realize_pos b).ne'

/-- Every element of `realizeCh zp ch` is `(w, realize K)` for some child `K ∈ ch`. -/
theorem mem_realizeCh {zp : ℝ} {ch : List Branch} {p : ℝ × RTree} :
    p ∈ realizeCh zp ch → ∃ K ∈ ch, p.2 = realize K := by
  induction ch with
  | nil => intro hp; simp [realizeCh] at hp
  | cons K rest ih =>
    intro hp
    rw [realizeCh] at hp
    rcases List.mem_cons.mp hp with h | h
    · exact ⟨K, List.mem_cons.mpr (Or.inl rfl), by rw [h]⟩
    · obtain ⟨K', hK', hK'2⟩ := ih h
      exact ⟨K', List.mem_cons.mpr (Or.inr hK'), hK'2⟩

/-! ### The Step-2 identity: `Zopen/Ztot (realize b) = rho0 b` -/

mutual
theorem q_realize_eq_rho0 : ∀ b : Branch, Zopen (realize b) / Ztot (realize b) = rho0 b
  | .node c ch => by
    have hne : ∀ p ∈ realizeCh (zc c ch.length) ch, Ztot p.2 ≠ 0 := by
      intro p hp
      obtain ⟨K, _, hK2⟩ := mem_realizeCh hp
      rw [hK2]; exact Ztot_realize_ne K
    rw [realize_node, tree_cavity_recursion _ hne, q_realizeCh_sum (zc c ch.length) ch, rho0_node]
theorem q_realizeCh_sum : ∀ (zp : ℝ) (ch : List Branch),
    ((realizeCh zp ch).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum = zp * cavSum ch
  | _, [] => by simp [realizeCh, cavSum]
  | zp, K :: rest => by
    have hsplit : ((realizeCh zp (K :: rest)).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
        = (zp * branchZ K) * (Zopen (realize K) / Ztot (realize K))
          + ((realizeCh zp rest).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum := by
      rw [realizeCh]; simp
    rw [hsplit, q_realize_eq_rho0 K, q_realizeCh_sum zp rest, cavSum]
    have hbz : branchZ K * rho0 K = cav K := by
      cases K with
      | node cK chK => rw [branchZ]; exact (cav_eq_zc_mul_rho0 cK chK).symm
    rw [mul_assoc, hbz]
    ring
end

/-- **Corollary: `cav` is a DEC-weighted matching cavity.**  `cav b = z(d,c) * Zopen/Ztot (realize b)`. -/
theorem cav_eq_zc_mul_q_realize (c : ℕ) (ch : List Branch) :
    cav (Branch.node c ch) = zc c ch.length * (Zopen (realize (Branch.node c ch)) / Ztot (realize (Branch.node c ch))) := by
  rw [q_realize_eq_rho0, ← cav_eq_zc_mul_rho0]

end R3Cert
