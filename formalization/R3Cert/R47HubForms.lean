/-
  R4-R7 campaign, PHASE 2a2: the hub assembly toolkit.

  Pieces for the backbone `Ztot` seam (P2a3): `dtChildren` distributes over append; the arm
  cavity ratio is the clean rational `Q(armU j) = (3j+3)/(4j+3)`; arm partition functions
  are positive; the product/sum of a hub's arm children evaluate in closed form
  (`Popen = prod Ztot(arm)`, `sum w*Q = sum 3/(d(4j+3))`).  Everything is `Matched_factor`
  -shaped so the seam is a direct assembly.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47HubState

namespace R3Cert
namespace Step3

open RTree

/-! ### `dtChildren` distributes over append -/

theorem dtChildren_append (d : ℕ) (l1 l2 : List UTree) :
    dtChildren d (l1 ++ l2) = dtChildren d l1 ++ dtChildren d l2 := by
  induction l1 with
  | nil => rw [List.nil_append, dtChildren_nil, List.nil_append]
  | cons K rest ih =>
    rw [List.cons_append, dtChildren_cons, dtChildren_cons, ih, List.cons_append]

/-! ### Arm positivity and the arm cavity ratio -/

theorem Ztot_dtSub_armU_pos (j : ℕ) : 0 < Ztot (dtSub (armU j)) := by
  rw [Ztot_dtSub_armU]
  have h1 : (0 : ℝ) ≤ (j : ℝ) / (3 * ((j : ℝ) + 1)) := by positivity
  have h2 : (0 : ℝ) < (3 / 2 : ℝ) ^ j := by positivity
  nlinarith [mul_nonneg h2.le h1]

/-- **The arm cavity ratio**: `Q(armU j) = (3j+3)/(4j+3)`. -/
theorem Q_armU (j : ℕ) :
    Zopen (dtSub (armU j)) / Ztot (dtSub (armU j))
      = (3 * (j : ℝ) + 3) / (4 * (j : ℝ) + 3) := by
  rw [Zopen_dtSub_armU, Ztot_dtSub_armU]
  have h32 : ((3 / 2 : ℝ)) ^ j ≠ 0 := by positivity
  have hj1 : (3 * ((j : ℝ) + 1)) ≠ 0 := by positivity
  have hden : (1 + (j : ℝ) / (3 * ((j : ℝ) + 1))) ≠ 0 := by positivity
  have h43 : (4 * (j : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Hub children in closed form -/

theorem Popen_dtChildren_arms (d : ℕ) (arms : List ℕ) :
    Popen (dtChildren d (arms.map armU))
      = (arms.map (fun j => Ztot (dtSub (armU j)))).prod := by
  induction arms with
  | nil => rw [List.map_nil, dtChildren_nil, Popen, List.map_nil, List.prod_nil]
  | cons a rest ih =>
    rw [List.map_cons, dtChildren_cons, Popen_cons, ih, List.map_cons, List.prod_cons]

/-- The weighted cavity sum of a hub's arm children. -/
theorem sum_wQ_arms (d : ℕ) (hd : 0 < d) (arms : List ℕ) :
    ((dtChildren d (arms.map armU)).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
      = (arms.map (fun j : ℕ => 3 / ((d : ℝ) * (4 * (j : ℝ) + 3)))).sum := by
  induction arms with
  | nil => rw [List.map_nil, dtChildren_nil, List.map_nil, List.sum_nil, List.map_nil,
      List.sum_nil]
  | cons a rest ih =>
    rw [List.map_cons, dtChildren_cons, List.map_cons, List.sum_cons, ih,
      List.map_cons, List.sum_cons]
    congr 1
    show 1 / ((d : ℝ) * (udeg (armU a) : ℝ)) * (Zopen (dtSub (armU a)) / Ztot (dtSub (armU a)))
      = 3 / ((d : ℝ) * (4 * (a : ℝ) + 3))
    rw [Q_armU, udeg_armU]
    have hdR : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
    have h43 : (4 * (a : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp <;> ring

/-- The weighted cavity sum of a hub's own cherries. -/
theorem sum_wQ_cherries (d : ℕ) (hd : 0 < d) (c : ℕ) :
    ((dtChildren d (List.replicate c cherryU)).map
        (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum
      = (c : ℝ) * (1 / (3 * (d : ℝ))) := by
  rw [dtChildren_replicate_cherry, List.map_replicate, List.sum_replicate, nsmul_eq_mul,
    cherry_term _ hd]

end Step3
end R3Cert
