/-
  THE PLAINIFICATION THEOREM -- Phi <= 1 reduces to CHERRY-FREE ("plain") trees, formalized.

  `plainification_theorem.py` (self-verified) shows a CHERRY is EXACTLY an ARM child: the atomic identity
  (MOVE B)  node (c+1) ch  ==  node c (armB :: ch)  preserves BOTH the cavity and logPhi.  Iterating turns
  every branch into a PLAIN branch (`c = 0` at every node) with the SAME cavity and logPhi, so

      Phi <= 1  <=>  every PLAIN branch has logPhi <= 0.

  This file machine-checks that reduction (no `sorry`).  The residual plain-tree inequality is NOT proved
  here (it is the open Brualdi-Goldwasser crux, `Reach.ValidPotential` existence); this file removes the
  cherry-count and leaf-cherry-count parameters exactly.

  MAIN RESULTS (all no-sorry):
  * `cav_cherry_step`  / `logPhi_cherry_step` -- the atomic MOVE B identity (cavity and logPhi).
  * `cav_plainify`     / `logPhi_plainify`    -- `plainify` preserves cavity and logPhi.
  * `plainify_isPlain` -- `plainify b` is plain.
  * `phi_le_one_of_plain` -- if every plain branch has `logPhi <= 0`, then EVERY branch does (Phi <= 1).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar

namespace R3Cert

open Real

/-! ## List helpers (append distribution) -/

theorem cavSum_append (l₁ l₂ : List Branch) :
    cavSum (l₁ ++ l₂) = cavSum l₁ + cavSum l₂ := by
  induction l₁ with
  | nil => simp [cavSum]
  | cons b rest ih => rw [List.cons_append, cavSum, cavSum, ih]; ring

theorem logPhiSum_append (l₁ l₂ : List Branch) :
    logPhiSum (l₁ ++ l₂) = logPhiSum l₁ + logPhiSum l₂ := by
  induction l₁ with
  | nil => simp [logPhiSum]
  | cons b rest ih => rw [List.cons_append, logPhiSum, logPhiSum, ih]; ring

/-! ## The atomic identity (MOVE B): a cherry is exactly an ARM child -/

/-- **MOVE B (cavity):** `cav (node (c+1) ch) = cav (node c (armB :: ch))`.
    Both denominators equal `3 + 3·nch + 4c + 4 + 3S`: the extra ARM child's `1/3` cavity (times 3)
    exactly compensates the extra `+4` from one more cherry vs. one more child. -/
theorem cav_cherry_step (c : ℕ) (ch : List Branch) :
    cav (Branch.node (c + 1) ch) = cav (Branch.node c (armB :: ch)) := by
  rw [cav_eq, cav_eq, cavSum, cav_arm, List.length_cons]
  congr 1
  push_cast
  ring

/-- **MOVE B (root increment):** `eroot (c+1) ch = logPhi armB + eroot c (armB :: ch)`.
    The `(3/2)^c` and `rhoB^{-(1+2c)}` factors of `ac` produce exactly `logPhi armB = -2L + log(3/2)`;
    the remaining factor `(1 + c/3d)(1 + z·S)` cancels (both sides `= (3d+c+3S)/(3d)`). -/
theorem eroot_cherry_step (c : ℕ) (ch : List Branch) :
    eroot (c + 1) ch = logPhi armB + eroot c (armB :: ch) := by
  have hr : (0 : ℝ) < rhoB := rhoB_pos
  have hSnn : 0 ≤ cavSum ch := cavSum_nonneg ch
  have hSnn' : 0 ≤ cavSum (armB :: ch) := cavSum_nonneg (armB :: ch)
  have hA1 : 0 < ac (c + 1) ch.length := by
    rw [ac]; exact div_pos (by positivity) (pow_pos hr _)
  have hA2 : 0 < ac c (ch.length + 1) := by
    rw [ac]; exact div_pos (by positivity) (pow_pos hr _)
  have hF1 : 0 < 1 + zc (c + 1) ch.length * cavSum ch := by
    rw [zc]; positivity
  have hF2 : 0 < 1 + zc c (ch.length + 1) * cavSum (armB :: ch) := by
    rw [zc]; positivity
  have hcs : cavSum (armB :: ch) = 1 / 3 + cavSum ch := by rw [cavSum, cav_arm]
  -- The multiplicative core identity, with `rhoB^2` cleared to the LHS (both sides positive).
  have hkey : ac (c + 1) ch.length * (1 + zc (c + 1) ch.length * cavSum ch) * rhoB ^ 2
      = (3 / 2) * (ac c (ch.length + 1) * (1 + zc c (ch.length + 1) * cavSum (armB :: ch))) := by
    rw [hcs]
    have hpow : rhoB ^ (1 + 2 * (c + 1)) = rhoB ^ (1 + 2 * c) * rhoB ^ 2 := by
      rw [show (1 + 2 * (c + 1)) = (1 + 2 * c) + 2 from by ring, pow_add]
    have hpow32 : (3 / 2 : ℝ) ^ (c + 1) = (3 / 2) * (3 / 2) ^ c := by
      rw [pow_succ]; ring
    have hrne : rhoB ≠ 0 := ne_of_gt hr
    have hrp : (0 : ℝ) < rhoB ^ (1 + 2 * c) := pow_pos hr _
    unfold ac zc
    rw [hpow, hpow32]
    push_cast
    field_simp
    ring
  -- Take logs of `hkey` and read off the eroot identity.
  have hpos1 : 0 < ac (c + 1) ch.length * (1 + zc (c + 1) ch.length * cavSum ch) := mul_pos hA1 hF1
  have hpos2 : 0 < ac c (ch.length + 1) * (1 + zc c (ch.length + 1) * cavSum (armB :: ch)) :=
    mul_pos hA2 hF2
  have hr2 : (0 : ℝ) < rhoB ^ 2 := by positivity
  have hlogged : Real.log (ac (c + 1) ch.length * (1 + zc (c + 1) ch.length * cavSum ch)) + 2 * Lval
      = Real.log (3 / 2)
        + Real.log (ac c (ch.length + 1) * (1 + zc c (ch.length + 1) * cavSum (armB :: ch))) := by
    have h := congrArg Real.log hkey
    rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt hr2), Real.log_pow, logRhoB,
      Real.log_mul (by norm_num) (ne_of_gt hpos2)] at h
    push_cast at h
    linarith [h]
  rw [eroot, eroot, logPhi_arm]
  simp only [List.length_cons]
  rw [← Real.log_mul (ne_of_gt hA1) (ne_of_gt hF1),
    ← Real.log_mul (ne_of_gt hA2) (ne_of_gt hF2)]
  linarith [hlogged]

/-- **MOVE B (logPhi):** `logPhi (node (c+1) ch) = logPhi (node c (armB :: ch))`. -/
theorem logPhi_cherry_step (c : ℕ) (ch : List Branch) :
    logPhi (Branch.node (c + 1) ch) = logPhi (Branch.node c (armB :: ch)) := by
  have harm : logPhiSum (armB :: ch) = logPhi armB + logPhiSum ch := rfl
  simp only [logPhi]
  rw [harm, eroot_cherry_step]
  ring

/-! ## Iterating MOVE B at one node: replace all `c` cherries by `c` ARM children -/

theorem cav_cherriesToArms (c : ℕ) (ch : List Branch) :
    cav (Branch.node c ch) = cav (Branch.node 0 (List.replicate c armB ++ ch)) := by
  induction c generalizing ch with
  | zero => simp
  | succ n ih =>
      rw [cav_cherry_step, ih (armB :: ch), List.replicate_succ', List.append_assoc,
        List.singleton_append]

theorem logPhi_cherriesToArms (c : ℕ) (ch : List Branch) :
    logPhi (Branch.node c ch) = logPhi (Branch.node 0 (List.replicate c armB ++ ch)) := by
  induction c generalizing ch with
  | zero => simp
  | succ n ih =>
      rw [logPhi_cherry_step, ih (armB :: ch), List.replicate_succ', List.append_assoc,
        List.singleton_append]

/-! ## `plainify` -- push MOVE B recursively through the whole tree -/

mutual
/-- `plainify` a branch: drop all cherries to ARM children and recurse into the children. -/
noncomputable def plainify : Branch → Branch
  | .node c ch => Branch.node 0 (List.replicate c armB ++ plainifyList ch)
/-- `plainify` a child list, elementwise. -/
noncomputable def plainifyList : List Branch → List Branch
  | [] => []
  | b :: rest => plainify b :: plainifyList rest
end

theorem length_plainifyList (l : List Branch) : (plainifyList l).length = l.length := by
  induction l with
  | nil => rfl
  | cons b rest ih => rw [plainifyList, List.length_cons, List.length_cons, ih]

mutual
theorem cav_plainify (b : Branch) : cav (plainify b) = cav b := by
  cases b with
  | node c ch =>
    rw [plainify, cav_eq, cav_eq, List.length_append, List.length_replicate,
      length_plainifyList, cavSum_append, nearStar_cavSum, cavSum_plainifyList ch]
    congr 1
    push_cast
    ring
theorem cavSum_plainifyList (l : List Branch) : cavSum (plainifyList l) = cavSum l := by
  cases l with
  | nil => rfl
  | cons b rest => rw [plainifyList, cavSum, cavSum, cav_plainify b, cavSum_plainifyList rest]
end

mutual
theorem logPhi_plainify (b : Branch) : logPhi (plainify b) = logPhi b := by
  cases b with
  | node c ch =>
    rw [plainify, logPhi_cherriesToArms c ch]
    simp only [logPhi, eroot]
    rw [logPhiSum_append, logPhiSum_append, logPhiSum_plainifyList ch,
      List.length_append, List.length_append, length_plainifyList,
      cavSum_append, cavSum_append, cavSum_plainifyList ch]
theorem logPhiSum_plainifyList (l : List Branch) : logPhiSum (plainifyList l) = logPhiSum l := by
  cases l with
  | nil => rfl
  | cons b rest =>
    rw [plainifyList, logPhiSum, logPhiSum, logPhi_plainify b, logPhiSum_plainifyList rest]
end

/-! ## Plain branches and the reduction capstone -/

/- A branch is PLAIN when every node has `0` cherries (leaves are bare `node 0 []`). -/
mutual
def IsPlain : Branch → Prop
  | .node c ch => c = 0 ∧ IsPlainList ch
def IsPlainList : List Branch → Prop
  | [] => True
  | b :: rest => IsPlain b ∧ IsPlainList rest
end

theorem isPlain_armB : IsPlain armB := by
  unfold armB
  exact ⟨rfl, ⟨⟨rfl, trivial⟩, trivial⟩⟩

theorem isPlainList_replicate (b : Branch) (h : IsPlain b) (n : ℕ) :
    IsPlainList (List.replicate n b) := by
  induction n with
  | zero => exact trivial
  | succ m ih => rw [List.replicate_succ]; exact ⟨h, ih⟩

theorem isPlainList_append : ∀ (l₁ l₂ : List Branch),
    IsPlainList l₁ → IsPlainList l₂ → IsPlainList (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | b :: rest, l₂, h₁, h₂ => ⟨h₁.1, isPlainList_append rest l₂ h₁.2 h₂⟩

mutual
theorem plainify_isPlain (b : Branch) : IsPlain (plainify b) := by
  cases b with
  | node c ch =>
    rw [plainify]
    exact ⟨rfl, isPlainList_append _ _ (isPlainList_replicate armB isPlain_armB c)
      (plainifyList_isPlain ch)⟩
theorem plainifyList_isPlain (l : List Branch) : IsPlainList (plainifyList l) := by
  cases l with
  | nil => exact trivial
  | cons b rest =>
    rw [plainifyList]; exact ⟨plainify_isPlain b, plainifyList_isPlain rest⟩
end

/-- **THE PLAINIFICATION REDUCTION (no `sorry`).**  If every PLAIN branch has `logPhi <= 0`, then EVERY
    branch does -- i.e. `Phi <= 1` for all trees follows from `Phi <= 1` on cherry-free trees.  Proof:
    `logPhi b = logPhi (plainify b)` (MOVE B, iterated) and `plainify b` is plain. -/
theorem phi_le_one_of_plain
    (hplain : ∀ b : Branch, IsPlain b → logPhi b ≤ 0) (b : Branch) : logPhi b ≤ 0 := by
  rw [← logPhi_plainify b]
  exact hplain (plainify b) (plainify_isPlain b)

/-- The residual crux, isolated: every PLAIN (cherry-free) branch has `logPhi <= 0`. -/
def PlainConjecture : Prop := ∀ b : Branch, IsPlain b → logPhi b ≤ 0

/-- **THE REDUCTION AS AN EQUIVALENCE (no `sorry`).**  `Phi <= 1` for ALL trees is EQUIVALENT to the
    parameter-free plain-tree bound.  Forward: plain branches are branches.  Backward: `phi_le_one_of_plain`.
    So `PlainConjecture` is exactly the open crux, with the cherry/leaf-count parameters removed. -/
theorem phi_le_one_iff_plain : (∀ b : Branch, logPhi b ≤ 0) ↔ PlainConjecture := by
  constructor
  · intro h b _; exact h b
  · intro h b; exact phi_le_one_of_plain h b

end R3Cert
