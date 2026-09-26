/-
  R4-R7 campaign, PHASE 2b2: the rewrite is FIXED-n.

  The stratification argument compares pi at FIXED vertex count (rho_B^n is constant per
  n, so pi-monotonicity = A-monotonicity within a stratum step).  This file machine-checks
  that the topped-up merge really is a fixed-n surgery: the state's realized vertex count
  is invariant under every `Step`.

  Bookkeeping identity behind it: the absorbed hub's vertex becomes the new load-5 arm's
  root vertex, and the `k = 5 - cb` borrows move cherries between arms without creating or
  destroying vertices -- `1 + 2*cb + 11*k = 9*k + 11` exactly when `cb + k = 5`.

  * `usize`/`usizeList`  -- vertex count of a bare tree / child list;
  * `usize_armU`, `usizeList_replicate_cherry` -- closed forms (arm `j` has `1 + 2j`);
  * `hubSize`/`stateSize` -- the per-hub and per-state vertex counts;
  * `usize_backbone`     -- the realization seam: `usize (backboneU s) = stateSize s`
    for nonempty `s`;
  * `Step.stateSize_eq`, `Step.usize_eq` -- CONSERVATION under every step.

  conjecture1_proved=False.  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Step

namespace R3Cert
namespace Step3

/-! ### Vertex count of a bare tree -/

mutual
/-- Number of vertices of a bare rooted tree. -/
def usize : UTree → ℕ
  | .node cs => 1 + usizeList cs
/-- Total vertex count of a child list. -/
def usizeList : List UTree → ℕ
  | [] => 0
  | K :: rest => usize K + usizeList rest
end

theorem usize_node (cs : List UTree) : usize (UTree.node cs) = 1 + usizeList cs := by
  rw [usize]

theorem usizeList_nil : usizeList [] = 0 := by rw [usizeList]

theorem usizeList_cons (K : UTree) (rest : List UTree) :
    usizeList (K :: rest) = usize K + usizeList rest := by rw [usizeList]

theorem usizeList_append (l1 l2 : List UTree) :
    usizeList (l1 ++ l2) = usizeList l1 + usizeList l2 := by
  induction l1 with
  | nil => rw [List.nil_append, usizeList_nil]; omega
  | cons K rest ih => rw [List.cons_append, usizeList_cons, usizeList_cons, ih]; omega

/-! ### Closed forms for the state building blocks -/

theorem usize_cherryU : usize cherryU = 2 := by
  rw [cherryU, usize_node, usizeList_cons, usizeList_nil, usize_node, usizeList_nil]

theorem usizeList_replicate_cherry (c : ℕ) :
    usizeList (List.replicate c cherryU) = 2 * c := by
  induction c with
  | zero => rw [List.replicate_zero, usizeList_nil]
  | succ k ih =>
    rw [List.replicate_succ, usizeList_cons, ih, usize_cherryU]
    omega

theorem usize_armU (j : ℕ) : usize (armU j) = 1 + 2 * j := by
  rw [armU, usize_node, usizeList_replicate_cherry]

theorem usizeList_map_armU (arms : List ℕ) :
    usizeList (arms.map armU) = arms.length + 2 * arms.sum := by
  induction arms with
  | nil =>
    rw [List.map_nil, usizeList_nil, List.length_nil, List.sum_nil]
    omega
  | cons a rest ih =>
    rw [List.map_cons, usizeList_cons, ih, usize_armU, List.length_cons, List.sum_cons]
    ring

/-! ### State-level vertex counts -/

/-- The vertex count a hub contributes: its own vertex + its arms + its cherries. -/
def hubSize (h : Hub) : ℕ := 1 + (h.1.length + 2 * h.1.sum) + 2 * h.2

/-- Total vertex count of a state. -/
def stateSize (s : List Hub) : ℕ := (s.map hubSize).sum

/-- `tailU` equation lemmas (the match-in-def). -/
theorem tailU_nil : tailU [] = [] := rfl

theorem tailU_cons (h : Hub) (t : List Hub) : tailU (h :: t) = [backboneU (h :: t)] := rfl

/-- The realization seam, in tail form: a state's tail realizes to its vertex count. -/
theorem usizeList_tailU (s : List Hub) : usizeList (tailU s) = stateSize s := by
  induction s with
  | nil => rw [tailU_nil, usizeList_nil, stateSize, List.map_nil, List.sum_nil]
  | cons h t ih =>
    obtain ⟨arms, c⟩ := h
    rw [tailU_cons, usizeList_cons, usizeList_nil, backboneU_eq, usize_node,
      usizeList_append, usizeList_append, usizeList_map_armU,
      usizeList_replicate_cherry, ih]
    simp only [stateSize, hubSize, List.map_cons, List.sum_cons]
    omega

/-- **The realization seam**: for a nonempty state the realized backbone's vertex count
    is the state's. -/
theorem usize_backbone (h : Hub) (t : List Hub) :
    usize (backboneU (h :: t)) = stateSize (h :: t) := by
  have h1 := usizeList_tailU (h :: t)
  rw [tailU_cons, usizeList_cons, usizeList_nil] at h1
  omega

/-! ### Conservation -/

/-- A step's source and target are nonempty. -/
theorem Step.ne_nil {s s' : List Hub} (hst : Step s s') : s ≠ [] ∧ s' ≠ [] := by
  cases hst <;> exact ⟨by simp, by simp⟩

/-- **Fixed-n at the state level**: the topped-up merge conserves the vertex count
    exactly -- the absorbed hub becomes the new load-5 arm's root, and the borrows move
    cherries without creating or destroying vertices. -/
theorem Step.stateSize_eq {s s' : List Hub} (hst : Step s s') :
    stateSize s' = stateSize s := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit =>
    have hlen := hsplit.length_eq
    have hsum := hsplit.sum_eq
    simp only [List.length_append, List.length_replicate, List.sum_append,
      List.sum_const_nat] at hlen hsum
    simp only [stateSize, List.map_cons, List.sum_cons, hubSize, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, List.sum_append,
      List.sum_const_nat, List.sum_cons, List.sum_nil]
    omega
  | @tail hd s s' hst ih =>
    simp only [stateSize, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- **The rewrite is fixed-n**: the realized backbone's vertex count is invariant under
    every step. -/
theorem Step.usize_eq {s s' : List Hub} (hst : Step s s') :
    usize (backboneU s') = usize (backboneU s) := by
  obtain ⟨hs, hs'⟩ := hst.ne_nil
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hs
  obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hs'
  rw [usize_backbone, usize_backbone, hst.stateSize_eq]

end Step3
end R3Cert
