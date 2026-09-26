/-
  Top-level dispatch for `IsSubaction ρwit`, and the branch-ceiling capstone (2026-09-04).

  Assembles the per-degree SUBACTION cells (`BGSCLSubaction`, `BGSCLSubactionDeg3`,
  `BGSCLSubactionDeg3Mid`, `BGSCLSubactionD4Cells`, `BGSCLSubactionTailWrap`) into the single
  obligation `IsSubaction ρwit` that `ceiling_of_witness` needs.  The dispatcher `rcases` the
  child list `cs` by length (node degree `= |cs| + 1`) and, within each length, by the children's
  `bcc` classes, applying the matching cell.  Child order is canonicalized by `subaction_perm`
  (permutation invariance of the (SUB) predicate): the 9 ordered degree-3 pairs reduce to the 6
  canonical `subaction_deg3_*` cells, and an arbitrary degree-4 triple is sorted by `bcc` and
  routed to the 35 canonical `subaction_deg4_*` cells; the tail (degree ≥ 5) goes to `tail_wrapper`.

  CANONICALIZATION CONVENTION:
    child classes by `bcc`:  L = 0,  deg-2 = 1,  deg-3 = 2,  deg-4 = 3,  H = (4 ≤ bcc);
    canonical child order = non-decreasing `bcc`.

  `isSubaction_ρwit` and the capstone `bg_ceiling : ∀ b, bell b ≤ 0` are fully proven, no `sorry`.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionDeg3
import R3Cert.BGSCLSubactionDeg3Mid
import R3Cert.BGSCLSubactionD4Cells
import R3Cert.BGSCLSubactionTailWrap

namespace R3Cert
namespace BGSCL

open Real

/-! ### Permutation invariance of the (SUB) predicate. -/

/-- `ρwit` reads only through `bcc (node cs) = |cs|` and `bY (node cs)` (which, by `bY_node`,
    depends only on `|cs|` and `(cs.map bY).sum`); hence it is invariant under permuting the
    children.  A `List.Perm` fixes both `|cs|` and `(cs.map bY).sum`, so `ρwit` agrees. -/
theorem ρwit_node_perm {cs cs' : List Branch} (h : cs.Perm cs') :
    ρwit (Branch.node cs) = ρwit (Branch.node cs') := by
  have hlen : cs.length = cs'.length := h.length_eq
  have hbY : (cs.map bY).sum = (cs'.map bY).sum := (h.map bY).sum_eq
  have hbYnode : bY (Branch.node cs) = bY (Branch.node cs') := by
    rw [bY_node, bY_node, hlen, hbY]
  rw [ρwit, ρwit]
  simp only [bcc, hlen, hbYnode]

/-- **Permutation invariance of (SUB).**  The subaction inequality at a hub `node cs` transports
    across any permutation of the children: the log-term (through `(cs.map bY).sum` and `|cs|`), the
    node `ρwit` (`ρwit_node_perm`), and the RHS `(cs.map ρwit).sum` are each Perm-invariant. -/
theorem subaction_perm {cs cs' : List Branch} (h : cs.Perm cs')
    (hsub : (Real.log (1 + (cs'.map bY).sum / ((cs'.length : ℝ) + 1)) - FSTAR)
        + ρwit (Branch.node cs') ≤ (cs'.map ρwit).sum) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
        + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have hlen : cs.length = cs'.length := h.length_eq
  have hbY : (cs.map bY).sum = (cs'.map bY).sum := (h.map bY).sum_eq
  have hrho : (cs.map ρwit).sum = (cs'.map ρwit).sum := (h.map ρwit).sum_eq
  have hnode : ρwit (Branch.node cs) = ρwit (Branch.node cs') := ρwit_node_perm h
  rw [hbY, hlen, hnode, hrho]
  exact hsub

/-! ### Class helpers. -/

/-- A child with `bcc = 0` is the leaf `node []`. -/
theorem eq_leaf_of_bcc_zero {c : Branch} (hc : bcc c = 0) : c = Branch.node [] := by
  cases c with
  | node cs =>
    simp only [bcc, List.length_eq_zero_iff] at hc
    rw [hc]

/-! ### Degree-1 arm (`cs = []`). -/

/-- Degree-1 dispatch: the leaf node. -/
theorem subaction_deg1 :
    (Real.log (1 + (([] : List Branch).map bY).sum / ((([] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node []) ≤ (([] : List Branch).map ρwit).sum :=
  subaction_nil

/-! ### Degree-2 arm (`cs = [c]`). -/

/-- Degree-2 dispatch: one child, cased by `bcc c` — leaf ⇒ `subaction_cherry`,
    deg-2 ⇒ `subaction_deg2_deg2child`, deg-≥3 ⇒ `subaction_deg2_highchild`. -/
theorem subaction_deg2 (c : Branch) :
    (Real.log (1 + (([c] : List Branch).map bY).sum / ((([c] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c]) ≤ (([c] : List Branch).map ρwit).sum := by
  rcases (show bcc c = 0 ∨ bcc c = 1 ∨ 2 ≤ bcc c by omega) with h | h | h
  · -- leaf child
    rw [eq_leaf_of_bcc_zero h]
    exact subaction_cherry
  · exact subaction_deg2_deg2child c h
  · exact subaction_deg2_highchild c h

/-! ### Degree-3 arm (`cs = [c1, c2]`).

  Canonicalize the ordered pair `(bcc c1, bcc c2)` over the classes {L = 0, deg-2 = 1, H = ≥2}
  to non-decreasing order via `subaction_perm (List.Perm.swap ..)`, reducing the 9 ordered
  profiles to the 6 canonical cells:
    LL  → subaction_broom_d3,          LD2 → subaction_deg3_leaf_deg2,
    LH  → subaction_deg3_leaf_high,    D2D2→ subaction_deg3_deg2children,
    D2H → subaction_deg3_deg2_high,    HH  → subaction_deg3_highchildren. -/

/-- The canonical (non-decreasing) degree-3 cell for classes `(k1, k2)` with `k1 ≤ k2` classwise.
    Handles the 6 canonical orderings; callers use `subaction_perm` to canonicalize. -/
theorem subaction_deg3_canon (c1 c2 : Branch)
    (hle : bcc c1 = 0 ∧ bcc c2 = 0
         ∨ bcc c1 = 0 ∧ bcc c2 = 1
         ∨ bcc c1 = 0 ∧ 2 ≤ bcc c2
         ∨ bcc c1 = 1 ∧ bcc c2 = 1
         ∨ bcc c1 = 1 ∧ 2 ≤ bcc c2
         ∨ 2 ≤ bcc c1 ∧ 2 ≤ bcc c2) :
    (Real.log (1 + (([c1, c2] : List Branch).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2] : List Branch).map ρwit).sum := by
  rcases hle with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · -- (L, L)
    rw [eq_leaf_of_bcc_zero k1, eq_leaf_of_bcc_zero k2]
    exact subaction_broom_d3
  · -- (L, deg-2)
    rw [eq_leaf_of_bcc_zero k1]
    exact subaction_deg3_leaf_deg2 c2 k2
  · -- (L, high)
    rw [eq_leaf_of_bcc_zero k1]
    exact subaction_deg3_leaf_high c2 k2
  · -- (deg-2, deg-2)
    exact subaction_deg3_deg2children c1 c2 k1 k2
  · -- (deg-2, high)
    exact subaction_deg3_deg2_high c1 c2 k1 k2
  · -- (high, high)
    exact subaction_deg3_highchildren c1 c2 k1 k2

/-- Degree-3 dispatch: two children, canonicalized to non-decreasing `bcc` via `subaction_perm`. -/
theorem subaction_deg3 (c1 c2 : Branch) :
    (Real.log (1 + (([c1, c2] : List Branch).map bY).sum
        / ((([c1, c2] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2]) ≤ (([c1, c2] : List Branch).map ρwit).sum := by
  -- classify each child
  rcases (show bcc c1 = 0 ∨ bcc c1 = 1 ∨ 2 ≤ bcc c1 by omega) with h1 | h1 | h1 <;>
  rcases (show bcc c2 = 0 ∨ bcc c2 = 1 ∨ 2 ≤ bcc c2 by omega) with h2 | h2 | h2
  -- canonical (already non-decreasing) cases: apply directly
  · exact subaction_deg3_canon c1 c2 (Or.inl ⟨h1, h2⟩)
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  -- (deg-2, L) → swap to (L, deg-2)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inl ⟨h2, h1⟩)))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
  -- (high, L) → swap to (L, high)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
  -- (high, deg-2) → swap to (deg-2, high)
  · exact subaction_perm (List.Perm.swap c2 c1 []) (subaction_deg3_canon c2 c1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))))
  -- (high, high)
  · exact subaction_deg3_canon c1 c2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))

/-! ### Degree-4 arm (`cs = [c1, c2, c3]`).

  Same sort-then-classify factoring as degree 3, one dimension up.  `subaction_deg4_canon`
  handles a triple already in non-decreasing `bcc` order (`bcc x ≤ bcc y ≤ bcc z`), routing
  the 35 reachable class-triples to the `subaction_deg4_XYZ` cells (the 90 non-monotone
  class-triples are unreachable given the two `≤` hypotheses — `omega` closes them).
  `subaction_deg4` sorts an arbitrary triple by `bcc` via three `le_total` splits and transports
  the canonical proof back with `subaction_perm`.  Class codes: 0→L, 1→2, 2→3, 3→4, ≥4→H. -/

/-- The canonical (non-decreasing `bcc`) degree-4 cell.  Given `bcc x ≤ bcc y ≤ bcc z`, classify each
    of `bcc x, bcc y, bcc z` into {0,1,2,3,≥4} and apply the matching `subaction_deg4_XYZ` cell; the
    two ≤ hypotheses render the 90 non-monotone class-triples unreachable (`omega`). -/
theorem subaction_deg4_canon (x y z : Branch)
    (hxy : bcc x ≤ bcc y) (hyz : bcc y ≤ bcc z) :
    (Real.log (1 + (([x, y, z] : List Branch).map bY).sum
        / ((([x, y, z] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [x, y, z]) ≤ (([x, y, z] : List Branch).map ρwit).sum := by
  rcases (show bcc x = 0 ∨ bcc x = 1 ∨ bcc x = 2 ∨ bcc x = 3 ∨ 4 ≤ bcc x by omega) with
    hx | hx | hx | hx | hx <;>
  rcases (show bcc y = 0 ∨ bcc y = 1 ∨ bcc y = 2 ∨ bcc y = 3 ∨ 4 ≤ bcc y by omega) with
    hy | hy | hy | hy | hy <;>
  rcases (show bcc z = 0 ∨ bcc z = 1 ∨ bcc z = 2 ∨ bcc z = 3 ∨ 4 ≤ bcc z by omega) with
    hz | hz | hz | hz | hz <;>
  first
    | exact subaction_deg4_LLL x y z hx hy hz
    | exact subaction_deg4_LL2 x y z hx hy hz
    | exact subaction_deg4_LL3 x y z hx hy hz
    | exact subaction_deg4_LL4 x y z hx hy hz
    | exact subaction_deg4_LLH x y z hx hy hz
    | exact subaction_deg4_L22 x y z hx hy hz
    | exact subaction_deg4_L23 x y z hx hy hz
    | exact subaction_deg4_L24 x y z hx hy hz
    | exact subaction_deg4_L2H x y z hx hy hz
    | exact subaction_deg4_L33 x y z hx hy hz
    | exact subaction_deg4_L34 x y z hx hy hz
    | exact subaction_deg4_L3H x y z hx hy hz
    | exact subaction_deg4_L44 x y z hx hy hz
    | exact subaction_deg4_L4H x y z hx hy hz
    | exact subaction_deg4_LHH x y z hx hy hz
    | exact subaction_deg4_222 x y z hx hy hz
    | exact subaction_deg4_223 x y z hx hy hz
    | exact subaction_deg4_224 x y z hx hy hz
    | exact subaction_deg4_22H x y z hx hy hz
    | exact subaction_deg4_233 x y z hx hy hz
    | exact subaction_deg4_234 x y z hx hy hz
    | exact subaction_deg4_23H x y z hx hy hz
    | exact subaction_deg4_244 x y z hx hy hz
    | exact subaction_deg4_24H x y z hx hy hz
    | exact subaction_deg4_2HH x y z hx hy hz
    | exact subaction_deg4_333 x y z hx hy hz
    | exact subaction_deg4_334 x y z hx hy hz
    | exact subaction_deg4_33H x y z hx hy hz
    | exact subaction_deg4_344 x y z hx hy hz
    | exact subaction_deg4_34H x y z hx hy hz
    | exact subaction_deg4_3HH x y z hx hy hz
    | exact subaction_deg4_444 x y z hx hy hz
    | exact subaction_deg4_44H x y z hx hy hz
    | exact subaction_deg4_4HH x y z hx hy hz
    | exact subaction_deg4_HHH x y z hx hy hz
    | omega

/-- Degree-4 dispatch: sort the three children into non-decreasing `bcc` order `[x,y,z]` via three
    `le_total` splits, and transport `subaction_deg4_canon` back to the input order `[c1,c2,c3]` with
    `subaction_perm`. -/
theorem subaction_deg4 (c1 c2 c3 : Branch) :
    (Real.log (1 + (([c1, c2, c3] : List Branch).map bY).sum
        / ((([c1, c2, c3] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [c1, c2, c3]) ≤ (([c1, c2, c3] : List Branch).map ρwit).sum := by
  -- perms of [c1,c2,c3] to each sorted order
  have p_123 : ([c1, c2, c3] : List Branch).Perm [c1, c2, c3] := List.Perm.refl _
  have p_132 : ([c1, c2, c3] : List Branch).Perm [c1, c3, c2] :=
    (List.Perm.swap c3 c2 []).cons c1
  have p_213 : ([c1, c2, c3] : List Branch).Perm [c2, c1, c3] :=
    List.Perm.swap c2 c1 [c3]
  have p_231 : ([c1, c2, c3] : List Branch).Perm [c2, c3, c1] :=
    (List.Perm.swap c2 c1 [c3]).trans ((List.Perm.swap c3 c1 []).cons c2)
  have p_312 : ([c1, c2, c3] : List Branch).Perm [c3, c1, c2] :=
    ((List.Perm.swap c3 c2 []).cons c1).trans (List.Perm.swap c3 c1 [c2])
  have p_321 : ([c1, c2, c3] : List Branch).Perm [c3, c2, c1] :=
    (List.Perm.swap c2 c1 [c3]).trans
      ((List.Perm.swap c3 c1 []).cons c2 |>.trans (List.Perm.swap c3 c2 [c1]))
  rcases le_total (bcc c1) (bcc c2) with h12 | h12 <;>
    rcases le_total (bcc c2) (bcc c3) with h23 | h23 <;>
    rcases le_total (bcc c1) (bcc c3) with h13 | h13
  · -- a≤b≤c
    exact subaction_perm p_123 (subaction_deg4_canon c1 c2 c3 h12 h23)
  · -- a≤b, b≤c, c≤a ⟹ all equal
    exact subaction_perm p_123 (subaction_deg4_canon c1 c2 c3 h12 h23)
  · -- a≤c≤b
    exact subaction_perm p_132 (subaction_deg4_canon c1 c3 c2 h13 h23)
  · -- c≤a≤b
    exact subaction_perm p_312 (subaction_deg4_canon c3 c1 c2 h13 h12)
  · -- b≤a≤c
    exact subaction_perm p_213 (subaction_deg4_canon c2 c1 c3 h12 h13)
  · -- b≤c≤a
    exact subaction_perm p_231 (subaction_deg4_canon c2 c3 c1 h23 h13)
  · -- c≤b≤a (all equal here)
    exact subaction_perm p_321 (subaction_deg4_canon c3 c2 c1 h23 h12)
  · -- c≤b≤a
    exact subaction_perm p_321 (subaction_deg4_canon c3 c2 c1 h23 h12)

/-! ### Top-level dispatch. -/

/-- **`IsSubaction ρwit`** — the single remaining obligation of `ceiling_of_witness`, assembled by
    dispatching on child-list length (node degree) and, within each degree, on the children's
    `bcc` classes.  Degrees 1/2/3/4 are discharged by the per-degree sort-then-classify dispatchers
    over the cell family; the tail (degree ≥ 5) by `tail_wrapper`.  No `sorry`. -/
theorem isSubaction_ρwit : IsSubaction ρwit := by
  intro cs
  rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, rest⟩⟩⟩⟩
  · -- degree 1: cs = []
    exact subaction_deg1
  · -- degree 2: cs = [c1]
    exact subaction_deg2 c1
  · -- degree 3: cs = [c1, c2]
    exact subaction_deg3 c1 c2
  · -- degree 4: cs = [c1, c2, c3]
    exact subaction_deg4 c1 c2 c3
  · -- degree ≥ 5: cs = c1 :: c2 :: c3 :: c4 :: rest  (tail)
    exact tail_wrapper _ (by simp only [List.length_cons]; omega)

/-! ### Capstone. -/

/-- **The branch ceiling.**  Feeding the fully-assembled `IsSubaction ρwit` into `ceiling_of_witness`
    (whose nonnegativity leg `ρwit_nonneg` is already discharged) yields `∀ b, bell b ≤ 0` — the
    additive-subaction branch ceiling, unconditional in Lean.  `conjecture1_proved = False`. -/
theorem bg_ceiling : ∀ b, bell b ≤ 0 := ceiling_of_witness isSubaction_ρwit

end BGSCL
end R3Cert
