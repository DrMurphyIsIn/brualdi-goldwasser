/-
  R4-R7 campaign, PHASE 7: the structural STRAIGHTENING measure (tree->hub, Pass 3).

  The tree->hub schema's remaining obligations (`RewriteDecreases`, `RewriteProgresses`) are
  about a rewrite that straightens an arbitrary tree toward a hub-backbone.  This file builds the
  MEASURE that anchors both: a structural defect count `strDefect` that vanishes on every
  backbone (the "off-spine branches" component of the lexicographic measure).

  Recognizers: `isLeaf`/`isCherry`/`isArm` for the canonical pieces (`cherryU = node[node[]]`,
  `armU j = node (replicate j cherryU)`).  A node is a canonical backbone layer when all but at
  most one of its children are `isPiece` (arm or cherry) and the exceptional child (the tail) is
  itself a backbone.  `strDefect (node cs)` charges `(#non-piece children - 1)` (a canonical layer
  has at most one) plus the defects of the non-piece children (recursing into the tail).

  What is PROVED here (no `sorry`, axiom-clean):
    * `isArm_armU`, `isCherry_cherryU`, `isPiece_*` -- the canonical pieces are recognized;
    * `strDefect_armU`, `strDefect_cherryU` -- pieces are defect-free;
    * `strDefect_backboneU` -- **every hub-backbone has zero defect**, by induction on the hub
      list (the measure vanishes on the tree->hub target class).

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47HubState
import R3Cert.R47Backbone
import R3Cert.R47R7TreeReduce

namespace R3Cert
namespace Step3

open RTree

/-! ### Structural recognizers -/

/-- A bare leaf `node []`. -/
def isLeaf : UTree → Bool
  | .node [] => true
  | .node (_ :: _) => false

/-- A cherry `node [node []]` (`= cherryU`). -/
def isCherry : UTree → Bool
  | .node [c] => isLeaf c
  | .node [] => false
  | .node (_ :: _ :: _) => false

/-- An arm `node (replicate j cherryU)`: every child is a cherry (`armU j`; `armU 0 = leaf`). -/
def isArm : UTree → Bool
  | .node cs => cs.all isCherry

/-- A canonical off-spine piece: an arm or a cherry. -/
def isPiece (c : UTree) : Bool := isArm c || isCherry c

theorem isCherry_cherryU : isCherry cherryU = true := by
  rw [cherryU, isCherry, isLeaf]

theorem isArm_armU (j : ℕ) : isArm (armU j) = true := by
  rw [armU, isArm, List.all_eq_true]
  intro x hx
  rw [List.eq_of_mem_replicate hx]; exact isCherry_cherryU

theorem isPiece_armU (j : ℕ) : isPiece (armU j) = true := by
  rw [isPiece, isArm_armU, Bool.true_or]

theorem isPiece_cherryU : isPiece cherryU = true := by
  rw [isPiece, isCherry_cherryU, Bool.or_true]

/-! ### The straightening defect measure -/

/-- Number of non-piece children in a list. -/
def npCount : List UTree → ℕ
  | [] => 0
  | c :: rest => (if isPiece c then 0 else 1) + npCount rest

mutual
/-- Structural defect: `(#non-piece children - 1)` at this node (a canonical backbone layer has
    at most one non-piece child, the tail) plus the defects of the non-piece children. -/
def strDefect : UTree → ℕ
  | .node cs => (npCount cs - 1) + npDefectSum cs
/-- Sum of `strDefect` over the non-piece children. -/
def npDefectSum : List UTree → ℕ
  | [] => 0
  | c :: rest => (if isPiece c then 0 else strDefect c) + npDefectSum rest
end

/-! ### Additivity of the child-list folds -/

theorem npCount_append (A B : List UTree) : npCount (A ++ B) = npCount A + npCount B := by
  induction A with
  | nil => rw [List.nil_append, npCount, Nat.zero_add]
  | cons c rest ih => rw [List.cons_append, npCount, npCount, ih, Nat.add_assoc]

theorem npDefectSum_append (A B : List UTree) :
    npDefectSum (A ++ B) = npDefectSum A + npDefectSum B := by
  induction A with
  | nil => rw [List.nil_append, npDefectSum, Nat.zero_add]
  | cons c rest ih => rw [List.cons_append, npDefectSum, npDefectSum, ih, Nat.add_assoc]

/-! ### Piece lists carry no defect -/

theorem npCount_pieces {L : List UTree} (h : ∀ x ∈ L, isPiece x = true) : npCount L = 0 := by
  induction L with
  | nil => rw [npCount]
  | cons c rest ih =>
    rw [npCount, h c (by simp), if_pos rfl, Nat.zero_add]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem npDefectSum_pieces {L : List UTree} (h : ∀ x ∈ L, isPiece x = true) :
    npDefectSum L = 0 := by
  induction L with
  | nil => rw [npDefectSum]
  | cons c rest ih =>
    rw [npDefectSum, h c (by simp), if_pos rfl, Nat.zero_add]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem pieces_map_armU (arms : List ℕ) : ∀ x ∈ arms.map armU, isPiece x = true := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact isPiece_armU j

theorem pieces_replicate_cherryU (c : ℕ) :
    ∀ x ∈ List.replicate c cherryU, isPiece x = true := by
  intro x hx
  rw [List.eq_of_mem_replicate hx]; exact isPiece_cherryU

/-! ### Canonical pieces are defect-free -/

theorem isPiece_leaf : isPiece (UTree.node []) = true := by
  rw [isPiece, isArm, List.all_nil, Bool.true_or]

theorem strDefect_leaf : strDefect (UTree.node []) = 0 := by
  rw [strDefect, npCount, npDefectSum]

theorem strDefect_cherryU : strDefect cherryU = 0 := by
  rw [cherryU, strDefect, npCount, npCount, npDefectSum, npDefectSum, isPiece_leaf]
  simp

theorem strDefect_armU (j : ℕ) : strDefect (armU j) = 0 := by
  rw [armU, strDefect, npCount_pieces (pieces_replicate_cherryU j),
    npDefectSum_pieces (pieces_replicate_cherryU j)]

/-! ### The measure vanishes on every backbone -/

theorem strDefect_backboneU (s : List Hub) : strDefect (backboneU s) = 0 := by
  induction s with
  | nil => exact strDefect_leaf
  | cons hd rest ih =>
    obtain ⟨arms, c⟩ := hd
    rw [backboneU_eq, strDefect, npCount_append, npCount_append, npDefectSum_append,
      npDefectSum_append, npCount_pieces (pieces_map_armU arms),
      npCount_pieces (pieces_replicate_cherryU c), npDefectSum_pieces (pieces_map_armU arms),
      npDefectSum_pieces (pieces_replicate_cherryU c)]
    have hY : npDefectSum (tailU rest) = 0 := by
      cases rest with
      | nil => simp [tailU, npDefectSum]
      | cons hd2 rest2 =>
        rw [tailU, npDefectSum, npDefectSum]
        split <;> simp [ih]
    have hX : npCount (tailU rest) ≤ 1 := by
      cases rest with
      | nil => simp [tailU, npCount]
      | cons hd2 rest2 =>
        rw [tailU, npCount, npCount]
        split <;> omega
    omega

/-! ### The straightening rewrite: `RewriteDecreases` discharged for the `strDefect` measure -/

/-- A straightening step: `Aobj`-non-decreasing and strictly `strDefect`-decreasing.  The concrete
    Kelmans-straighten moves are instances (each raises no `Aobj` and removes an off-spine defect,
    lowering `strDefect`). -/
def StraightStep (t t' : UTree) : Prop := Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t

/-- **`RewriteDecreases` discharged** for the straightening rewrite with the concrete `strDefect`
    measure -- every straightening step strictly lowers the off-spine defect count. -/
theorem straightStep_decreases : RewriteDecreases StraightStep strDefect :=
  fun h => h.2

/-- `RewriteMonotone` for the straightening rewrite (each step is `Aobj`-non-decreasing). -/
theorem straightStep_monotone : RewriteMonotone StraightStep :=
  fun h => h.1

/-- The single remaining straightening obligation: every positive-defect tree admits a
    straightening step.  This is the structural existence of a defect-reducing `Aobj`-monotone move
    (the Kelmans-straighten content the paper certifies). -/
def StraightProgress : Prop := ∀ t : UTree, strDefect t ≠ 0 → ∃ t', StraightStep t t'

/-- **Straightening reduces every tree to a defect-zero tree** (given `StraightProgress`).  Uses the
    generalized schema with the measure-zero target and the discharged `RewriteDecreases` +
    monotonicity; only `StraightProgress` remains, and `strDefect_backboneU` confirms every
    hub-backbone is a valid (defect-zero) endpoint. -/
theorem straighten_to_defectZero (hprog : StraightProgress) :
    ∀ t : UTree, ∃ n : UTree, strDefect n = 0 ∧ Aobj t ≤ Aobj n :=
  treeReduce_of_rewrite (fun t => strDefect t = 0) StraightStep strDefect
    (fun h => h.1) (fun h => h.2) (fun {t} hn => hprog t hn)

end Step3
end R3Cert
