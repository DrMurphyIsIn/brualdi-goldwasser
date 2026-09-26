/-
  R4-R7 campaign, PHASE 2a: the stratum-(ii) state objects and their closed forms.

  Per the campaign addendum, the Kelmans rewrite operates on backbone-of-hub trees, whose
  states are integer data: arm cherry-loads and hub cherry-loads.  This file defines the
  bare-tree realizations (`cherryU`, `armU`, `backboneU`) and machine-checks the closed
  forms of the building blocks in the true-degree weighting:

  * `dtSub cherryU = cherryMid` -- the campaign's cherry IS the bridge's cherry, so the
    whole 4c toolkit (`Ztot_cherryMid = 3/2`, `Popen/Matched_replicate_cherry`) reuses;
  * `Ztot (dtSub (armU j)) = (3/2)^j * (1 + j/(3(j+1)))`, `Zopen = (3/2)^j` -- the arm
    partition functions, exactly the DEC arm quantities.

  Next (P2a2): the backbone `Ztot` recursion and the state-level amplitude `AState` with
  the seam `Aobj (backboneU h rest) = AState h rest`.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Tree

namespace R3Cert
namespace Step3

open RTree

/-! ### State objects -/

/-- A cherry as a bare tree. -/
def cherryU : UTree := UTree.node [UTree.node []]

/-- An arm carrying `j` cherries. -/
def armU (j : ℕ) : UTree := UTree.node (List.replicate j cherryU)

/-- A hub state: the arm cherry-loads and the hub's own cherry load. -/
abbrev Hub := List ℕ × ℕ

/-- Realize a hub backbone as a rooted tree (root = first hub; each hub carries its arms,
    its own cherries, and the next hub as one further child). -/
def backboneU : List Hub → UTree
  | [] => UTree.node []
  | (arms, c) :: rest =>
      UTree.node (arms.map armU ++ List.replicate c cherryU ++
        (match rest with
         | [] => []
         | _ :: _ => [backboneU rest]))

theorem udeg_cherryU : udeg cherryU = 2 := by
  simp [cherryU, udeg_node]

theorem udeg_armU (j : ℕ) : udeg (armU j) = j + 1 := by
  simp [armU, udeg_node]

/-! ### The campaign cherry is the bridge cherry -/

theorem dtSub_leaf : dtSub (UTree.node []) = RTree.node [] := by
  rw [dtSub_node, dtChildren_nil]

theorem dtSub_cherryU : dtSub cherryU = cherryMid := by
  rw [cherryU, dtSub_node, dtChildren_cons, dtChildren_nil, dtSub_leaf]
  norm_num [cherryMid, udeg_node]

theorem Ztot_dtSub_cherryU : Ztot (dtSub cherryU) = 3 / 2 := by
  rw [dtSub_cherryU, Ztot_cherryMid]

theorem Zopen_dtSub_cherryU : Zopen (dtSub cherryU) = 1 := by
  rw [dtSub_cherryU, Zopen_cherryMid]

/-- The weighted children of `j` cherries under a degree-`d` parent are `j` copies of the
    bridge's `litCherry d`. -/
theorem dtChildren_replicate_cherry (d : ℕ) (j : ℕ) :
    dtChildren d (List.replicate j cherryU) = List.replicate j (litCherry d) := by
  induction j with
  | zero => rw [List.replicate_zero, dtChildren_nil, List.replicate_zero]
  | succ k ih =>
    rw [List.replicate_succ, dtChildren_cons, ih, List.replicate_succ, litCherry_eq,
      dtSub_cherryU]
    norm_num [udeg_cherryU]

/-! ### Arm closed forms -/

theorem Zopen_dtSub_armU (j : ℕ) : Zopen (dtSub (armU j)) = (3 / 2) ^ j := by
  rw [armU, dtSub_node, List.length_replicate, dtChildren_replicate_cherry, Zopen,
    Popen_replicate_cherry]

theorem Ztot_dtSub_armU (j : ℕ) :
    Ztot (dtSub (armU j)) = (3 / 2) ^ j * (1 + (j : ℝ) / (3 * ((j : ℝ) + 1))) := by
  rw [armU, dtSub_node, List.length_replicate, dtChildren_replicate_cherry, Ztot,
    Popen_replicate_cherry, Matched_replicate_cherry _ _ (by omega)]
  push_cast
  ring

end Step3
end R3Cert
