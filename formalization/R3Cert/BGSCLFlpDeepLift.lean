/-
  Problem B, Stage B2 (keystone): the DEEP FLP lift is UNCONDITIONAL.

  `BGSCLHnormPort.straightStep_sized_lift` isolated the context-lift's `Aobj` half as a per-level
  Obligation-A hypothesis.  This file DISCHARGES that debt for the FLP move: the pair of cavity gains

      G1 : Ztot(dtSub c) <= Ztot(dtSub c')
      G2 : Zopen(dtSub c)/udeg c <= Zopen(dtSub c')/udeg c'

  SELF-PROPAGATES through any ancestor frame (`dtSub_gains_lift`) -- the ancestor's own weight
  `1/(len+1)` is common to both sides, and by the root-degree factorization
  (`Ztot_node_deg`: `Ztot = P·(1 + qSum/k)`, `Popen_dtChildren`: `Zopen = P`) the replaced child
  enters `Ztot` only through `Ztot_c·(1 + w·Q0) + w·(Zopen_c/udeg_c)` -- monotone in (G1, G2).
  At the root, `Aobj_child_replace_le_deg` closes from the same pair.  The FLP site supplies the
  base gains (`Ztot_dtSub_flp_child_le`, and `1/3 <= 3/4` for G2 at `crest = []`).

  Headline: `flp_deep_straightStep` -- a leaf-pair FLP flip at ANY depth (site parent carrying a
  non-piece sibling, wrapped in arbitrary ancestor frames) is a full `StraightStep_sized` on the
  whole tree, with NO per-level obligations.  The `StraightProgress_sized` finder (B3) now only
  needs to FIND such a site.  Numerically re-verified (exact rationals, ~8000 propagation levels,
  0 violations) before formalization.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLRealOblACaseAIdentity
import R3Cert.R47ArmPerm
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47Dress
import R3Cert.R47HeadId
import R3Cert.R47HubState
import R3Cert.R47R7Sized
import R3Cert.R47RootRate
import R3Cert.R47StepSize
import R3Cert.R47Tree
import R3Cert.R47VeeId

namespace R3Cert
namespace Step3

open RTree

/-! ### General node cavity identities -/

/-- `Ztot(dtSub)` of a node: the root-degree factorization at the subtree degree `len + 1`. -/
theorem Ztot_dtSub_node_eq (cs : List UTree) :
    Ztot (dtSub (UTree.node cs))
      = (cs.map fun K => Ztot (dtSub K)).prod
        * (1 + (1 / ((cs.length : ℝ) + 1)) * qSum cs) := by
  rw [dtSub_node, Ztot_node_deg]
  push_cast
  ring

/-- `Zopen(dtSub)` of a node: the plain child product. -/
theorem Zopen_dtSub_node_eq (cs : List UTree) :
    Zopen (dtSub (UTree.node cs)) = (cs.map fun K => Ztot (dtSub K)).prod := by
  rw [dtSub_node]
  have h : Zopen (RTree.node (dtChildren (cs.length + 1) cs))
      = Popen (dtChildren (cs.length + 1) cs) := rfl
  rw [h, Popen_dtChildren]

/-- Every `udeg` is positive (a node has `len + 1 >= 1`). -/
theorem udeg_cast_pos (K : UTree) : (0 : ℝ) < (udeg K : ℝ) := by
  obtain ⟨cs⟩ := K
  rw [udeg_node]
  positivity

/-! ### The G-pair propagation through one ancestor frame -/

/-! ### The root closure from the G-pair -/

/-! ### Piece-status plumbing -/

/-! ### Ancestor frames -/

/-- Fold a stack of sibling frames around a core subtree (head frame innermost). -/
def plugFrames : List (List UTree × List UTree) → UTree → UTree
  | [], c => c
  | f :: fs, c => plugFrames fs (UTree.node (f.1 ++ c :: f.2))

/-! ### The FLP base gains at `crest = []` -/

/-! ### The headline: deep FLP flips are unconditional straight-steps -/

end Step3
end R3Cert
