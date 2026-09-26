/-
  R3Cert.R47SingleHub -- the single-hub objective in closed form (Hdom / R6 entry point).

  `Hdom` (the open layer of R47TopCapstone.conjecture1_of_layers) bounds the objective of a merge-NORMAL
  Balanced+Capped state by the tie.  A single-hub state `[(arms, c)]` is a normal form
  (R47NormalForm.singleHub_isNormal); this file gives its objective in the clean rooted-tree form the R6
  arm/cherry value machinery (Ztot_dtSub_armU, Ztot_dtSub_cherryU) acts on:

      Aobj (backboneU [(arms, c)]) = Ztot (dtRealize (node (arms.map armU ++ replicate c cherryU))).

  This is the foundation the R6 optimization (arms balanced at 5, hub de-load) will build on.  It does
  NOT discharge Hdom -- that needs the value bounds + the multi-hub tiebreak (R5).  Genuine proof
  (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47RotateV

namespace R3Cert
namespace Step3

open RTree

/-- The objective of a single-hub state, unfolded to its rooted-tree `Ztot` form. -/
theorem singleHub_Aobj (arms : List ℕ) (c : ℕ) :
    Aobj (backboneU [(arms, c)])
      = Ztot (dtRealize (UTree.node (arms.map armU ++ List.replicate c cherryU))) := by
  rw [← AobjV_nil (arms, c) []]
  show Ztot (dtRealize (UTree.node
      (arms.map armU ++ List.replicate c cherryU ++ tailU [] ++ tailU []))) = _
  simp only [tailU_nil, List.append_nil]

end Step3
end R3Cert
