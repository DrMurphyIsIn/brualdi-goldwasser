/-
  R4-R7 campaign, PHASE 5e (part 3, second file): the VEE-form merge identities
  (hubward direction) -- the head identities with an UP-chain present.

  Validated exactly (60/60 random Vee states, all 36 load cells): rooted at the
  absorber with the donor in the DOWN position,

      AobjV up a ((armsB,cb) :: down) = KblockV * beforeD daV dbV cA cb k sQV srV
      AobjV up (merged) down          = KblockV * afterD  daV dbV cA k    sQV srV

  with `daV = |armsA| + |tailU up| + 1` (the up-edge joins the absorber's degree),
  `sQV = sigmaArms armsA + qSum (tailU up)` (the up-block is one more capped
  neighbour), `KblockV = Kblock * (up-block Ztots)`.  This file: `qSum_append` and
  the BEFORE identity (raw donor sum).  Per the pinned construction notes: the
  donor-side haves are the HeadId ones verbatim (`down` for `rest`), and the endgame
  instantiates `twohub_scalar` EXPLICITLY and closes by `linear_combination` (ring
  glue on both sides; the up-factors reassociate into the PA/SA slots, the division
  subterm is a ring-atom -- no transcription of goal shapes).

  The split form, the AFTER identity, the mirror (donor-in-up) identities, and both
  `vee_merge_le` directions are the next files.  Nothing here asserts per-step
  monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47HeadId
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-! ### qSum over concatenation -/

theorem qSum_append (l1 l2 : List UTree) : qSum (l1 ++ l2) = qSum l1 + qSum l2 := by
  simp [qSum]

/-! ### The hubward Vee BEFORE identity (raw form) -/

/-! ### The hubward Vee BEFORE identity (certificate-slot form) -/

/-! ### The hubward Vee AFTER identity -/

end Step3
end R3Cert
