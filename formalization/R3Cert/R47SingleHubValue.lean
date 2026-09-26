/-
  R3Cert.R47SingleHubValue -- the single-hub objective as an explicit-degree hub node (R6 setup).

  `singleHub_Aobj` (R47SingleHub) gives the single-hub objective as `Ztot (dtRealize (node cs))`.
  This file rewrites it to the explicit-degree `dtChildren` hub-node form that `Ztot_hubNode`
  (R47Backbone) consumes for the R6 arm/cherry value expansion:

      Aobj (backboneU [(arms, c)]) = Ztot (RTree.node (dtChildren (arms.length + c)
                                            (arms.map armU ++ replicate c cherryU))).

  With this, the next R6 brick applies `Ztot_hubNode` (ts = []) to get the closed arm/cherry
  arithmetic the arms-balanced-at-5 optimization acts on.  Genuine proof (no `sorry`).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47SingleHub
import R3Cert.R47Backbone
import R3Cert.R47Tree

namespace R3Cert
namespace Step3

open RTree

/-- The single-hub objective as an explicit-degree `dtChildren` hub node. -/
theorem singleHub_Aobj_node (arms : List ℕ) (c : ℕ) :
    Aobj (backboneU [(arms, c)])
      = Ztot (RTree.node (dtChildren (arms.length + c)
          (arms.map armU ++ List.replicate c cherryU))) := by
  rw [singleHub_Aobj, dtRealize_node,
    show (arms.map armU ++ List.replicate c cherryU).length = arms.length + c by
      simp [List.length_append, List.length_map, List.length_replicate]]

end Step3
end R3Cert
