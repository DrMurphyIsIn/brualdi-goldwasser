/-
  R3Cert.R47SingleHubFormula -- the single-hub objective as closed arm/cherry arithmetic (R6 core input).

  Applies `Ztot_hubNode` (R47Backbone) with `ts = []` to `singleHub_Aobj_node` (#99) to express the
  single-hub objective as the explicit arm/cherry formula the arms-balanced-at-5 optimization acts on:

      Aobj (backboneU [(arms, c)])
        = (∏ arms) * (3/2)^c * (1 + Σ_j 3/(d(4j+3)) + c/(3d)),   d = arms.length + c,

  where `∏ arms = ((arms.map armU).map (Ztot ∘ dtSub)).prod`.  Requires `0 < d` (a Capped normal-form
  hub has ≥ 5 arms, so this is discharged downstream).  Genuine proof (no `sorry`).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47SingleHubValue
import R3Cert.R47Backbone

namespace R3Cert
namespace Step3

open RTree

/-- The single-hub objective in closed arm/cherry arithmetic form. -/
theorem singleHub_Aobj_formula (arms : List ℕ) (c : ℕ) (hd : 0 < arms.length + c) :
    Aobj (backboneU [(arms, c)])
      = ((arms.map armU).map (fun K => Ztot (dtSub K))).prod * (3 / 2) ^ c
        * (1 + ((arms.map (fun j : ℕ =>
                3 / (((arms.length + c : ℕ) : ℝ) * (4 * (j : ℝ) + 3)))).sum
            + (c : ℝ) * (1 / (3 * ((arms.length + c : ℕ) : ℝ))))) := by
  rw [singleHub_Aobj_node]
  have h := Ztot_hubNode (arms.length + c) hd arms c [] (by simp)
  rw [List.append_nil] at h
  rw [h]
  simp only [List.map_nil, List.prod_nil, mul_one, dtChildren_nil, List.sum_nil, add_zero]

end Step3
end R3Cert
