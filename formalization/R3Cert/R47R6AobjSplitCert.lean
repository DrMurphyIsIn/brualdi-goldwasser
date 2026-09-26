/-
  R47 R6 single-hub objective split at a two-arm head -- the Aobj list-split for the
  balancing connective identity.

  SOURCE: singleHub_Aobj_formula (R47SingleHubFormula) + armProd_cons (R47Mono) +
  List.map_cons/sum_cons.

  Peels the leading two arms `a, b` off the single-hub objective, exposing the head arm
  values `Ztot(dtSub(armU a))`, `Ztot(dtSub(armU b))`, the common tail product `armProd rest`
  and the coupling with the two head slot-activities separated -- the exact form the
  balancing transfer `(a,b) -> (a+1,b-1)` acts on (the tail `armProd rest`, the tail sum, the
  hub term `c/(3D)`, and the degree `D = |a::b::rest| + c` are all COMMON to the transferred
  state, since the transfer preserves length).

  HONEST SCOPE.  The algebraic Aobj split at a two-arm head -- the list-surgery step of the
  connective identity.  It does NOT include the transfer comparison, the induction, nor the
  conjecture.  Self-contained; genuine proof (no `sorry`, no `axiom`, no vacuous hypothesis).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47SingleHubFormula
import R3Cert.R47HeadId
import R3Cert.R47Mono
import R3Cert.R47HubForms

namespace R3Cert
namespace Step3

open RTree

/-- **Single-hub objective split at a two-arm head.**  `D = (|a::b::rest| + c : ℕ)`. -/
theorem Aobj_cons2 (a b : ℕ) (rest : List ℕ) (c : ℕ)
    (hd : 0 < (a :: b :: rest).length + c) :
    Aobj (backboneU [(a :: b :: rest, c)])
      = Ztot (dtSub (armU a)) * Ztot (dtSub (armU b)) * armProd rest * (3 / 2) ^ c
        * (1 + (3 / ((((a :: b :: rest).length + c : ℕ) : ℝ) * (4 * (a : ℝ) + 3))
              + 3 / ((((a :: b :: rest).length + c : ℕ) : ℝ) * (4 * (b : ℝ) + 3))
              + (rest.map (fun j : ℕ =>
                  3 / ((((a :: b :: rest).length + c : ℕ) : ℝ) * (4 * (j : ℝ) + 3)))).sum)
            + (c : ℝ) * (1 / (3 * (((a :: b :: rest).length + c : ℕ) : ℝ)))) := by
  rw [singleHub_Aobj_formula _ _ hd, armProd_double, armProd_cons, armProd_cons]
  simp only [List.map_cons, List.sum_cons]
  ring

end Step3
end R3Cert
