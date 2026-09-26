/-
  THE CAPSTONE: `Φ ≤ 1` — every piece assembled, unconditionally.

    E2 (kink family: main region + small corner)          [PotentialE2, PotentialE2Small]
      ⟹ E1, E3 (Lipschitz / slope reductions)            [PotentialE13]
      ⟹ StarBound (convex piece interpolation)           [PotentialM1Piece]
      ⟹ DeficitNonneg (tangent at the tie + m=0 slice)   [PotentialM1, PotentialM0Region]
      ⟹ ValidPotentialPlain Pval (classification)        [PotentialAssembly, PotentialReduce]
      ⟹ logPhi b ≤ 0 for EVERY branch                    [PotentialBound telescoping + Plainify]

  HONEST SCOPE: this closes the `Φ ≤ 1` inequality for the `Branch` cavity model of `Reach.lean`
  (the model in which the entire R3Cert library works, including the near-star tie `Φ = 1` at
  `k = 5`).  The remaining formalization gap between this model and the original
  permanent-of-Laplacian statement is the H2 cavity-recursion bridge (`Matching.lean` /
  `CavityTree.lean`), audited 2026-08-09 as not yet genuinely machine-checked.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.Plainify
import R3Cert.PotentialBound
import R3Cert.PotentialAssembly
import R3Cert.PotentialM1
import R3Cert.PotentialM1Piece
import R3Cert.PotentialE2
import R3Cert.PotentialE2Small
import R3Cert.PotentialE13

namespace R3Cert

/-- **`StarBound` holds** — the tangent-strengthened `m ≥ 1` crux. -/
theorem starBound_holds : StarBound :=
  starBound_of_endpoints (e1Bound_of_e2 e2Bound_holds) e2Bound_holds (e3Bound_of_e2 e2Bound_holds)

/-- **`DeficitNonneg` holds** — the tree-free per-node inequality. -/
theorem deficitNonneg_holds : DeficitNonneg :=
  deficitNonneg_of_star starBound_holds

/-- **The crux: `Pval` is a valid plain potential.** -/
theorem validPotentialPlain_holds : ValidPotentialPlain Pval :=
  validPlain_of_deficit deficitNonneg_holds

/-- **The plain-tree conjecture holds.** -/
theorem plainConjecture_holds : PlainConjecture :=
  plainConjecture_of_validPlain Pval validPotentialPlain_holds

/-- **THE BOUND: `log Φ(B) ≤ 0` — i.e. `Φ(B) ≤ 1` — for EVERY branch.** -/
theorem phi_le_one (b : Branch) : logPhi b ≤ 0 :=
  phi_le_one_of_deficitNonneg deficitNonneg_holds b

end R3Cert
