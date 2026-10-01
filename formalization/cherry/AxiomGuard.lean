/-
  AxiomGuard -- every headline theorem of the cherry-regime formalization depends only on the three
  standard axioms of Lean 4 + Mathlib (propext, Classical.choice, Quot.sound).
  Run after `lake build`:  lake env lean AxiomGuard.lean
-/
import LeanCherry

-- Every finite tree, λ ≥ 1 + √5: the upper bound, and that it is strict.
#print axioms LeanCherry.pi_lam_le_tree
#print axioms LeanCherry.pi_lam_lt_tree
-- λ = 1: the matching sum is per(L) / ∏ deg, for every tree on at least two vertices.
#print axioms LeanCherry.pi_one_eq_permanent_tree
-- Branches, λ ≥ 1 + √5: the ceiling, with equality only for the cherry.
#print axioms LeanCherry.Br.ceiling_cherry_regime
#print axioms LeanCherry.Br.Tl_eq_cherry_iff
-- The maximum M_n, λ ≥ 1 + √5: bounds, ρ and the growth rate.
#print axioms LeanCherry.Mn_le
#print axioms LeanCherry.Mn_ge
#print axioms LeanCherry.rho_eq
#print axioms LeanCherry.Mn_rate
-- The one-block formula, every λ ≥ 0 (the limit for λ > 0).
#print axioms LeanCherry.Mn_le_rho
#print axioms LeanCherry.Mn_ge_block
#print axioms LeanCherry.Mn_tendsto_rho
#print axioms LeanCherry.rhoB_eq_cherry
