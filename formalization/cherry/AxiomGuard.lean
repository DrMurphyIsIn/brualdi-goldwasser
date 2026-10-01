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
-- The witness framework, every λ > 0: the witness theorem (a)-(c), and (d) up to the strict-supporting-line step.
#print axioms LeanCherry.Witness.mt_main_a
#print axioms LeanCherry.Witness.mt_main_b
#print axioms LeanCherry.Witness.mt_main_c
#print axioms LeanCherry.Witness.tight_node
#print axioms LeanCherry.Witness.tight_of_g_zero
-- The golden hinge at λ = 1 + √5 is a witness, and gives ρ(1 + √5) = φ.
#print axioms LeanCherry.hinge_witness
#print axioms LeanCherry.rho_lam_c_via_witness
-- Part (B), 0 < λ < 1 + √5, from two external numerical inputs (stated as hypotheses; not proved in Lean).
#print axioms LeanCherry.part_B_of_inputs
-- Part (B) on the window 3.22 ≤ λ < 1 + √5, by hand: the window witness and a best arm, and the branch bound.
#print axioms LeanCherry.window_witness
#print axioms LeanCherry.window_ceiling
-- Part (B), 0 < λ < 1 + √5, with the window removed from the inputs (still external below 3.22; not proved in Lean).
#print axioms LeanCherry.partB_witnessInput_of_low
#print axioms LeanCherry.part_B_of_inputs_low
