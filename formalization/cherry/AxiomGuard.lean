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
-- Part (B) on [2.35, 1 + √5): the window witness and a best arm (by exact-rational box checks on [2.35, 3.22)),
-- and the reduction below 2.35 (still external there; not proved in Lean).
#print axioms LeanCherry.window_witness_ext
#print axioms LeanCherry.window_witness_full
#print axioms LeanCherry.part_B_of_inputs_lower
-- Part (B) on [2, 1 + √5): the same, with the boxes extended down to 2, and the reduction below 2 (still
-- external there; not proved in Lean).
#print axioms LeanCherry.window_witness_ext2
#print axioms LeanCherry.window_witness_full2
#print axioms LeanCherry.part_B_of_inputs_lower2
-- Part (B) on all of 0 < λ < 1 + √5, with no external input: the kinked witness W2 on (0, 3/20] and the witness W*
-- on [3/20, 1 + √5) for every λ, a best arm, both former inputs, and the branch bound, ρ = e^{f*} and the bound on M_n.
#print axioms LeanCherry.part_B_full
#print axioms LeanCherry.partB_witness_all
#print axioms LeanCherry.partB_witnessInput
#print axioms LeanCherry.partB_smallInput
-- f* = f_3 on (0, 3/20], by a direct comparison of the arms.
#print axioms LeanCherry.fstar_eq_f3
-- The scalar certificates of part (B), as real inequalities over their whole intervals (exact-rational rows over
-- monotone enclosures, and Bernstein identities), and the (S6) hand step on [λ_D2, 2].
#print axioms LeanCherry.PBC.cert_C1
#print axioms LeanCherry.PBC.cert_C2
#print axioms LeanCherry.PBC.cert_C3
#print axioms LeanCherry.PBC.cert_C4
#print axioms LeanCherry.PBC.cert_C5
#print axioms LeanCherry.PBC.cert_C6
#print axioms LeanCherry.PBC.cert_C7
#print axioms LeanCherry.PBC.cert_C8
#print axioms LeanCherry.PBC.cert_C10
#print axioms LeanCherry.PBC.cert_Dmax
#print axioms LeanCherry.PBC.cert_S6_mid
#print axioms LeanCherry.PBC.cert_S6_full
#print axioms LeanCherry.PBC.mono_g
-- Auxiliary, not used by part_B_full: C9 (G3(3/43) < 0) and the monotonicity of r and of L_q, kept for the record.
#print axioms LeanCherry.PBC.cert_C9
#print axioms LeanCherry.PBC.mono_r
#print axioms LeanCherry.PBC.mono_Lq
-- Part (B), the equality clause, 0 < λ < 1 + √5: log T(b) = |b| f* exactly at the best arms.
#print axioms LeanCherry.part_B_equality
#print axioms LeanCherry.part_B_full_eq
#print axioms LeanCherry.eq_clause_of
#print axioms LeanCherry.PB.eq_config
#print axioms LeanCherry.PB.fArm2_lt_fArm3
#print axioms LeanCherry.PB.S6_lt
#print axioms LeanCherry.W2Facts.hg2_lt
