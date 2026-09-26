/-
  AxiomGuard -- every headline theorem of the Brualdi-Goldwasser formalization depends only on the
  three standard axioms of Lean 4 + Mathlib (propext, Classical.choice, Quot.sound).
  Run after `lake build`:  lake env lean AxiomGuard.lean
-/
import R3Cert.BGMaximizerAll
import R3Cert.BGGrowthRate
import R3Cert.BGSCLSharp
import R3Cert.BGStatement

-- The answer in Mathlib's vocabulary (SimpleGraph.IsTree, lapMatrix, Matrix.permanent): see Statement.lean.
#print axioms R3Cert.BGStatement.bg_maximum_le
#print axioms R3Cert.BGStatement.bg_maximum_attained
#print axioms R3Cert.TreePaths.tree_iso
-- The answer: for every n >= 4 the explicit spider bgMax n maximizes per(L)/prod deg over all trees.
#print axioms R3Cert.BGMaximizerAll.bg_maximizer_all
#print axioms R3Cert.BGMaximizerAll.bg_maximizer_all_perm
-- Its four ranges.
#print axioms R3Cert.BGMaximizerTiny.bg_maximizer_tiny
#print axioms R3Cert.BGMaximizerSmall.bg_maximizer_small
#print axioms R3Cert.BGMaximizerMid.bg_maximizer_mid
#print axioms R3Cert.BGMaximizerFinal.bg_maximizer
-- Structural steps.
#print axioms BGMax.bg_spider_reduction
#print axioms BGMax.maximizer_is_spider_150
#print axioms R3Cert.BGMaximizerSmall.maximizer_is_spider_small
#print axioms R3Cert.BGSpiderTable.spider_opt_table
#print axioms R3Cert.BGSpiderStruct.structProp_492
#print axioms R3Cert.BGSpiderCand.candProp_492
#print axioms R3Cert.BGMaximizerMid.exists_max_tree
#print axioms R3Cert.Step3.pi_utree
-- Companion results: the exact growth rate and the sharp rate ceiling (unique equality case).
#print axioms R3Cert.Step3.bg_max_growth
#print axioms R3Cert.BGSCL.bg_ceiling
#print axioms R3Cert.BGSCL.bg_sharp
