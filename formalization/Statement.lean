/-
  Statement.lean -- the Brualdi-Goldwasser theorem, for reviewers.

  Brualdi and Goldwasser (1984) asked which tree on n vertices maximizes the Laplacian ratio
      per L(G) / ∏_v deg(v).
  This file states the answer using only Mathlib's definitions for the graph side:
      SimpleGraph, SimpleGraph.IsTree, SimpleGraph.lapMatrix (= degree matrix - adjacency matrix),
      Matrix.permanent, SimpleGraph.degree.
  The maximum value is `F (bgChildren n)`, a closed form defined in a few lines (listed below).

  Check it with:   lake env lean Statement.lean
  (after `./build.sh`).  The last lines print the axioms: only propext, Classical.choice, Quot.sound.

  WHAT TO READ to trust this file (everything else is proof, checked by the kernel):

    R3Cert/BGSpiderOpt.lean       `Child` (a cherry, or an arm carrying j cherries; `arm 0` is a leaf),
                                  `alpha j = (4j+3)/(3(j+1))`, `bb j = 3/(4j+3)`,
                                  `Child.g` (cherry 3/2, arm j (3/2)^j * alpha j),
                                  `Child.r` (cherry 1/3, arm j bb j),
                                  `F l = (∏ g) * (1 + (∑ r) / length l)`.
    R3Cert/BGSpiderRule.lean      `W n`: for n >= 492, w4 n arms of 4, w6 n arms of 6, w5 n arms of 5,
                                  with s = 6(n-1) mod 11 (`sres`).
    R3Cert/BGSpiderTableData.lean `tab n` for n <= 491, read from `tabData` via `canon C s a b`
                                  (C cherries, a arms of s cherries, b arms of s+1), in BGSpiderTable.lean.
    R3Cert/BGStatement.lean       `bgChildren n := if n ≤ 491 then tab n else W n`.

  `F l` is the value, by the matching-sum formula, of the spider whose centre carries the children `l`
  (paper, Section 6); `bg_maximum_attained` also confirms it is the value of an actual tree.
-/
import R3Cert.BGStatement

open R3Cert.BGStatement R3Cert.BGSpiderOpt

/-- **Upper bound.** Every tree on `n ≥ 4` vertices has Laplacian ratio at most `F (bgChildren n)`. -/
theorem brualdi_goldwasser_upper (n : ℕ) (h4 : 4 ≤ n) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hV : Fintype.card V = n) :
    (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) ≤ (F (bgChildren n) : ℝ) :=
  bg_maximum_le n h4 G hG hV

/-- **Attainment.** Some tree on `n ≥ 4` vertices has Laplacian ratio exactly `F (bgChildren n)`. -/
theorem brualdi_goldwasser_attained (n : ℕ) (h4 : 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.IsTree ∧
      (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = (F (bgChildren n) : ℝ) :=
  bg_maximum_attained n h4

#print axioms brualdi_goldwasser_upper
#print axioms brualdi_goldwasser_attained
