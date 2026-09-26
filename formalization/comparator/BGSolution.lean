/-
  The Comparator SOLUTION: the same statements as `BGChallenge.lean`, proved.
-/
import R3Cert.BGStatement

open R3Cert.BGStatement R3Cert.BGSpiderOpt

namespace BGComparator

theorem upper (n : ℕ) (h4 : 4 ≤ n) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hV : Fintype.card V = n) :
    (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) ≤ (F (bgChildren n) : ℝ) :=
  bg_maximum_le n h4 G hG hV

theorem attained (n : ℕ) (h4 : 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.IsTree ∧
      (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = (F (bgChildren n) : ℝ) :=
  bg_maximum_attained n h4

end BGComparator
