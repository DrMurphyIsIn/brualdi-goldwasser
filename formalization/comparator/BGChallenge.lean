/-
  The Comparator CHALLENGE: the Brualdi-Goldwasser theorem, stated in Mathlib's vocabulary, with no
  proof.  It imports only the definitions of the answer (`R3Cert.BGAnswer`: the closed form `F` and the
  list `bgChildren n`), not the proof.  Comparator checks that `BGSolution` proves exactly these
  statements, using only the axioms propext, Quot.sound and Classical.choice, and replays the proof in
  Lean's kernel and in nanoda (an independent Rust implementation of the Lean kernel).
  The `sorry`s below are the challenge's by design; the proofs are in `BGSolution.lean`.
-/
import R3Cert.BGAnswer

open R3Cert.BGStatement R3Cert.BGSpiderOpt

namespace BGComparator

theorem upper (n : ℕ) (h4 : 4 ≤ n) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hV : Fintype.card V = n) :
    (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) ≤ (F (bgChildren n) : ℝ) := by
  sorry

theorem attained (n : ℕ) (h4 : 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.IsTree ∧
      (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = (F (bgChildren n) : ℝ) := by
  sorry

end BGComparator
