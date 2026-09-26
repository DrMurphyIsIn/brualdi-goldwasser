/-
  The FOLDED-IDENTITY / telescoping increment: a plain-restricted valid potential and the induction
  `logPhi B <= -P(cav B)` for plain `B`, reducing `PlainConjecture` (and hence `Phi <= 1`) to the per-node
  super-solution at plain nodes.

  This mirrors the existing `Reach.logPhi_le_of_potential` (which needs the super-solution at ALL nodes,
  including cherries) but restricts to PLAIN nodes (`c = 0`), matching `Plainify.PlainConjecture`.  The
  explicit potential `Pval` (Potential.lean) is intended to satisfy `ValidPotentialPlain`; that per-node
  inequality (the crux, via Lemma A) is a subsequent increment.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.Plainify
import R3Cert.Potential

namespace R3Cert

open Real

/-- A **plain valid potential**: `P >= 0`, and the per-node super-solution at PLAIN nodes
    `eroot 0 ch <= (Σ_{b∈ch} P(cav b)) - P(cav (node 0 ch))`. -/
def ValidPotentialPlain (P : ℝ → ℝ) : Prop :=
  (∀ m, 0 ≤ P m) ∧
    (∀ ch : List Branch, IsPlainList ch →
      eroot 0 ch ≤ (ch.map (fun b => P (cav b))).sum - P (cav (Branch.node 0 ch)))

mutual
/-- Strong-induction step (branch), plain version: `logPhi B <= -P(cav B)`. -/
theorem logPhi_le_of_potentialPlain (P : ℝ → ℝ) (hP : ValidPotentialPlain P)
    (B : Branch) (hB : IsPlain B) : logPhi B ≤ - P (cav B) := by
  cases B with
  | node c ch =>
    obtain ⟨hc, hch⟩ := hB
    subst hc
    have hsum := logPhiSum_le_of_potentialPlain P hP ch hch
    have hstep := hP.2 ch hch
    rw [logPhi]; linarith [hsum, hstep]
/-- Strong-induction step (child list), plain version. -/
theorem logPhiSum_le_of_potentialPlain (P : ℝ → ℝ) (hP : ValidPotentialPlain P)
    (ch : List Branch) (hch : IsPlainList ch) :
    logPhiSum ch ≤ - (ch.map (fun b => P (cav b))).sum := by
  cases ch with
  | nil => rw [logPhiSum]; simp
  | cons b rest =>
    obtain ⟨hb, hrest⟩ := hch
    have h1 := logPhi_le_of_potentialPlain P hP b hb
    have h2 := logPhiSum_le_of_potentialPlain P hP rest hrest
    rw [logPhiSum]; simp only [List.map_cons, List.sum_cons]; linarith
end

/-- If `P` is a valid plain potential, every plain branch has `logPhi <= 0` (i.e. `PlainConjecture`). -/
theorem plainConjecture_of_validPlain (P : ℝ → ℝ) (hP : ValidPotentialPlain P) :
    PlainConjecture := by
  intro b hb
  have h := logPhi_le_of_potentialPlain P hP b hb
  have hpos := hP.1 (cav b)
  linarith

/-- ... and hence `Phi <= 1` for ALL branches (via the plainification reduction). -/
theorem phi_le_one_of_validPlain (P : ℝ → ℝ) (hP : ValidPotentialPlain P) (b : Branch) :
    logPhi b ≤ 0 :=
  phi_le_one_of_plain (plainConjecture_of_validPlain P hP) b

end R3Cert
