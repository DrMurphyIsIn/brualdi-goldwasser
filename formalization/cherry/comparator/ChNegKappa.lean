/- Comparator control (challenge side): the three-piece window witness, but with slope kappa = 2 in place of
   kappa = f*/t. Constants as in `ChWinConst.lean`: y_C = 1/(2+l), f_C = log sqrt(1+l/2), eps = 2(f* - f_C),
   ydag = (e^{f*}-1)/l, w = y_C - ydag, s1 = eps/w.
   window_witness_kap2 : the bad-slope h is a witness on the window (FALSE; must be REJECTED, config `neg_kappa`).
   kap2_not_witness    : it is not a witness (must be ACCEPTED, config `kappa_refute`). -/
import ChWinConst

namespace LeanCherry

noncomputable section

open Br

def hWk2 (l y : ℝ) : ℝ := max (max 0 (s1W l * (y - ydag l))) (epsW l + 2 * (y - yC l))

theorem window_witness_kap2 (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) :
    Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hWk2 l) := by
  sorry

theorem kap2_not_witness (l : ℝ) (h1 : 3.22 ≤ l) (h2 : l < 1 + √5) :
    ¬ Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) (hWk2 l) := by
  sorry

end

end LeanCherry
