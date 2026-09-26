/-
  R3Cert.BGMaximizerAll -- the Brualdi-Goldwasser problem, solved: the maximizer for EVERY n >= 4.

  Brualdi and Goldwasser (1984) asked which trees on n vertices maximize the Laplacian ratio
  per(L(T)) / prod_v deg(v).  For every n >= 4 an explicit spider `bgMax n` -- a centre carrying cherries
  (pendant 2-paths) and arms (vertices carrying cherries) -- maximizes it:
    * n <= 491 : the table spider `tab n` (BGSpiderTableData, generated from the exact optimization);
    * n >= 492 : the rule spider `W n` (BGSpiderRule): only arms, all with 5 cherries except, with
                 s = 6(n-1) mod 11, s arms of 6 (s = 1..4; for s = 3, n <= 722 and s = 4, n <= 2319 instead
                 11-s arms of 4) or 11-s arms of 4 (s = 5..10).
  (For n <= 3 there is only one tree of each size.)
  Assembled from bg_maximizer_tiny (4..6), bg_maximizer_small (7..149), bg_maximizer_mid (150..491) and
  bg_maximizer (>= 492).  Kernel-checked, no `sorry`, standard axioms only.
-/
import Mathlib
import R3Cert.BGMaximizerTiny
import R3Cert.BGMaximizerSmall
import R3Cert.BGMaximizerMid
import R3Cert.BGMaximizerFinal

namespace R3Cert
namespace BGMaximizerAll

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSpiderRule R3Cert.BGSpiderTable

/-- The Brualdi-Goldwasser maximizer on `n` vertices. -/
def bgMax (n : ℕ) : UTree := if n ≤ 491 then spiderU (tab n) else spiderU (W n)

/-- **The Brualdi-Goldwasser maximizer, every `n ≥ 4`.**  `bgMax n` has `n` vertices and maximizes
    `Aobj` (the Laplacian ratio) over all trees on `n` vertices. -/
theorem bg_maximizer_all (n : ℕ) (h4 : 4 ≤ n) :
    usize (bgMax n) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (bgMax n) := by
  unfold bgMax
  by_cases h491 : n ≤ 491
  · rw [if_pos h491]
    by_cases h6 : n ≤ 6
    · exact BGMaximizerTiny.bg_maximizer_tiny n h4 h6
    · by_cases h149 : n ≤ 149
      · exact BGMaximizerSmall.bg_maximizer_small n (by omega) h149
      · exact BGMaximizerMid.bg_maximizer_mid n (by omega) h491
  · rw [if_neg h491]
    exact BGMaximizerFinal.bg_maximizer n (by omega)

/-- **The same, for the literal Laplacian permanent ratio of the realized graphs.** -/
theorem bg_maximizer_all_perm (n : ℕ) (h4 : 4 ≤ n) (t : UTree) (ht : usize t = n) :
    (lapl (aGraph (Step3.realize (dtRealize t)))).permanent
        / (∏ v, ((aGraph (Step3.realize (dtRealize t))).degree v : ℝ))
      ≤ (lapl (aGraph (Step3.realize (dtRealize (bgMax n))))).permanent
        / (∏ v, ((aGraph (Step3.realize (dtRealize (bgMax n)))).degree v : ℝ)) := by
  rw [pi_utree, pi_utree]
  exact (bg_maximizer_all n h4).2 t ht

end BGMaximizerAll
end R3Cert
