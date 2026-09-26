/-
  R3Cert.BGMaximizerFinal -- the Brualdi-Goldwasser maximizer for every n >= 492, unconditional.

  Brualdi and Goldwasser (1984) asked which tree on n vertices maximizes the Laplacian ratio
  pi(T) = per(L(T)) / prod_v deg(v).  For every n >= 492 the answer is the spider `W n`
  (R3Cert.BGSpiderRule): a centre carrying only arms (an arm is a vertex carrying cherries,
  i.e. pendant 2-paths), all with 5 cherries except, with s = 6(n-1) mod 11,
      s = 1..4 : s arms carry 6 cherries   (except s = 3, n <= 722 and s = 4, n <= 2319:
                                             11 - s arms carry 4 cherries),
      s = 5..10: 11 - s arms carry 4 cherries.

  Chain: `BGSpiderRule.bg_maximizer_of` (spider reduction `BGMax.bg_spider_reduction`, the closed
  form `Aobj_spiderU`, existence of a spider-family maximizer) with its two inputs
  `BGSpiderStruct.structProp_492` and `BGSpiderCand.candProp_492`.

  Kernel-checked, no `sorry`, only propext / Classical.choice / Quot.sound.  Sizes n <= 491 are
  settled by the certified exhaustive search proof/verification/bg_certified_interval.py (exact
  arithmetic, NOT Lean): every maximizer there is a spider, given by the table in
  proof/docs/BG_SPIDER_OPTIMIZATION_2026-09-24.md.
-/
import Mathlib
import R3Cert.BGSpiderRule
import R3Cert.BGSpiderStruct
import R3Cert.BGSpiderCand

namespace R3Cert
namespace BGMaximizerFinal

open R3Cert.RTree R3Cert.Step3 R3Cert.BGSpiderRule

/-- **The Brualdi-Goldwasser maximizer, n ≥ 492.**  The spider `W n` has `n` vertices, and every tree
    on `n` vertices has `Aobj ≤ Aobj (W n)`. -/
theorem bg_maximizer (n : ℕ) (hn : 492 ≤ n) :
    usize (spiderU (W n)) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (spiderU (W n)) :=
  bg_maximizer_of BGSpiderStruct.structProp_492 BGSpiderCand.candProp_492 n hn hn

/-- The same statement for the literal Laplacian permanent ratio. -/
theorem bg_maximizer_perm (n : ℕ) (hn : 492 ≤ n) (t : UTree) (ht : usize t = n) :
    (lapl (aGraph (Step3.realize (dtRealize t)))).permanent
        / (∏ v, ((aGraph (Step3.realize (dtRealize t))).degree v : ℝ))
      ≤ (lapl (aGraph (Step3.realize (dtRealize (spiderU (W n)))))).permanent
        / (∏ v, ((aGraph (Step3.realize (dtRealize (spiderU (W n))))).degree v : ℝ)) := by
  rw [pi_utree, pi_utree]
  exact (bg_maximizer n hn).2 t ht

end BGMaximizerFinal
end R3Cert
