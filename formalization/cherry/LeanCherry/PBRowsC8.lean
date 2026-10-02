/-
LeanCherry.PBRowsC8 -- certificate C8, (S6) for lam >= 2, on t in [1/2, 6181/10000] (1 row).
Generated row instances: each row is a box [t1, t2] with rational endpoint bounds of the monotone atoms
(Taylor sums of exp, checked by norm_num) and one rational inequality (norm_num).
-/
import LeanCherry.PBRowsCore

open Real

namespace LeanCherry
namespace PBC

noncomputable section

/-- certificate C8, scaled (one row) -/
theorem cert_C8_scaled (t : ℝ) (h1 : (1/2:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : r8 t < Lm t / 2 - 2 / 3 * Lg (2 * t / 3) := by
  have E := enc_box (t1 := (1/2:ℝ)) (t2 := (6181/10000:ℝ)) (lmL := (1386294361/1000000000:ℝ)) (lmH := (389336873/250000000:ℝ)) (l34L := (1027023871/1250000000:ℝ)) (l34H := (8492099497/10000000000:ℝ)) (l23L := (4186875331/5000000000:ℝ)) (l23H := (4315231087/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1/2:ℝ)) (a := (693147180549/1000000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (6181/10000:ℝ)) (b := (962596484761/1000000000000:ℝ)) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (6181/10000:ℝ) / 4) (a := (380882072837/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1/2:ℝ) / 4) (b := (318453731129/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (6181/10000:ℝ) / 3) (a := (345054352299/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1/2:ℝ) / 3) (b := (143841036231/500000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6hi_box (t1 := (1/2:ℝ)) (t2 := (6181/10000:ℝ)) (by norm_num) h1 h2 (by norm_num) E (by norm_num)

end

end PBC
end LeanCherry
