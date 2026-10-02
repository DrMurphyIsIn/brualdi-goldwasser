/-
LeanCherry.PBRowsC3 -- certificate C3, (S4) on t in (0, 6181/10000] (13 rows).
Generated row instances: each row is a box [t1, t2] with rational endpoint bounds of the monotone atoms
(Taylor sums of exp, checked by norm_num) and one rational inequality (norm_num).
-/
import LeanCherry.PBRowsCore

open Real

namespace LeanCherry
namespace PBC

noncomputable section

theorem c3_row_0 (t : ℝ) (ht : 0 < t) (h2 : t ≤ (241/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  exact S4_box (t1 := (0:ℝ)) (t2 := (241/2000:ℝ)) (R := (10663065529/10000000000:ℝ)) (by norm_num) (le_of_lt ht) h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_1 (t : ℝ) (h1 : (241/2000:ℝ) ≤ t) (h2 : t ≤ (47/250:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (241/2000:ℝ)) (t2 := (47/250:ℝ)) (R := (11097419041/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_2 (t : ℝ) (h1 : (47/250:ℝ) ≤ t) (h2 : t ≤ (117/500:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (47/250:ℝ)) (t2 := (117/500:ℝ)) (R := (11425773623/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_3 (t : ℝ) (h1 : (117/500:ℝ) ≤ t) (h2 : t ≤ (539/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (117/500:ℝ)) (t2 := (539/2000:ℝ)) (R := (292502713/250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_4 (t : ℝ) (h1 : (539/2000:ℝ) ≤ t) (h2 : t ≤ (599/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (539/2000:ℝ)) (t2 := (599/2000:ℝ)) (R := (5974009853/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_5 (t : ℝ) (h1 : (599/2000:ℝ) ≤ t) (h2 : t ≤ (131/400:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (599/2000:ℝ)) (t2 := (131/400:ℝ)) (R := (6097107609/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_6 (t : ℝ) (h1 : (131/400:ℝ) ≤ t) (h2 : t ≤ (71/200:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (131/400:ℝ)) (t2 := (71/200:ℝ)) (R := (97277001/78125000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_7 (t : ℝ) (h1 : (71/200:ℝ) ≤ t) (h2 : t ≤ (48/125:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (71/200:ℝ)) (t2 := (48/125:ℝ)) (R := (12741179787/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_8 (t : ℝ) (h1 : (48/125:ℝ) ≤ t) (h2 : t ≤ (833/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (48/125:ℝ)) (t2 := (833/2000:ℝ)) (R := (818200211/625000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_9 (t : ℝ) (h1 : (833/2000:ℝ) ≤ t) (h2 : t ≤ (911/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (833/2000:ℝ)) (t2 := (911/2000:ℝ)) (R := (13551927137/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_10 (t : ℝ) (h1 : (911/2000:ℝ) ≤ t) (h2 : t ≤ (507/1000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (911/2000:ℝ)) (t2 := (507/1000:ℝ)) (R := (7121091149/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_11 (t : ℝ) (h1 : (507/1000:ℝ) ≤ t) (h2 : t ≤ (1163/2000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (507/1000:ℝ)) (t2 := (1163/2000:ℝ)) (R := (15457963193/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_row_12 (t : ℝ) (h1 : (1163/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  exact S4_box (t1 := (1163/2000:ℝ)) (t2 := (6181/10000:ℝ)) (R := (1618173821/1000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht (by norm_num) (by norm_num)
    (by norm_num [gS, rhohat])

theorem c3_cov_12 (t : ℝ) (h1 : (1163/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 :=
  c3_row_12 t h1 h2

theorem c3_cov_11 (t : ℝ) (h1 : (507/1000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (1163/2000:ℝ) with h | h
  · exact c3_row_11 t h1 h
  · exact c3_cov_12 t h.le h2

theorem c3_cov_10 (t : ℝ) (h1 : (911/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (507/1000:ℝ) with h | h
  · exact c3_row_10 t h1 h
  · exact c3_cov_11 t h.le h2

theorem c3_cov_9 (t : ℝ) (h1 : (833/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (911/2000:ℝ) with h | h
  · exact c3_row_9 t h1 h
  · exact c3_cov_10 t h.le h2

theorem c3_cov_8 (t : ℝ) (h1 : (48/125:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (833/2000:ℝ) with h | h
  · exact c3_row_8 t h1 h
  · exact c3_cov_9 t h.le h2

theorem c3_cov_7 (t : ℝ) (h1 : (71/200:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (48/125:ℝ) with h | h
  · exact c3_row_7 t h1 h
  · exact c3_cov_8 t h.le h2

theorem c3_cov_6 (t : ℝ) (h1 : (131/400:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (71/200:ℝ) with h | h
  · exact c3_row_6 t h1 h
  · exact c3_cov_7 t h.le h2

theorem c3_cov_5 (t : ℝ) (h1 : (599/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (131/400:ℝ) with h | h
  · exact c3_row_5 t h1 h
  · exact c3_cov_6 t h.le h2

theorem c3_cov_4 (t : ℝ) (h1 : (539/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (599/2000:ℝ) with h | h
  · exact c3_row_4 t h1 h
  · exact c3_cov_5 t h.le h2

theorem c3_cov_3 (t : ℝ) (h1 : (117/500:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (539/2000:ℝ) with h | h
  · exact c3_row_3 t h1 h
  · exact c3_cov_4 t h.le h2

theorem c3_cov_2 (t : ℝ) (h1 : (47/250:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (117/500:ℝ) with h | h
  · exact c3_row_2 t h1 h
  · exact c3_cov_3 t h.le h2

theorem c3_cov_1 (t : ℝ) (h1 : (241/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (47/250:ℝ) with h | h
  · exact c3_row_1 t h1 h
  · exact c3_cov_2 t h.le h2

/-- certificate C3 -/
theorem cert_C3 (t : ℝ) (ht : 0 < t) (h2 : t ≤ (6181/10000:ℝ)) : 1291 / 1000 * gS (rhohat t) * t * (1 + 1 / Real.sqrt (1 - t)) < (1 + t) ^ 2 := by
  rcases le_or_gt t (241/2000:ℝ) with h | h
  · exact c3_row_0 t ht h
  · exact c3_cov_1 t h.le h2

end

end PBC
end LeanCherry
