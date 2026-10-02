/-
LeanCherry.PBRowsC10 -- certificate C10, the W2 conditions (T1)-(T8) on t in (0, 3/43] (9 conditions x 2 rows).
Generated row instances: each row is a box [t1, t2] with rational endpoint bounds of the monotone atoms
(Taylor sums of exp, checked by norm_num) and one rational inequality (norm_num).
-/
import LeanCherry.PBRowsCore

open Real

namespace LeanCherry
namespace PBC

noncomputable section

theorem w2_box_0 (t : ℝ) (ht : 0 < t) (h2 : t ≤ (3/86:ℝ)) : W2Enc t ((3 * (1:ℝ) + 3 / 4 * (9871423827/10000000000:ℝ)) / 7) ((3 * (2544646007/2500000000:ℝ) + 3 / 4 * (1:ℝ)) / 7) ((3 / 2 * (9871423827/10000000000:ℝ) - (2544646007/2500000000:ℝ)) / 7) ((3 / 2 * (1:ℝ) - (1:ℝ)) / 7) (4 / 5 * (1/12:ℝ) / 7) (4 / 5 * (1064123529/10000000000:ℝ) / 7) (2 / ((1 - (0:ℝ)) * (3 + 2 * (0:ℝ)))) (2 / ((1 - (3/86:ℝ)) * (3 + 2 * (3/86:ℝ)))) (1 / (5 + 4 * (3/86:ℝ))) (1 / (5 + 4 * (0:ℝ))) ((3 * (1:ℝ) + 3 / 4 * (9871423827/10000000000:ℝ)) / 7 * (1:ℝ)) ((3 * (2544646007/2500000000:ℝ) + 3 / 4 * (1:ℝ)) / 7 * (5047687559/5000000000:ℝ)) (5047687559/5000000000:ℝ) := by
  have E := enc_box0 (t2 := (3/86:ℝ)) (lmL := (1:ℝ)) (lmH := (2544646007/2500000000:ℝ)) (l34L := (9871423827/10000000000:ℝ)) (l34H := (1:ℝ)) (l23L := (308921651/312500000:ℝ)) (l23H := (1:ℝ)) ht h2 (by norm_num) (by norm_num)
      (le_trans (Lm_le_pt (p := (3/86:ℝ)) (b := (35506688467/1000000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (3/86:ℝ) / 4) (a := (25826399549/1000000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (by norm_num)
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (3/86:ℝ) / 3) (a := (11494759107/500000000000:ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (by norm_num)
  exact w2enc (t1 := (0:ℝ)) (t2 := (3/86:ℝ)) (xL := (1:ℝ)) (gL := (1/12:ℝ)) (gH := (1064123529/10000000000:ℝ)) (by norm_num) (le_of_lt ht) h2
    (by norm_num) ht E (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (3/86:ℝ) * ((3 * (2544646007/2500000000:ℝ) + 3 / 4 * (1:ℝ)) / 7)) 6 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num) (one_le_Xe (mul_pos ht (lt_of_lt_of_le (by norm_num) E.phi3_lo))))
    (G2t_ge ht (by linarith))
    (le_trans (G2t_mono ht h2 (by norm_num)) (le_trans (G2t_le_pt (p := (3/86:ℝ)) (b1 := (2582639957/100000000000:ℝ)) (a2 := (11494759107/500000000000:ℝ)) (b3 := (35506688467/1000000000000:ℝ)) 6 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num)))
    (by norm_num)

theorem w2_T_0 (t : ℝ) (ht : 0 < t) (h2 : t ≤ (3/86:ℝ)) :
    0 < kt t - e1 t ∧ 0 < et t - h2t t ∧ h2t t / (kt t - e1 t) ≤ (et t - h2t t) / (1 - kt t) ∧
    (et t - h2t t) / (1 - kt t) ≤ y4 t * (1 - t * kt t * y4 t) ∧ (kt t - e1 t) / h2t t ≤ 1 + 14 * (1 + t * e1 t) ∧
    Xe (t * phi3 t) ≤ 14 / 13 ∧ 0 ≤ phi3 t - kt t - h2t t + 2 * Real.sqrt (kt t * h2t t) ∧
    0 ≤ phi3 t + 5 * et t - 5 / 6 ∧ 1 / 36 ≤ et t := by
  have W := w2_box_0 t ht h2
  have c1 : (0:ℝ) < 2 / ((1 - (0:ℝ)) * (3 + 2 * (0:ℝ))) - (3 * (2544646007/2500000000:ℝ) + 3 / 4 * (1:ℝ)) / 7 * (5047687559/5000000000:ℝ) := by norm_num
  have c2 : (0:ℝ) < (3 / 2 * (9871423827/10000000000:ℝ) - (2544646007/2500000000:ℝ)) / 7 - 4 / 5 * (1064123529/10000000000:ℝ) / 7 := by norm_num
  have c3 : (2:ℝ) / ((1 - (3/86:ℝ)) * (3 + 2 * (3/86:ℝ))) < 1 := by norm_num
  exact ⟨W.T1 c1, W.T3a c2, W.T2 c1 c2 c3 (by norm_num), W.T4 (3/86:ℝ) h2 (by norm_num) c1 c2 c3 (by norm_num) (by norm_num) (by norm_num),
    W.T5 (0:ℝ) (le_of_lt ht) (by norm_num) (by norm_num) c1 (by norm_num), W.T6 (by norm_num),
    W.T7 (6225149/78125000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num), W.T8 (by norm_num), W.T8b (by norm_num)⟩

theorem w2_box_1 (t : ℝ) (h1 : (3/86:ℝ) ≤ t) (h2 : t ≤ (3/43:ℝ)) : W2Enc t ((3 * (10178584021/10000000000:ℝ) + 3 / 4 * (304598589/312500000:ℝ)) / 7) ((3 * (2073192299/2000000000:ℝ) + 3 / 4 * (2467855959/2500000000:ℝ)) / 7) ((3 / 2 * (304598589/312500000:ℝ) - (2073192299/2000000000:ℝ)) / 7) ((3 / 2 * (2467855959/2500000000:ℝ) - (10178584021/10000000000:ℝ)) / 7) (4 / 5 * (1064123449/10000000000:ℝ) / 7) (4 / 5 * (1303876881/10000000000:ℝ) / 7) (2 / ((1 - (3/86:ℝ)) * (3 + 2 * (3/86:ℝ)))) (2 / ((1 - (3/43:ℝ)) * (3 + 2 * (3/43:ℝ)))) (1 / (5 + 4 * (3/43:ℝ))) (1 / (5 + 4 * (3/86:ℝ))) ((3 * (10178584021/10000000000:ℝ) + 3 / 4 * (304598589/312500000:ℝ)) / 7 * (10094896609/10000000000:ℝ)) ((3 * (2073192299/2000000000:ℝ) + 3 / 4 * (2467855959/2500000000:ℝ)) / 7 * (2548586411/2500000000:ℝ)) (2548586411/2500000000:ℝ) := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (3/86:ℝ)) (t2 := (3/43:ℝ)) (lmL := (10178584021/10000000000:ℝ)) (lmH := (2073192299/2000000000:ℝ)) (l34L := (304598589/312500000:ℝ)) (l34H := (2467855959/2500000000:ℝ)) (l23L := (1221801303/1250000000:ℝ)) (l23H := (4942746421/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (3/86:ℝ)) (a := (17753344223/500000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (3/43:ℝ)) (b := (7232066159/100000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (3/43:ℝ) / 4) (a := (25501277221/500000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (3/86:ℝ) / 4) (b := (2582639957/100000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (3/43:ℝ) / 3) (a := (22731187033/500000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (3/86:ℝ) / 3) (b := (4597903647/200000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact w2enc (t1 := (3/86:ℝ)) (t2 := (3/43:ℝ)) (xL := (10094896609/10000000000:ℝ)) (gL := (1064123449/10000000000:ℝ)) (gH := (1303876881/10000000000:ℝ)) (by norm_num) h1 h2
    (by norm_num) ht E (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (3/43:ℝ) * ((3 * (2073192299/2000000000:ℝ) + 3 / 4 * (2467855959/2500000000:ℝ)) / 7)) 6 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (xe_lo (t1 := (3/86:ℝ)) (by norm_num) h1 (by norm_num) E.phi3_lo (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (3/86:ℝ) * ((3 * (10178584021/10000000000:ℝ) + 3 / 4 * (304598589/312500000:ℝ)) / 7)) 6 (by norm_num))))
    (le_trans (le_trans (by norm_num) (G2t_ge_pt (p := (3/86:ℝ)) (a1 := (25826399549/1000000000000:ℝ)) (b2 := (4597903647/200000000000:ℝ)) (a3 := (17753344223/500000000000:ℝ)) 6 6 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))) (G2t_mono (by norm_num) h1 (by linarith)))
    (le_trans (G2t_mono ht h2 (by norm_num)) (le_trans (G2t_le_pt (p := (3/43:ℝ)) (b1 := (51002554463/1000000000000:ℝ)) (a2 := (22731187033/500000000000:ℝ)) (b3 := (7232066159/100000000000:ℝ)) 7 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num)))
    (by norm_num)

theorem w2_T_1 (t : ℝ) (h1 : (3/86:ℝ) ≤ t) (h2 : t ≤ (3/43:ℝ)) :
    0 < kt t - e1 t ∧ 0 < et t - h2t t ∧ h2t t / (kt t - e1 t) ≤ (et t - h2t t) / (1 - kt t) ∧
    (et t - h2t t) / (1 - kt t) ≤ y4 t * (1 - t * kt t * y4 t) ∧ (kt t - e1 t) / h2t t ≤ 1 + 14 * (1 + t * e1 t) ∧
    Xe (t * phi3 t) ≤ 14 / 13 ∧ 0 ≤ phi3 t - kt t - h2t t + 2 * Real.sqrt (kt t * h2t t) ∧
    0 ≤ phi3 t + 5 * et t - 5 / 6 ∧ 1 / 36 ≤ et t := by
  have W := w2_box_1 t h1 h2
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have c1 : (0:ℝ) < 2 / ((1 - (3/86:ℝ)) * (3 + 2 * (3/86:ℝ))) - (3 * (2073192299/2000000000:ℝ) + 3 / 4 * (2467855959/2500000000:ℝ)) / 7 * (2548586411/2500000000:ℝ) := by norm_num
  have c2 : (0:ℝ) < (3 / 2 * (304598589/312500000:ℝ) - (2073192299/2000000000:ℝ)) / 7 - 4 / 5 * (1303876881/10000000000:ℝ) / 7 := by norm_num
  have c3 : (2:ℝ) / ((1 - (3/43:ℝ)) * (3 + 2 * (3/43:ℝ))) < 1 := by norm_num
  exact ⟨W.T1 c1, W.T3a c2, W.T2 c1 c2 c3 (by norm_num), W.T4 (3/43:ℝ) h2 (by norm_num) c1 c2 c3 (by norm_num) (by norm_num) (by norm_num),
    W.T5 (3/86:ℝ) h1 (by norm_num) (by norm_num) c1 (by norm_num), W.T6 (by norm_num),
    W.T7 (906075567/10000000000:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num), W.T8 (by norm_num), W.T8b (by norm_num)⟩

/-- certificate C10, scaled: (T1), (T3a), (T2), (T4), (T5), (T6), (T7), (T8), (T8b) on (0, 3/43] -/
theorem cert_C10_scaled (t : ℝ) (ht : 0 < t) (h2 : t ≤ (3/43:ℝ)) :
    0 < kt t - e1 t ∧ 0 < et t - h2t t ∧ h2t t / (kt t - e1 t) ≤ (et t - h2t t) / (1 - kt t) ∧
    (et t - h2t t) / (1 - kt t) ≤ y4 t * (1 - t * kt t * y4 t) ∧ (kt t - e1 t) / h2t t ≤ 1 + 14 * (1 + t * e1 t) ∧
    Xe (t * phi3 t) ≤ 14 / 13 ∧ 0 ≤ phi3 t - kt t - h2t t + 2 * Real.sqrt (kt t * h2t t) ∧
    0 ≤ phi3 t + 5 * et t - 5 / 6 ∧ 1 / 36 ≤ et t := by
  rcases le_or_gt t (3/86:ℝ) with h | h
  · exact w2_T_0 t ht h
  · exact w2_T_1 t h.le h2

end

end PBC
end LeanCherry
