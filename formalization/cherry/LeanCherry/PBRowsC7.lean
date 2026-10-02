/-
LeanCherry.PBRowsC7 -- certificate C7, (S6) for W* on t in [3/43, 3229/10000] (17 rows).
Generated row instances: each row is a box [t1, t2] with rational endpoint bounds of the monotone atoms
(Taylor sums of exp, checked by norm_num) and one rational inequality (norm_num).
-/
import LeanCherry.PBRowsCore

open Real

namespace LeanCherry
namespace PBC

noncomputable section

theorem c7_row_0 (t : ℝ) (h1 : (3/43:ℝ) ≤ t) (h2 : t ≤ (1543/21500:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (3/43:ℝ)) (t2 := (1543/21500:ℝ)) (lmL := (10365961491/10000000000:ℝ)) (lmH := (10376986309/10000000000:ℝ)) (l34L := (9740155611/10000000000:ℝ)) (l34H := (9747154853/10000000000:ℝ)) (l23L := (1221017741/1250000000:ℝ)) (l23H := (9774410429/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (3/43:ℝ)) (a := (72320661569/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (1543/21500:ℝ)) (b := (37236488079/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (1543/21500:ℝ) / 4) (a := (13106738467/250000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (3/43:ℝ) / 4) (b := (51002554463/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (1543/21500:ℝ) / 3) (a := (46735637197/1000000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (3/43:ℝ) / 3) (b := (45462374087/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (3/43:ℝ)) (t2 := (1543/21500:ℝ)) (xL := (2038768461/2000000000:ℝ)) (xH := (2549918557/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (1543/21500:ℝ) * ((3 * (10376986309/10000000000:ℝ) + 3 / 4 * (9747154853/10000000000:ℝ)) / 7)) 6 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (3/43:ℝ) * ((3 * (10365961491/10000000000:ℝ) + 3 / 4 * (9740155611/10000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_1 (t : ℝ) (h1 : (1543/21500:ℝ) ≤ t) (h2 : t ≤ (6387/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (1543/21500:ℝ)) (t2 := (6387/86000:ℝ)) (lmL := (2075397261/2000000000:ℝ)) (lmH := (10390811671/10000000000:ℝ)) (l34L := (9731425303/10000000000:ℝ)) (l34H := (304379863/312500000:ℝ)) (l23L := (4880160653/5000000000:ℝ)) (l23H := (4884070967/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1543/21500:ℝ)) (a := (74472976137/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (6387/86000:ℝ)) (b := (15433980033/200000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (6387/86000:ℝ) / 4) (a := (54204604723/1000000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1543/21500:ℝ) / 4) (b := (52426953889/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (6387/86000:ℝ) / 3) (a := (302030873/6250000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1543/21500:ℝ) / 3) (b := (23367818609/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (1543/21500:ℝ)) (t2 := (6387/86000:ℝ)) (xL := (509980607/500000000:ℝ)) (xH := (318966329/312500000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (6387/86000:ℝ) * ((3 * (10390811671/10000000000:ℝ) + 3 / 4 * (304379863/312500000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (1543/21500:ℝ) * ((3 * (2075397261/2000000000:ℝ) + 3 / 4 * (9731425303/10000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_2 (t : ℝ) (h1 : (6387/86000:ℝ) ≤ t) (h2 : t ≤ (1329/17200:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (6387/86000:ℝ)) (t2 := (1329/17200:ℝ)) (lmL := (2597702917/2500000000:ℝ)) (lmH := (520373377/500000000:ℝ)) (l34L := (2430244077/2500000000:ℝ)) (l34H := (2432856327/2500000000:ℝ)) (l23L := (4875479239/5000000000:ℝ)) (l23H := (305010041/312500000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (6387/86000:ℝ)) (a := (4823118759/62500000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (1329/17200:ℝ)) (b := (10051979913/125000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (1329/17200:ℝ) / 4) (a := (28166811439/500000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (6387/86000:ℝ) / 4) (b := (6775575593/125000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (1329/17200:ℝ) / 3) (a := (6278596811/125000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (6387/86000:ℝ) / 3) (b := (48324939701/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (6387/86000:ℝ)) (t2 := (1329/17200:ℝ)) (xL := (637927757/625000000:ℝ)) (xH := (10215646801/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (1329/17200:ℝ) * ((3 * (520373377/500000000:ℝ) + 3 / 4 * (2432856327/2500000000:ℝ)) / 7)) 6 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (6387/86000:ℝ) * ((3 * (2597702917/2500000000:ℝ) + 3 / 4 * (2430244077/2500000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_3 (t : ℝ) (h1 : (1329/17200:ℝ) ≤ t) (h2 : t ≤ (6989/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (1329/17200:ℝ)) (t2 := (6989/86000:ℝ)) (lmL := (10407467537/10000000000:ℝ)) (lmH := (10429787261/10000000000:ℝ)) (l34L := (970709053/1000000000:ℝ)) (l34H := (1215122039/1250000000:ℝ)) (l23L := (9738511733/10000000000:ℝ)) (l23H := (9750958483/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1329/17200:ℝ)) (a := (80415839283/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (6989/86000:ℝ)) (b := (10595026623/125000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (6989/86000:ℝ) / 4) (a := (462228759/7812500000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1329/17200:ℝ) / 4) (b := (56333622899/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (6989/86000:ℝ) / 3) (a := (2638079787/50000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1329/17200:ℝ) / 3) (b := (50228774509/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (1329/17200:ℝ)) (t2 := (6989/86000:ℝ)) (xL := (10215543169/10000000000:ℝ)) (xH := (127841647/125000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (6989/86000:ℝ) * ((3 * (10429787261/10000000000:ℝ) + 3 / 4 * (1215122039/1250000000:ℝ)) / 7)) 6 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (1329/17200:ℝ) * ((3 * (10407467537/10000000000:ℝ) + 3 / 4 * (970709053/1000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_4 (t : ℝ) (h1 : (6989/86000:ℝ) ≤ t) (h2 : t ≤ (461/5375:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (6989/86000:ℝ)) (t2 := (461/5375:ℝ)) (lmL := (5214893629/5000000000:ℝ)) (lmH := (10455051239/10000000000:ℝ)) (l34L := (4845765891/5000000000:ℝ)) (l34H := (1941418107/2000000000:ℝ)) (l23L := (1215569931/1250000000:ℝ)) (l23H := (4869255869/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (6989/86000:ℝ)) (a := (84760212963/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (461/5375:ℝ)) (b := (3586811997/40000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (461/5375:ℝ) / 4) (a := (62341341653/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (6989/86000:ℝ) / 4) (b := (59165281173/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (461/5375:ℝ) / 3) (a := (13900843119/250000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (6989/86000:ℝ) / 3) (b := (52761595761/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (6989/86000:ℝ)) (t2 := (461/5375:ℝ)) (xL := (10227199677/10000000000:ℝ)) (xH := (10240533073/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (461/5375:ℝ) * ((3 * (10455051239/10000000000:ℝ) + 3 / 4 * (1941418107/2000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (6989/86000:ℝ) * ((3 * (5214893629/5000000000:ℝ) + 3 / 4 * (4845765891/5000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_5 (t : ℝ) (h1 : (461/5375:ℝ) ≤ t) (h2 : t ≤ (1973/21500:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (461/5375:ℝ)) (t2 := (1973/21500:ℝ)) (lmL := (2613762809/2500000000:ℝ)) (lmH := (10488993693/10000000000:ℝ)) (l34L := (9670889347/10000000000:ℝ)) (l34H := (4845765893/5000000000:ℝ)) (l23L := (303313709/312500000:ℝ)) (l23H := (9724559453/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (461/5375:ℝ)) (a := (350274609/3906250000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (1973/21500:ℝ)) (b := (48127405943/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (1973/21500:ℝ) / 4) (a := (4160028637/62500000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (461/5375:ℝ) / 4) (b := (31170670837/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (1973/21500:ℝ) / 3) (a := (296899447/5000000000:ℝ)) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (461/5375:ℝ) / 3) (b := (55603372497/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (461/5375:ℝ)) (t2 := (1973/21500:ℝ)) (xL := (2560090349/2500000000:ℝ)) (xH := (10258257947/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (1973/21500:ℝ) * ((3 * (10488993693/10000000000:ℝ) + 3 / 4 * (4845765893/5000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (461/5375:ℝ) * ((3 * (2613762809/2500000000:ℝ) + 3 / 4 * (9670889347/10000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_6 (t : ℝ) (h1 : (1973/21500:ℝ) ≤ t) (h2 : t ≤ (4247/43000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (1973/21500:ℝ)) (t2 := (4247/43000:ℝ)) (lmL := (1048899369/1000000000:ℝ)) (lmH := (658060627/625000000:ℝ)) (l34L := (4823476643/5000000000:ℝ)) (l34H := (9670889351/10000000000:ℝ)) (l23L := (9684549009/10000000000:ℝ)) (l23H := (2426509673/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1973/21500:ℝ)) (a := (19250962373/200000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (4247/43000:ℝ)) (b := (103991943547/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (4247/43000:ℝ) / 4) (a := (71460367339/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1973/21500:ℝ) / 4) (b := (66560458213/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (4247/43000:ℝ) / 3) (a := (63767875419/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1973/21500:ℝ) / 3) (b := (59379889421/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (1973/21500:ℝ)) (t2 := (4247/43000:ℝ)) (xL := (5129015617/5000000000:ℝ)) (xH := (5139542201/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (4247/43000:ℝ) * ((3 * (658060627/625000000:ℝ) + 3 / 4 * (9670889351/10000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (1973/21500:ℝ) * ((3 * (1048899369/1000000000:ℝ) + 3 / 4 * (4823476643/5000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_7 (t : ℝ) (h1 : (4247/43000:ℝ) ≤ t) (h2 : t ≤ (2317/21500:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (4247/43000:ℝ)) (t2 := (2317/21500:ℝ)) (lmL := (10528970029/10000000000:ℝ)) (lmH := (2645243847/2500000000:ℝ)) (l34L := (4808203973/5000000000:ℝ)) (l34H := (964695329/1000000000:ℝ)) (l23L := (9657104029/10000000000:ℝ)) (l23H := (4842274507/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (4247/43000:ℝ)) (a := (51995971763/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (2317/21500:ℝ)) (b := (11402846499/100000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (2317/21500:ℝ) / 4) (a := (38862588159/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (4247/43000:ℝ) / 4) (b := (13957103/195312500:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (2317/21500:ℝ) / 3) (a := (6938142647/100000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (4247/43000:ℝ) / 3) (b := (797098443/12500000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (4247/43000:ℝ)) (t2 := (2317/21500:ℝ)) (xL := (2569696347/2500000000:ℝ)) (xH := (10306133811/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (2317/21500:ℝ) * ((3 * (2645243847/2500000000:ℝ) + 3 / 4 * (964695329/1000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (4247/43000:ℝ) * ((3 * (10528970029/10000000000:ℝ) + 3 / 4 * (4808203973/5000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_8 (t : ℝ) (h1 : (2317/21500:ℝ) ≤ t) (h2 : t ≤ (5107/43000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (2317/21500:ℝ)) (t2 := (5107/43000:ℝ)) (lmL := (2116195077/2000000000:ℝ)) (lmH := (10645486277/10000000000:ℝ)) (l34L := (9579420599/10000000000:ℝ)) (l34H := (9616407949/10000000000:ℝ)) (l23L := (9623838653/10000000000:ℝ)) (l23H := (9657104033/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (2317/21500:ℝ)) (a := (114028464969/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (5107/43000:ℝ)) (b := (31608429311/250000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (5107/43000:ℝ) / 4) (a := (17065849187/200000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (2317/21500:ℝ) / 4) (b := (77725176339/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (5107/43000:ℝ) / 3) (a := (76199913183/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (2317/21500:ℝ) / 3) (b := (69381426491/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (2317/21500:ℝ)) (t2 := (5107/43000:ℝ)) (xL := (5152863991/5000000000:ℝ)) (xH := (10339591259/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (5107/43000:ℝ) * ((3 * (10645486277/10000000000:ℝ) + 3 / 4 * (9616407949/10000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (2317/21500:ℝ) * ((3 * (2116195077/2000000000:ℝ) + 3 / 4 * (9579420599/10000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_9 (t : ℝ) (h1 : (5107/43000:ℝ) ≤ t) (h2 : t ≤ (91/688:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (5107/43000:ℝ)) (t2 := (91/688:ℝ)) (lmL := (5322743137/5000000000:ℝ)) (lmH := (10726125989/10000000000:ℝ)) (l34L := (953453801/1000000000:ℝ)) (l34H := (9579420603/10000000000:ℝ)) (l23L := (239585629/250000000:ℝ)) (l23H := (9623838657/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (5107/43000:ℝ)) (a := (126433717223/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (91/688:ℝ)) (b := (141871724551/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (91/688:ℝ) / 4) (a := (94583171401/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (5107/43000:ℝ) / 4) (b := (21332311489/250000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (91/688:ℝ) / 3) (a := (42252504343/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (5107/43000:ℝ) / 3) (b := (19049978301/250000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (5107/43000:ℝ)) (t2 := (91/688:ℝ)) (xL := (413561869/400000000:ℝ)) (xH := (10381282357/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (91/688:ℝ) * ((3 * (10726125989/10000000000:ℝ) + 3 / 4 * (9579420603/10000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (5107/43000:ℝ) * ((3 * (5322743137/5000000000:ℝ) + 3 / 4 * (953453801/1000000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_10 (t : ℝ) (h1 : (91/688:ℝ) ≤ t) (h2 : t ≤ (6397/43000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (91/688:ℝ)) (t2 := (6397/43000:ℝ)) (lmL := (5363062993/5000000000:ℝ)) (lmH := (10826959813/10000000000:ℝ)) (l34L := (2370107559/2500000000:ℝ)) (l34H := (9534538013/10000000000:ℝ)) (l23L := (4767318097/5000000000:ℝ)) (l23H := (2395856291/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (91/688:ℝ)) (a := (14187172453/100000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (6397/43000:ℝ)) (b := (161069911443/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (6397/43000:ℝ) / 4) (a := (26444612889/250000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (91/688:ℝ) / 4) (b := (47291585711/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (6397/43000:ℝ) / 3) (a := (47281447857/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (91/688:ℝ) / 3) (b := (84505008707/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (91/688:ℝ)) (t2 := (6397/43000:ℝ)) (xL := (10380545199/10000000000:ℝ)) (xH := (1304151757/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (6397/43000:ℝ) * ((3 * (10826959813/10000000000:ℝ) + 3 / 4 * (9534538013/10000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (91/688:ℝ) * ((3 * (5363062993/5000000000:ℝ) + 3 / 4 * (2370107559/2500000000:ℝ)) / 7)) 7 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_11 (t : ℝ) (h1 : (6397/43000:ℝ) ≤ t) (h2 : t ≤ (14557/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (6397/43000:ℝ)) (t2 := (14557/86000:ℝ)) (lmL := (10826959811/10000000000:ℝ)) (lmH := (10955879363/10000000000:ℝ)) (l34L := (2353580879/2500000000:ℝ)) (l34H := (9480430239/10000000000:ℝ)) (l23L := (9474925891/10000000000:ℝ)) (l23H := (9534636197/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (6397/43000:ℝ)) (a := (80534955711/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (14557/86000:ℝ)) (b := (1448807557/7812500000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (14557/86000:ℝ) / 4) (a := (14939423049/125000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (6397/43000:ℝ) / 4) (b := (105778451577/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (14557/86000:ℝ) / 3) (a := (106919764503/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (6397/43000:ℝ) / 3) (b := (18912579147/200000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (6397/43000:ℝ)) (t2 := (14557/86000:ℝ)) (xL := (5216100257/5000000000:ℝ)) (xH := (419972563/400000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (14557/86000:ℝ) * ((3 * (10955879363/10000000000:ℝ) + 3 / 4 * (9480430239/10000000000:ℝ)) / 7)) 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (6397/43000:ℝ) * ((3 * (10826959811/10000000000:ℝ) + 3 / 4 * (2353580879/2500000000:ℝ)) / 7)) 8 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_12 (t : ℝ) (h1 : (14557/86000:ℝ) ≤ t) (h2 : t ≤ (16707/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (14557/86000:ℝ)) (t2 := (16707/86000:ℝ)) (lmL := (34237123/31250000:ℝ)) (lmH := (2779717013/2500000000:ℝ)) (l34L := (9335330721/10000000000:ℝ)) (l34H := (9414323519/10000000000:ℝ)) (l23L := (9403429913/10000000000:ℝ)) (l23H := (4737462947/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (14557/86000:ℝ)) (a := (7417894691/40000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (16707/86000:ℝ)) (b := (216003405271/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (16707/86000:ℝ) / 4) (a := (27203262273/200000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (14557/86000:ℝ) / 4) (b := (119515384413/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (16707/86000:ℝ) / 3) (a := (121785351601/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (14557/86000:ℝ) / 3) (b := (26729941131/250000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (14557/86000:ℝ)) (t2 := (16707/86000:ℝ)) (xL := (10497910499/10000000000:ℝ)) (xH := (10582412023/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (16707/86000:ℝ) * ((3 * (2779717013/2500000000:ℝ) + 3 / 4 * (9414323519/10000000000:ℝ)) / 7)) 8 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (14557/86000:ℝ) * ((3 * (34237123/31250000:ℝ) + 3 / 4 * (9335330721/10000000000:ℝ)) / 7)) 8 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_13 (t : ℝ) (h1 : (16707/86000:ℝ) ≤ t) (h2 : t ≤ (19373/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (16707/86000:ℝ)) (t2 := (19373/86000:ℝ)) (lmL := (222377361/200000000:ℝ)) (lmH := (2266083313/2000000000:ℝ)) (l34L := (4619883697/5000000000:ℝ)) (l34H := (2333832681/2500000000:ℝ)) (l23L := (4658361899/5000000000:ℝ)) (l23H := (2350857479/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (16707/86000:ℝ)) (a := (864013621/4000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (19373/86000:ℝ)) (b := (255237395467/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (19373/86000:ℝ) / 4) (a := (15610640733/100000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (16707/86000:ℝ) / 4) (b := (68008155693/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (19373/86000:ℝ) / 3) (a := (139916969107/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (16707/86000:ℝ) / 3) (b := (60892675811/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (16707/86000:ℝ)) (t2 := (19373/86000:ℝ)) (xL := (20664949/19531250:ℝ)) (xH := (5344790921/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (19373/86000:ℝ) * ((3 * (2266083313/2000000000:ℝ) + 3 / 4 * (2333832681/2500000000:ℝ)) / 7)) 8 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (16707/86000:ℝ) * ((3 * (222377361/200000000:ℝ) + 3 / 4 * (4619883697/5000000000:ℝ)) / 7)) 8 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_14 (t : ℝ) (h1 : (19373/86000:ℝ) ≤ t) (h2 : t ≤ (22641/86000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (19373/86000:ℝ)) (t2 := (22641/86000:ℝ)) (lmL := (11330416563/10000000000:ℝ)) (lmH := (11605321553/10000000000:ℝ)) (l34L := (9126069927/10000000000:ℝ)) (l34H := (2309941849/2500000000:ℝ)) (l23L := (4606631559/5000000000:ℝ)) (l23H := (46583619/50000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (19373/86000:ℝ)) (a := (127618697723/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (22641/86000:ℝ)) (b := (305530331711/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (22641/86000:ℝ) / 4) (a := (36038956259/200000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (19373/86000:ℝ) / 4) (b := (156106407351/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (22641/86000:ℝ) / 3) (a := (8085174041/50000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (19373/86000:ℝ) / 3) (b := (17489621141/125000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (19373/86000:ℝ)) (t2 := (22641/86000:ℝ)) (xL := (2137364699/2000000000:ℝ)) (xH := (2165554101/2000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (22641/86000:ℝ) * ((3 * (11605321553/10000000000:ℝ) + 3 / 4 * (2309941849/2500000000:ℝ)) / 7)) 8 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (19373/86000:ℝ) * ((3 * (11330416563/10000000000:ℝ) + 3 / 4 * (9126069927/10000000000:ℝ)) / 7)) 8 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_15 (t : ℝ) (h1 : (22641/86000:ℝ) ≤ t) (h2 : t ≤ (13363/43000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (22641/86000:ℝ)) (t2 := (13363/43000:ℝ)) (lmL := (11605321551/10000000000:ℝ)) (lmH := (239520931/200000000:ℝ)) (l34L := (2247248723/2500000000:ℝ)) (l34H := (9126069929/10000000000:ℝ)) (l23L := (9088097221/10000000000:ℝ)) (l23H := (115165789/125000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (22641/86000:ℝ)) (a := (30553033169/100000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (13363/43000:ℝ)) (b := (186088267487/500000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (13363/43000:ℝ) / 4) (a := (209511521073/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (22641/86000:ℝ) / 4) (b := (45048695329/250000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (13363/43000:ℝ) / 3) (a := (47071412081/250000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (22641/86000:ℝ) / 3) (b := (161703480841/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (22641/86000:ℝ)) (t2 := (13363/43000:ℝ)) (xL := (1082384171/1000000000:ℝ)) (xH := (1376564591/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (13363/43000:ℝ) * ((3 * (239520931/200000000:ℝ) + 3 / 4 * (9126069929/10000000000:ℝ)) / 7)) 8 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (22641/86000:ℝ) * ((3 * (11605321551/10000000000:ℝ) + 3 / 4 * (2247248723/2500000000:ℝ)) / 7)) 9 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_row_16 (t : ℝ) (h1 : (13363/43000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  have E := enc_box (t1 := (13363/43000:ℝ)) (t2 := (3229/10000:ℝ)) (lmL := (2994011637/2500000000:ℝ)) (lmH := (12076070193/10000000000:ℝ)) (l34L := (4477420777/5000000000:ℝ)) (l34H := (4494497447/5000000000:ℝ)) (l23L := (4528418971/5000000000:ℝ)) (l23H := (9088097223/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (13363/43000:ℝ)) (a := (372176534953/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (3229/10000:ℝ)) (b := (389936306501/1000000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (3229/10000:ℝ) / 4) (a := (108431937673/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (13363/43000:ℝ) / 4) (b := (104755760547/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (3229/10000:ℝ) / 3) (a := (97481765719/500000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (13363/43000:ℝ) / 3) (b := (37657129669/200000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S6_box (t1 := (13363/43000:ℝ)) (t2 := (3229/10000:ℝ)) (xL := (1100927877/1000000000:ℝ)) (xH := (5529965353/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) E
    (by norm_num) (by norm_num)
    (le_trans (Xe_le_pt (s := (3229/10000:ℝ) * ((3 * (12076070193/10000000000:ℝ) + 3 / 4 * (4494497447/5000000000:ℝ)) / 7)) 8 (by norm_num) (by norm_num) (by norm_num)) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial]))
    (le_trans (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial]) (Xe_ge_pt (s := (13363/43000:ℝ) * ((3 * (2994011637/2500000000:ℝ) + 3 / 4 * (4477420777/5000000000:ℝ)) / 7)) 9 (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem c7_cov_16 (t : ℝ) (h1 : (13363/43000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t :=
  c7_row_16 t h1 h2

theorem c7_cov_15 (t : ℝ) (h1 : (22641/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (13363/43000:ℝ) with h | h
  · exact c7_row_15 t h1 h
  · exact c7_cov_16 t h.le h2

theorem c7_cov_14 (t : ℝ) (h1 : (19373/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (22641/86000:ℝ) with h | h
  · exact c7_row_14 t h1 h
  · exact c7_cov_15 t h.le h2

theorem c7_cov_13 (t : ℝ) (h1 : (16707/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (19373/86000:ℝ) with h | h
  · exact c7_row_13 t h1 h
  · exact c7_cov_14 t h.le h2

theorem c7_cov_12 (t : ℝ) (h1 : (14557/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (16707/86000:ℝ) with h | h
  · exact c7_row_12 t h1 h
  · exact c7_cov_13 t h.le h2

theorem c7_cov_11 (t : ℝ) (h1 : (6397/43000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (14557/86000:ℝ) with h | h
  · exact c7_row_11 t h1 h
  · exact c7_cov_12 t h.le h2

theorem c7_cov_10 (t : ℝ) (h1 : (91/688:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (6397/43000:ℝ) with h | h
  · exact c7_row_10 t h1 h
  · exact c7_cov_11 t h.le h2

theorem c7_cov_9 (t : ℝ) (h1 : (5107/43000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (91/688:ℝ) with h | h
  · exact c7_row_9 t h1 h
  · exact c7_cov_10 t h.le h2

theorem c7_cov_8 (t : ℝ) (h1 : (2317/21500:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (5107/43000:ℝ) with h | h
  · exact c7_row_8 t h1 h
  · exact c7_cov_9 t h.le h2

theorem c7_cov_7 (t : ℝ) (h1 : (4247/43000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (2317/21500:ℝ) with h | h
  · exact c7_row_7 t h1 h
  · exact c7_cov_8 t h.le h2

theorem c7_cov_6 (t : ℝ) (h1 : (1973/21500:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (4247/43000:ℝ) with h | h
  · exact c7_row_6 t h1 h
  · exact c7_cov_7 t h.le h2

theorem c7_cov_5 (t : ℝ) (h1 : (461/5375:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (1973/21500:ℝ) with h | h
  · exact c7_row_5 t h1 h
  · exact c7_cov_6 t h.le h2

theorem c7_cov_4 (t : ℝ) (h1 : (6989/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (461/5375:ℝ) with h | h
  · exact c7_row_4 t h1 h
  · exact c7_cov_5 t h.le h2

theorem c7_cov_3 (t : ℝ) (h1 : (1329/17200:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (6989/86000:ℝ) with h | h
  · exact c7_row_3 t h1 h
  · exact c7_cov_4 t h.le h2

theorem c7_cov_2 (t : ℝ) (h1 : (6387/86000:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (1329/17200:ℝ) with h | h
  · exact c7_row_2 t h1 h
  · exact c7_cov_3 t h.le h2

theorem c7_cov_1 (t : ℝ) (h1 : (1543/21500:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (6387/86000:ℝ) with h | h
  · exact c7_row_1 t h1 h
  · exact c7_cov_2 t h.le h2

theorem c7_cov_0 (t : ℝ) (h1 : (3/43:ℝ) ≤ t) (h2 : t ≤ (3229/10000:ℝ)) : 0 < 1 - e1 t ∧ 0 < et t * (3 / 2 + (1 - kt t) / (1 - e1 t)) - D2t t := by
  rcases le_or_gt t (1543/21500:ℝ) with h | h
  · exact c7_row_0 t h1 h
  · exact c7_cov_1 t h.le h2

end

end PBC
end LeanCherry
