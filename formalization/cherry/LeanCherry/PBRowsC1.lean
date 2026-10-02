/-
LeanCherry.PBRowsC1 -- certificate C1, (S2) on t in (0, 6181/10000] (10 rows).
Generated row instances: each row is a box [t1, t2] with rational endpoint bounds of the monotone atoms
(Taylor sums of exp, checked by norm_num) and one rational inequality (norm_num).
-/
import LeanCherry.PBRowsCore

open Real

namespace LeanCherry
namespace PBC

noncomputable section

theorem c1_row_0 (t : ℝ) (ht : 0 < t) (h2 : t ≤ (213/2000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have E := enc_box0 (t2 := (213/2000:ℝ)) (lmL := (1:ℝ)) (lmH := (10573609803/10000000000:ℝ)) (l34L := (1924138809/2000000000:ℝ)) (l34H := (1:ℝ)) (l23L := (4830478271/5000000000:ℝ)) (l23H := (1:ℝ)) ht h2 (by norm_num) (by norm_num)
      (le_trans (Lm_le_pt (p := (213/2000:ℝ)) (b := (112608944393/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (213/2000:ℝ) / 4) (a := (38422646843/500000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (by norm_num)
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (213/2000:ℝ) / 3) (a := (13718558291/200000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (by norm_num)
  exact S2_box (t1 := (0:ℝ)) (t2 := (213/2000:ℝ)) (LqH := (1:ℝ)) (by norm_num) (le_of_lt ht) h2 (by norm_num) ht E
    (Lq_box0 ht (by linarith) (by norm_num))
    (by norm_num)

theorem c1_row_1 (t : ℝ) (h1 : (213/2000:ℝ) ≤ t) (h2 : t ≤ (87/400:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (213/2000:ℝ)) (t2 := (87/400:ℝ)) (lmL := (52868049/50000000:ℝ)) (lmH := (11276384211/10000000000:ℝ)) (l34L := (9263469633/10000000000:ℝ)) (l34H := (300646689/312500000:ℝ)) (l23L := (9338250827/10000000000:ℝ)) (l23H := (4830478273/5000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (213/2000:ℝ)) (a := (28152236093/250000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (87/400:ℝ)) (b := (122630678289/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (87/400:ℝ) / 4) (a := (37777587101/250000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (213/2000:ℝ) / 4) (b := (76845293707/1000000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (87/400:ℝ) / 3) (a := (33851159249/250000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (213/2000:ℝ) / 3) (b := (17148197869/250000000000:ℝ)) 7 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (213/2000:ℝ)) (t2 := (87/400:ℝ)) (LqH := (486690291/500000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (213/2000:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (213/2000:ℝ) * q3 (213/2000:ℝ)) (b := (26859891301/500000000000:ℝ)) 7 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_2 (t : ℝ) (h1 : (87/400:ℝ) ≤ t) (h2 : t ≤ (159/500:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (87/400:ℝ)) (t2 := (159/500:ℝ)) (lmL := (11276384209/10000000000:ℝ)) (lmH := (3008849223/2500000000:ℝ)) (l34L := (8968594127/10000000000:ℝ)) (l34H := (2315867409/2500000000:ℝ)) (l23L := (4534714331/5000000000:ℝ)) (l23H := (9338250829/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (87/400:ℝ)) (a := (245261356557/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (159/500:ℝ)) (b := (382725621149/1000000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (159/500:ℝ) / 4) (a := (213900969937/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (87/400:ℝ) / 4) (b := (6044413937/40000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (159/500:ℝ) / 3) (a := (192271887637/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (87/400:ℝ) / 3) (b := (135404637017/1000000000000:ℝ)) 8 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (87/400:ℝ)) (t2 := (159/500:ℝ)) (LqH := (1180783001/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (87/400:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (87/400:ℝ) * q3 (87/400:ℝ)) (b := (56435010801/500000000000:ℝ)) 8 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_3 (t : ℝ) (h1 : (159/500:ℝ) ≤ t) (h2 : t ≤ (803/2000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (159/500:ℝ)) (t2 := (803/2000:ℝ)) (lmL := (1203539689/1000000000:ℝ)) (lmH := (12785274073/10000000000:ℝ)) (l34L := (8741528429/10000000000:ℝ)) (l34H := (8968594129/10000000000:ℝ)) (l23L := (8860944219/10000000000:ℝ)) (l23H := (1133678583/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (159/500:ℝ)) (a := (47840702641/125000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (803/2000:ℝ)) (b := (102665750799/200000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (803/2000:ℝ) / 4) (a := (263229274843/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (159/500:ℝ) / 4) (b := (106950484979/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (803/2000:ℝ) / 3) (a := (59294485067/250000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (159/500:ℝ) / 3) (b := (96135943829/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (159/500:ℝ)) (t2 := (803/2000:ℝ)) (LqH := (9162402499/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (159/500:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (159/500:ℝ) * q3 (159/500:ℝ)) (b := (34494996127/200000000000:ℝ)) 9 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_4 (t : ℝ) (h1 : (803/2000:ℝ) ≤ t) (h2 : t ≤ (117/250:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (803/2000:ℝ)) (t2 := (117/250:ℝ)) (lmL := (12785274071/10000000000:ℝ)) (lmH := (13485294651/10000000000:ℝ)) (l34L := (8571084301/10000000000:ℝ)) (l34H := (8741528431/10000000000:ℝ)) (l23L := (13925779/16000000:ℝ)) (l23H := (8860944221/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (803/2000:ℝ)) (a := (256664376987/500000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (117/250:ℝ)) (b := (631111789651/1000000000000:ℝ)) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (117/250:ℝ) / 4) (a := (37605632371/125000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (803/2000:ℝ) / 4) (b := (16451829679/62500000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (117/250:ℝ) / 3) (a := (271552690511/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (803/2000:ℝ) / 3) (b := (237177940289/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (803/2000:ℝ)) (t2 := (117/250:ℝ)) (LqH := (889700369/1000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (803/2000:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (803/2000:ℝ) * q3 (803/2000:ℝ)) (b := (28669898891/125000000000:ℝ)) 9 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_5 (t : ℝ) (h1 : (117/250:ℝ) ≤ t) (h2 : t ≤ (13/25:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (117/250:ℝ)) (t2 := (13/25:ℝ)) (lmL := (269705893/200000000:ℝ)) (lmH := (14114791829/10000000000:ℝ)) (l34L := (8443685823/10000000000:ℝ)) (l34H := (4285542151/5000000000:ℝ)) (l23L := (1717110019/2000000000:ℝ)) (l23H := (8703611877/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (117/250:ℝ)) (a := (63111178963/100000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (13/25:ℝ)) (b := (733969175091/1000000000000:ℝ)) 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (13/25:ℝ) / 4) (a := (82325936783/250000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (117/250:ℝ) / 4) (b := (300845058989/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (13/25:ℝ) / 3) (a := (148816201647/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (117/250:ℝ) / 3) (b := (67888172633/250000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (117/250:ℝ)) (t2 := (13/25:ℝ)) (LqH := (1082110531/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (117/250:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (117/250:ℝ) * q3 (117/250:ℝ)) (b := (281845098587/1000000000000:ℝ)) 10 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_6 (t : ℝ) (h1 : (13/25:ℝ) ≤ t) (h2 : t ≤ (1121/2000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (13/25:ℝ)) (t2 := (1121/2000:ℝ)) (lmL := (3528697957/2500000000:ℝ)) (lmH := (14667574699/10000000000:ℝ)) (l34L := (834780663/1000000000:ℝ)) (l34H := (337747433/400000000:ℝ)) (l23L := (8496437921/10000000000:ℝ)) (l23H := (536596881/625000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (13/25:ℝ)) (a := (73396917507/100000000000:ℝ)) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (1121/2000:ℝ)) (b := (822117561867/1000000000000:ℝ)) 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (1121/2000:ℝ) / 4) (a := (175460460623/500000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (13/25:ℝ) / 4) (b := (329303747153/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (1121/2000:ℝ) / 3) (a := (158741781839/500000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (13/25:ℝ) / 3) (b := (59526480663/200000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (13/25:ℝ)) (t2 := (1121/2000:ℝ)) (LqH := (2111171183/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (13/25:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (13/25:ℝ) * q3 (13/25:ℝ)) (b := (10283732531/31250000000:ℝ)) 10 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_7 (t : ℝ) (h1 : (1121/2000:ℝ) ≤ t) (h2 : t ≤ (74/125:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (1121/2000:ℝ)) (t2 := (74/125:ℝ)) (lmL := (7333787349/5000000000:ℝ)) (lmH := (7571690073/5000000000:ℝ)) (l34L := (1034394821/1250000000:ℝ)) (l34H := (1043475829/1250000000:ℝ)) (l23L := (4214384773/5000000000:ℝ)) (l23H := (8496437923/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1121/2000:ℝ)) (a := (411058780923/500000000000:ℝ)) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (74/125:ℝ)) (b := (224122026147/250000000000:ℝ)) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (74/125:ℝ) / 4) (a := (18370852023/50000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1121/2000:ℝ) / 4) (b := (350920921267/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (74/125:ℝ) / 3) (a := (83163859521/250000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1121/2000:ℝ) / 3) (b := (317483563699/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (1121/2000:ℝ)) (t2 := (74/125:ℝ)) (LqH := (2065047099/2500000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (1121/2000:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (1121/2000:ℝ) * q3 (1121/2000:ℝ)) (b := (37082898707/100000000000:ℝ)) 10 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_8 (t : ℝ) (h1 : (74/125:ℝ) ≤ t) (h2 : t ≤ (1233/2000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (74/125:ℝ)) (t2 := (1233/2000:ℝ)) (lmL := (946461259/625000000:ℝ)) (lmH := (15546077181/10000000000:ℝ)) (l34L := (8219774563/10000000000:ℝ)) (l34H := (827515857/1000000000:ℝ)) (l23L := (8377096663/10000000000:ℝ)) (l23H := (8428769547/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (74/125:ℝ)) (a := (896488104567/1000000000000:ℝ)) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (1233/2000:ℝ)) (b := (191683131637/200000000000:ℝ)) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (1233/2000:ℝ) / 4) (a := (3040494611/8000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (74/125:ℝ) / 4) (b := (367417040481/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (1233/2000:ℝ) / 3) (a := (17214933643/50000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (74/125:ℝ) / 3) (b := (66531087621/200000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (74/125:ℝ)) (t2 := (1233/2000:ℝ)) (LqH := (1012792013/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (74/125:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (74/125:ℝ) * q3 (74/125:ℝ)) (b := (50884395851/125000000000:ℝ)) 11 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_row_9 (t : ℝ) (h1 : (1233/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) h1
  have E := enc_box (t1 := (1233/2000:ℝ)) (t2 := (6181/10000:ℝ)) (lmL := (777303859/500000000:ℝ)) (lmH := (389336873/250000000:ℝ)) (l34L := (1027023871/1250000000:ℝ)) (l34H := (2054943641/2500000000:ℝ)) (l23L := (4186875331/5000000000:ℝ)) (l23H := (1047137083/1250000000:ℝ)) (by norm_num) h1 h2 (by norm_num)
      (le_trans (by norm_num) (Lm_ge_pt (p := (1233/2000:ℝ)) (a := (239603914541/250000000000:ℝ)) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lm_le_pt (p := (6181/10000:ℝ)) (b := (962596484761/1000000000000:ℝ)) 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 3 * (6181/10000:ℝ) / 4) (a := (380882072837/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 3 * (1233/2000:ℝ) / 4) (b := (95015456599/250000000000:ℝ)) 11 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
      (le_trans (by norm_num) (Lg_ge_pt (x := 2 * (6181/10000:ℝ) / 3) (a := (345054352299/1000000000000:ℝ)) 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [expUp, Finset.sum_range_succ, Nat.factorial])))
      (le_trans (Lg_le_pt (x := 2 * (1233/2000:ℝ) / 3) (b := (344298672881/1000000000000:ℝ)) 10 (by norm_num) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial])) (by norm_num))
  exact S2_box (t1 := (1233/2000:ℝ)) (t2 := (6181/10000:ℝ)) (LqH := (7969262147/10000000000:ℝ)) (by norm_num) h1 h2 (by norm_num) ht E
    (Lq_box (t1 := (1233/2000:ℝ)) (by norm_num) h1 (by linarith) (le_trans (Lg_le_pt (x := (1233/2000:ℝ) * q3 (1233/2000:ℝ)) (b := (87604632421/200000000000:ℝ)) 11 (by norm_num [q3]) (by norm_num) (by norm_num [expLo, Finset.sum_range_succ, Nat.factorial, q3])) (by norm_num [q3])))
    (by norm_num)

theorem c1_cov_9 (t : ℝ) (h1 : (1233/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t :=
  c1_row_9 t h1 h2

theorem c1_cov_8 (t : ℝ) (h1 : (74/125:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (1233/2000:ℝ) with h | h
  · exact c1_row_8 t h1 h
  · exact c1_cov_9 t h.le h2

theorem c1_cov_7 (t : ℝ) (h1 : (1121/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (74/125:ℝ) with h | h
  · exact c1_row_7 t h1 h
  · exact c1_cov_8 t h.le h2

theorem c1_cov_6 (t : ℝ) (h1 : (13/25:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (1121/2000:ℝ) with h | h
  · exact c1_row_6 t h1 h
  · exact c1_cov_7 t h.le h2

theorem c1_cov_5 (t : ℝ) (h1 : (117/250:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (13/25:ℝ) with h | h
  · exact c1_row_5 t h1 h
  · exact c1_cov_6 t h.le h2

theorem c1_cov_4 (t : ℝ) (h1 : (803/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (117/250:ℝ) with h | h
  · exact c1_row_4 t h1 h
  · exact c1_cov_5 t h.le h2

theorem c1_cov_3 (t : ℝ) (h1 : (159/500:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (803/2000:ℝ) with h | h
  · exact c1_row_3 t h1 h
  · exact c1_cov_4 t h.le h2

theorem c1_cov_2 (t : ℝ) (h1 : (87/400:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (159/500:ℝ) with h | h
  · exact c1_row_2 t h1 h
  · exact c1_cov_3 t h.le h2

theorem c1_cov_1 (t : ℝ) (h1 : (213/2000:ℝ) ≤ t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (87/400:ℝ) with h | h
  · exact c1_row_1 t h1 h
  · exact c1_cov_2 t h.le h2

/-- certificate C1, scaled -/
theorem cert_C1_scaled (t : ℝ) (ht : 0 < t) (h2 : t ≤ (6181/10000:ℝ)) : q3 t * Lg (t * q3 t) < phi3 t := by
  rcases le_or_gt t (213/2000:ℝ) with h | h
  · exact c1_row_0 t ht h
  · exact c1_cov_1 t h.le h2

end

end PBC
end LeanCherry
