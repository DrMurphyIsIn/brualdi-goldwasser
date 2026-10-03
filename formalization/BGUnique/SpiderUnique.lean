import Mathlib
import R3Cert.BGSpiderStruct
import R3Cert.BGSpiderCand
import BGUnique.StrictCerts

namespace R3Cert
namespace SpiderStrict

open BGSpiderOpt BGSpiderRule BGSpiderStruct BGSpiderCand

lemma isMax_perm {l l' : List Child} (h : l.Perm l') (hm : IsMax l) : IsMax l' := by
  intro x hx
  rw [← F_perm h]
  exact hm x (hx.trans (nv_perm h).symm)

/-- Exchange: a cherry and a 4-arm become a 5-arm. -/
theorem exchange_cherry_four (rest : List Child) (hlen : 43 ≤ rest.length) :
    F ([Child.cherry, Child.arm 4] ++ rest) < F ([Child.arm 5] ++ rest) := by
  have hb := sum_r_bounds rest 0 1 (fun c hc => ⟨r_nonneg c, r_le_one c⟩)
  apply F_exchange_lt _ _ _ (115 / 114)
  · norm_num [Child.g, alpha]
  · simp
  · simp
  · set X := (rest.length : ℚ) with hXdef
    set Y := (rest.map Child.r).sum with hYdef
    have hX : (43 : ℚ) ≤ X := by rw [hXdef]; exact_mod_cast hlen
    have hY : 0 ≤ Y := by have := hb.1; simp at this; linarith
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg (sub_nonneg.2 hX) hY, sq_nonneg (X - 43), mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hX)]

/-- Exchange: a cherry and a 5-arm become a 6-arm (remainder messages at least 1/9). -/
theorem exchange_cherry_five (rest : List Child) (hr : ∀ c ∈ rest, 1 / 9 ≤ c.r) (hlen : 36 ≤ rest.length) :
    F ([Child.cherry, Child.arm 5] ++ rest) < F ([Child.arm 6] ++ rest) := by
  have hb := sum_r_bounds rest (1 / 9) 1 (fun c hc => ⟨hr c hc, r_le_one c⟩)
  apply F_exchange_lt _ _ _ (162 / 161)
  · norm_num [Child.g, alpha]
  · simp
  · simp
  · set X := (rest.length : ℚ) with hXdef
    set Y := (rest.map Child.r).sum with hYdef
    have hX : (36 : ℚ) ≤ X := by rw [hXdef]; exact_mod_cast hlen
    have hY : X / 9 ≤ Y := by have := hb.1; linarith
    norm_num [Child.r, bb]
    nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hY), sq_nonneg (X - 36),
      mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hX), sub_nonneg.2 hY]

lemma r_ge_ninth_of_adm (c : Child) (h : c = Child.cherry ∨ c = Child.arm 4 ∨ c = Child.arm 5 ∨ c = Child.arm 6) :
    1 / 9 ≤ c.r := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [Child.r, bb]

/-- A maximizer on at least 492 vertices has no cherry at the centre. -/
theorem no_cherry {l : List Child} (hmax : IsMax l) (hn : 492 ≤ nv l) : l.count Child.cherry = 0 := by
  obtain ⟨hc8, hadm, h46, h4c, h6c⟩ := cand_of_isMax hmax hn
  by_contra hne
  have hch : Child.cherry ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero hne)
  have hcnt := counts_eq l hadm
  by_cases h4m : Child.arm 4 ∈ l
  · have h6n : Child.arm 6 ∉ l := fun h => h46 ⟨h4m, h⟩
    have hcost : ∀ c ∈ l, c.cost ≤ 11 := by
      intro c hc
      rcases hadm c hc with rfl | rfl | rfl | rfl
      · simp [Child.cost]
      · simp [Child.cost]
      · simp [Child.cost]
      · exact absurd hc h6n
    have hlen := length_ge_of_cost hmax hn 11 hcost
    have h4e : Child.arm 4 ∈ l.erase Child.cherry := (List.mem_erase_of_ne (by decide)).mpr h4m
    have hp : l.Perm ([Child.cherry, Child.arm 4] ++ (l.erase Child.cherry).erase (Child.arm 4)) :=
      (List.perm_cons_erase hch).trans (List.Perm.cons _ (List.perm_cons_erase h4e))
    have hm' := isMax_perm hp hmax
    have hrl := hp.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hrl
    have hlt := exchange_cherry_four ((l.erase Child.cherry).erase (Child.arm 4)) (by omega)
    have hnv : nv ([Child.arm 5] ++ (l.erase Child.cherry).erase (Child.arm 4)) =
        nv ([Child.cherry, Child.arm 4] ++ (l.erase Child.cherry).erase (Child.arm 4)) := by
      simp only [nv, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Child.cost]
      omega
    exact absurd (hm' _ hnv) (not_le.mpr hlt)
  · have h5m : Child.arm 5 ∈ l := by
      by_contra h5n
      have e4 : c4 l = 0 := List.count_eq_zero_of_not_mem h4m
      have e5 : c5 l = 0 := List.count_eq_zero_of_not_mem h5n
      have hs := hcnt.2.2.2
      simp only [nv] at hn
      rw [e4, e5] at hs
      simp only [cC, c6] at hs
      omega
    have hcost : ∀ c ∈ l, c.cost ≤ 13 := by
      intro c hc
      rcases hadm c hc with rfl | rfl | rfl | rfl <;> simp [Child.cost]
    have hlen := length_ge_of_cost hmax hn 13 hcost
    have h5e : Child.arm 5 ∈ l.erase Child.cherry := (List.mem_erase_of_ne (by decide)).mpr h5m
    have hp : l.Perm ([Child.cherry, Child.arm 5] ++ (l.erase Child.cherry).erase (Child.arm 5)) :=
      (List.perm_cons_erase hch).trans (List.Perm.cons _ (List.perm_cons_erase h5e))
    have hm' := isMax_perm hp hmax
    have hrl := hp.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hrl
    have hr : ∀ c ∈ (l.erase Child.cherry).erase (Child.arm 5), 1 / 9 ≤ c.r := by
      intro c hc
      exact r_ge_ninth_of_adm c (hadm c (List.mem_of_mem_erase (List.mem_of_mem_erase hc)))
    have hlt := exchange_cherry_five ((l.erase Child.cherry).erase (Child.arm 5)) hr (by omega)
    have hnv : nv ([Child.arm 6] ++ (l.erase Child.cherry).erase (Child.arm 5)) =
        nv ([Child.cherry, Child.arm 5] ++ (l.erase Child.cherry).erase (Child.arm 5)) := by
      simp only [nv, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Child.cost]
      omega
    exact absurd (hm' _ hnv) (not_le.mpr hlt)

theorem scombo_0_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 0))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 0 + 11 * b + 13 * 0))) :
    Φ 0 0 b 0 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 0)) (w5 (1 + 9 * 0 + 11 * b + 13 * 0)) (w6 (1 + 9 * 0 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 0) = 0 := by unfold sres; omega
  have hw := w_zero _ hs
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 0) = 0 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_0_1 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 1))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 1) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 1) ∧ 1 = w6 (1 + 9 * 0 + 11 * b + 13 * 1))) :
    Φ 0 0 b 1 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 1)) (w5 (1 + 9 * 0 + 11 * b + 13 * 1)) (w6 (1 + 9 * 0 + 11 * b + 13 * 1)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 1) = 1 := by unfold sres; omega
  have hw := w_six _ 1 hs (by omega) (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 1) = 0 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 1) = 1 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 1) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_0_2 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 2))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 2) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 2) ∧ 2 = w6 (1 + 9 * 0 + 11 * b + 13 * 2))) :
    Φ 0 0 b 2 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 2)) (w5 (1 + 9 * 0 + 11 * b + 13 * 2)) (w6 (1 + 9 * 0 + 11 * b + 13 * 2)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 2) = 2 := by unfold sres; omega
  have hw := w_six _ 2 hs (by omega) (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 2) = 0 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 2) = 2 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 2) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_0_3 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 3))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 3) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 3) ∧ 3 = w6 (1 + 9 * 0 + 11 * b + 13 * 3))) :
    Φ 0 0 b 3 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 3)) (w5 (1 + 9 * 0 + 11 * b + 13 * 3)) (w6 (1 + 9 * 0 + 11 * b + 13 * 3)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 3) = 3 := by unfold sres; omega
  rcases Nat.lt_or_ge (1 + 9 * 0 + 11 * b + 13 * 3) 723 with hlo | hhi
  · have hw := w_four _ 3 hs (by omega) (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 3 := ⟨b - 3, by omega⟩
    have h4 : w4 (1 + 9 * 0 + 11 * (m + 3) + 13 * 3) = 8 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 0 + 11 * (m + 3) + 13 * 3) = 0 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 0 + 11 * (m + 3) + 13 * 3) = m + 0 := by unfold w5; rw [h4, h6]; omega
    rw [h4, h5, h6]
    exact strict_cert_3_X m (by omega) (by omega)
  · have hw := w_six _ 3 hs (by omega) (by omega) (by omega)
    have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 3) = 0 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 3) = 3 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 3) = b := by unfold w5; rw [h4, h6]; omega
    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_0_4 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 4))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 4) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 4) ∧ 4 = w6 (1 + 9 * 0 + 11 * b + 13 * 4))) :
    Φ 0 0 b 4 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 4)) (w5 (1 + 9 * 0 + 11 * b + 13 * 4)) (w6 (1 + 9 * 0 + 11 * b + 13 * 4)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 4) = 4 := by unfold sres; omega
  rcases Nat.lt_or_ge (1 + 9 * 0 + 11 * b + 13 * 4) 2320 with hlo | hhi
  · have hw := w_four _ 4 hs (by omega) (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    have h4 : w4 (1 + 9 * 0 + 11 * (m + 1) + 13 * 4) = 7 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 0 + 11 * (m + 1) + 13 * 4) = 0 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 0 + 11 * (m + 1) + 13 * 4) = m + 0 := by unfold w5; rw [h4, h6]; omega
    rw [h4, h5, h6]
    exact strict_cert_4_X m (by omega) (by omega)
  · have hw := w_six _ 4 hs (by omega) (by omega) (by omega)
    have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 4) = 0 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 4) = 4 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 4) = b := by unfold w5; rw [h4, h6]; omega
    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_0_5 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 5))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 5) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 5) ∧ 5 = w6 (1 + 9 * 0 + 11 * b + 13 * 5))) :
    Φ 0 0 b 5 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 5)) (w5 (1 + 9 * 0 + 11 * b + 13 * 5)) (w6 (1 + 9 * 0 + 11 * b + 13 * 5)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 5) = 5 := by unfold sres; omega
  have hw := w_four _ 5 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 5) = 6 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 5) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 5) = b + 1 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_5_X b (by omega)

theorem scombo_0_6 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 6))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 6) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 6) ∧ 6 = w6 (1 + 9 * 0 + 11 * b + 13 * 6))) :
    Φ 0 0 b 6 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 6)) (w5 (1 + 9 * 0 + 11 * b + 13 * 6)) (w6 (1 + 9 * 0 + 11 * b + 13 * 6)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 6) = 6 := by unfold sres; omega
  have hw := w_four _ 6 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 6) = 5 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 6) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 6) = b + 3 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_6_X b (by omega)

theorem scombo_0_7 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 7))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 7) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 7) ∧ 7 = w6 (1 + 9 * 0 + 11 * b + 13 * 7))) :
    Φ 0 0 b 7 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 7)) (w5 (1 + 9 * 0 + 11 * b + 13 * 7)) (w6 (1 + 9 * 0 + 11 * b + 13 * 7)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 7) = 7 := by unfold sres; omega
  have hw := w_four _ 7 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 7) = 4 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 7) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 7) = b + 5 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_7_X b (by omega)

theorem scombo_0_8 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 8))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 8) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 8) ∧ 8 = w6 (1 + 9 * 0 + 11 * b + 13 * 8))) :
    Φ 0 0 b 8 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 8)) (w5 (1 + 9 * 0 + 11 * b + 13 * 8)) (w6 (1 + 9 * 0 + 11 * b + 13 * 8)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 8) = 8 := by unfold sres; omega
  have hw := w_four _ 8 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 8) = 3 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 8) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 8) = b + 7 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_8_X b (by omega)

theorem scombo_0_9 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 9))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 9) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 9) ∧ 9 = w6 (1 + 9 * 0 + 11 * b + 13 * 9))) :
    Φ 0 0 b 9 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 9)) (w5 (1 + 9 * 0 + 11 * b + 13 * 9)) (w6 (1 + 9 * 0 + 11 * b + 13 * 9)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 9) = 9 := by unfold sres; omega
  have hw := w_four _ 9 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 9) = 2 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 9) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 9) = b + 9 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_9_X b (by omega)

theorem scombo_0_10 (b : ℕ) (hn : 492 ≤ (1 + 9 * 0 + 11 * b + 13 * 10))
    (hne : ¬ (0 = w4 (1 + 9 * 0 + 11 * b + 13 * 10) ∧ b = w5 (1 + 9 * 0 + 11 * b + 13 * 10) ∧ 10 = w6 (1 + 9 * 0 + 11 * b + 13 * 10))) :
    Φ 0 0 b 10 < Φ 0 (w4 (1 + 9 * 0 + 11 * b + 13 * 10)) (w5 (1 + 9 * 0 + 11 * b + 13 * 10)) (w6 (1 + 9 * 0 + 11 * b + 13 * 10)) := by
  have hs : sres (1 + 9 * 0 + 11 * b + 13 * 10) = 10 := by unfold sres; omega
  have hw := w_four _ 10 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 0 + 11 * b + 13 * 10) = 1 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 0 + 11 * b + 13 * 10) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 0 + 11 * b + 13 * 10) = b + 11 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_10_X b (by omega)

theorem scombo_10_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 10 + 11 * b + 13 * 0))
    (hne : ¬ (10 = w4 (1 + 9 * 10 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 10 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 10 + 11 * b + 13 * 0))) :
    Φ 0 10 b 0 < Φ 0 (w4 (1 + 9 * 10 + 11 * b + 13 * 0)) (w5 (1 + 9 * 10 + 11 * b + 13 * 0)) (w6 (1 + 9 * 10 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 10 + 11 * b + 13 * 0) = 1 := by unfold sres; omega
  have hw := w_six _ 1 hs (by omega) (by omega) (by omega)
  have h4 : w4 (1 + 9 * 10 + 11 * b + 13 * 0) = 0 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 10 + 11 * b + 13 * 0) = 1 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 10 + 11 * b + 13 * 0) = b + 7 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_1_Y b (by omega)

theorem scombo_9_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 9 + 11 * b + 13 * 0))
    (hne : ¬ (9 = w4 (1 + 9 * 9 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 9 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 9 + 11 * b + 13 * 0))) :
    Φ 0 9 b 0 < Φ 0 (w4 (1 + 9 * 9 + 11 * b + 13 * 0)) (w5 (1 + 9 * 9 + 11 * b + 13 * 0)) (w6 (1 + 9 * 9 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 9 + 11 * b + 13 * 0) = 2 := by unfold sres; omega
  have hw := w_six _ 2 hs (by omega) (by omega) (by omega)
  have h4 : w4 (1 + 9 * 9 + 11 * b + 13 * 0) = 0 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 9 + 11 * b + 13 * 0) = 2 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 9 + 11 * b + 13 * 0) = b + 5 := by unfold w5; rw [h4, h6]; omega
  rw [h4, h5, h6]
  exact strict_cert_2_Y b (by omega)

theorem scombo_8_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 8 + 11 * b + 13 * 0))
    (hne : ¬ (8 = w4 (1 + 9 * 8 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 8 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 8 + 11 * b + 13 * 0))) :
    Φ 0 8 b 0 < Φ 0 (w4 (1 + 9 * 8 + 11 * b + 13 * 0)) (w5 (1 + 9 * 8 + 11 * b + 13 * 0)) (w6 (1 + 9 * 8 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 8 + 11 * b + 13 * 0) = 3 := by unfold sres; omega
  rcases Nat.lt_or_ge (1 + 9 * 8 + 11 * b + 13 * 0) 723 with hlo | hhi
  · have hw := w_four _ 3 hs (by omega) (by omega)
    have h4 : w4 (1 + 9 * 8 + 11 * b + 13 * 0) = 8 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 8 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 8 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne
  · have hw := w_six _ 3 hs (by omega) (by omega) (by omega)
    have h4 : w4 (1 + 9 * 8 + 11 * b + 13 * 0) = 0 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 8 + 11 * b + 13 * 0) = 3 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 8 + 11 * b + 13 * 0) = b + 3 := by unfold w5; rw [h4, h6]; omega
    rw [h4, h5, h6]
    exact strict_cert_3_Y b (by omega)

theorem scombo_7_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 7 + 11 * b + 13 * 0))
    (hne : ¬ (7 = w4 (1 + 9 * 7 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 7 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 7 + 11 * b + 13 * 0))) :
    Φ 0 7 b 0 < Φ 0 (w4 (1 + 9 * 7 + 11 * b + 13 * 0)) (w5 (1 + 9 * 7 + 11 * b + 13 * 0)) (w6 (1 + 9 * 7 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 7 + 11 * b + 13 * 0) = 4 := by unfold sres; omega
  rcases Nat.lt_or_ge (1 + 9 * 7 + 11 * b + 13 * 0) 2320 with hlo | hhi
  · have hw := w_four _ 4 hs (by omega) (by omega)
    have h4 : w4 (1 + 9 * 7 + 11 * b + 13 * 0) = 7 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 7 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 7 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne
  · have hw := w_six _ 4 hs (by omega) (by omega) (by omega)
    have h4 : w4 (1 + 9 * 7 + 11 * b + 13 * 0) = 0 := by have := hw.1; omega
    have h6 : w6 (1 + 9 * 7 + 11 * b + 13 * 0) = 4 := by have := hw.2; omega
    have h5 : w5 (1 + 9 * 7 + 11 * b + 13 * 0) = b + 1 := by unfold w5; rw [h4, h6]; omega
    rw [h4, h5, h6]
    exact strict_cert_4_Y b (by omega)

theorem scombo_6_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 6 + 11 * b + 13 * 0))
    (hne : ¬ (6 = w4 (1 + 9 * 6 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 6 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 6 + 11 * b + 13 * 0))) :
    Φ 0 6 b 0 < Φ 0 (w4 (1 + 9 * 6 + 11 * b + 13 * 0)) (w5 (1 + 9 * 6 + 11 * b + 13 * 0)) (w6 (1 + 9 * 6 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 6 + 11 * b + 13 * 0) = 5 := by unfold sres; omega
  have hw := w_four _ 5 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 6 + 11 * b + 13 * 0) = 6 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 6 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 6 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_5_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 5 + 11 * b + 13 * 0))
    (hne : ¬ (5 = w4 (1 + 9 * 5 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 5 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 5 + 11 * b + 13 * 0))) :
    Φ 0 5 b 0 < Φ 0 (w4 (1 + 9 * 5 + 11 * b + 13 * 0)) (w5 (1 + 9 * 5 + 11 * b + 13 * 0)) (w6 (1 + 9 * 5 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 5 + 11 * b + 13 * 0) = 6 := by unfold sres; omega
  have hw := w_four _ 6 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 5 + 11 * b + 13 * 0) = 5 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 5 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 5 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_4_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 4 + 11 * b + 13 * 0))
    (hne : ¬ (4 = w4 (1 + 9 * 4 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 4 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 4 + 11 * b + 13 * 0))) :
    Φ 0 4 b 0 < Φ 0 (w4 (1 + 9 * 4 + 11 * b + 13 * 0)) (w5 (1 + 9 * 4 + 11 * b + 13 * 0)) (w6 (1 + 9 * 4 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 4 + 11 * b + 13 * 0) = 7 := by unfold sres; omega
  have hw := w_four _ 7 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 4 + 11 * b + 13 * 0) = 4 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 4 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 4 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_3_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 3 + 11 * b + 13 * 0))
    (hne : ¬ (3 = w4 (1 + 9 * 3 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 3 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 3 + 11 * b + 13 * 0))) :
    Φ 0 3 b 0 < Φ 0 (w4 (1 + 9 * 3 + 11 * b + 13 * 0)) (w5 (1 + 9 * 3 + 11 * b + 13 * 0)) (w6 (1 + 9 * 3 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 3 + 11 * b + 13 * 0) = 8 := by unfold sres; omega
  have hw := w_four _ 8 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 3 + 11 * b + 13 * 0) = 3 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 3 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 3 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_2_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 2 + 11 * b + 13 * 0))
    (hne : ¬ (2 = w4 (1 + 9 * 2 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 2 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 2 + 11 * b + 13 * 0))) :
    Φ 0 2 b 0 < Φ 0 (w4 (1 + 9 * 2 + 11 * b + 13 * 0)) (w5 (1 + 9 * 2 + 11 * b + 13 * 0)) (w6 (1 + 9 * 2 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 2 + 11 * b + 13 * 0) = 9 := by unfold sres; omega
  have hw := w_four _ 9 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 2 + 11 * b + 13 * 0) = 2 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 2 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 2 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne

theorem scombo_1_0 (b : ℕ) (hn : 492 ≤ (1 + 9 * 1 + 11 * b + 13 * 0))
    (hne : ¬ (1 = w4 (1 + 9 * 1 + 11 * b + 13 * 0) ∧ b = w5 (1 + 9 * 1 + 11 * b + 13 * 0) ∧ 0 = w6 (1 + 9 * 1 + 11 * b + 13 * 0))) :
    Φ 0 1 b 0 < Φ 0 (w4 (1 + 9 * 1 + 11 * b + 13 * 0)) (w5 (1 + 9 * 1 + 11 * b + 13 * 0)) (w6 (1 + 9 * 1 + 11 * b + 13 * 0)) := by
  have hs : sres (1 + 9 * 1 + 11 * b + 13 * 0) = 10 := by unfold sres; omega
  have hw := w_four _ 10 hs (by omega) (by omega)
  have h4 : w4 (1 + 9 * 1 + 11 * b + 13 * 0) = 1 := by have := hw.1; omega
  have h6 : w6 (1 + 9 * 1 + 11 * b + 13 * 0) = 0 := by have := hw.2; omega
  have h5 : w5 (1 + 9 * 1 + 11 * b + 13 * 0) = b := by unfold w5; rw [h4, h6]; omega
  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne


/-- Dispatch over the cherry-free candidate counts. -/
theorem counts_strict (a b d : ℕ) (ha : a ≤ 10) (hd : d ≤ 10) (had : a = 0 ∨ d = 0)
    (hn : 492 ≤ 1 + 9 * a + 11 * b + 13 * d)
    (hne : ¬ (a = w4 (1 + 9 * a + 11 * b + 13 * d) ∧ b = w5 (1 + 9 * a + 11 * b + 13 * d) ∧
      d = w6 (1 + 9 * a + 11 * b + 13 * d))) :
    Φ 0 a b d < Φ 0 (w4 (1 + 9 * a + 11 * b + 13 * d)) (w5 (1 + 9 * a + 11 * b + 13 * d))
      (w6 (1 + 9 * a + 11 * b + 13 * d)) := by
  rcases had with rfl | rfl
  · interval_cases d
    · exact scombo_0_0 b hn hne
    · exact scombo_0_1 b hn hne
    · exact scombo_0_2 b hn hne
    · exact scombo_0_3 b hn hne
    · exact scombo_0_4 b hn hne
    · exact scombo_0_5 b hn hne
    · exact scombo_0_6 b hn hne
    · exact scombo_0_7 b hn hne
    · exact scombo_0_8 b hn hne
    · exact scombo_0_9 b hn hne
    · exact scombo_0_10 b hn hne
  · interval_cases a
    · exact scombo_0_0 b hn hne
    · exact scombo_1_0 b hn hne
    · exact scombo_2_0 b hn hne
    · exact scombo_3_0 b hn hne
    · exact scombo_4_0 b hn hne
    · exact scombo_5_0 b hn hne
    · exact scombo_6_0 b hn hne
    · exact scombo_7_0 b hn hne
    · exact scombo_8_0 b hn hne
    · exact scombo_9_0 b hn hne
    · exact scombo_10_0 b hn hne

theorem adm_W (n : ℕ) : Adm (W n) := by
  intro x hx
  simp only [W, List.mem_append, List.mem_replicate] at hx
  rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> simp

theorem perm_of_counts {l l' : List Child} (h : Adm l) (h' : Adm l')
    (hc : cC l = cC l') (h4 : c4 l = c4 l') (h5 : c5 l = c5 l') (h6 : c6 l = c6 l') : l.Perm l' := by
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x = Child.cherry ∨ x = Child.arm 4 ∨ x = Child.arm 5 ∨ x = Child.arm 6
  · rcases hx with rfl | rfl | rfl | rfl
    · exact hc
    · exact h4
    · exact h5
    · exact h6
  · rw [List.count_eq_zero_of_not_mem (fun hm => hx (h x hm)),
      List.count_eq_zero_of_not_mem (fun hm => hx (h' x hm))]

/-- A cherry-free candidate that is not a rearrangement of the rule winner is strictly worse. -/
theorem nocherry_strict (l : List Child) (hC : Cand l) (h0 : l.count Child.cherry = 0) (hn : 492 ≤ nv l)
    (hne : ¬ l.Perm (W (nv l))) : F l < F (W (nv l)) := by
  obtain ⟨-, hadm, h46, h4, h6⟩ := hC
  have hc0 : cC l = 0 := h0
  have hN : nv l = 1 + 9 * c4 l + 11 * c5 l + 13 * c6 l := by
    have := nv_eq l hadm; rw [hc0] at this; omega
  rw [F_eq_Φ l hadm, F_W_eq, hc0]
  rw [hN] at hn hne ⊢
  have had : c4 l = 0 ∨ c6 l = 0 := by
    by_contra hcon
    push Not at hcon
    exact h46 ⟨List.count_pos_iff.mp (Nat.pos_of_ne_zero hcon.1),
      List.count_pos_iff.mp (Nat.pos_of_ne_zero hcon.2)⟩
  apply counts_strict _ _ _ h4 h6 had hn
  rintro ⟨e4, e5, e6⟩
  apply hne
  have hW : cC (W (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l)) = 0 ∧
      c4 (W (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l)) = w4 (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l) ∧
      c5 (W (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l)) = w5 (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l) ∧
      c6 (W (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l)) = w6 (1 + 9 * c4 l + 11 * c5 l + 13 * c6 l) := by
    simp [cC, c4, c5, c6, W, List.count_append, List.count_replicate]
  exact perm_of_counts hadm (adm_W _) (by rw [hc0, hW.1]) (by rw [hW.2.1]; exact e4)
    (by rw [hW.2.2.1]; exact e5) (by rw [hW.2.2.2]; exact e6)

/-- The rule winner is optimal in the spider family (from the existing certificate chain). -/
theorem W_opt (l : List Child) (hn : 492 ≤ nv l) : F l ≤ F (W (nv l)) :=
  spider_opt_of structProp_492 candProp_492 l hn

/-- Uniqueness in the spider family, n ≥ 492: a spider whose value reaches the rule winner's is a
    rearrangement of it. -/
theorem spider_unique_large (l : List Child) (hn : 492 ≤ nv l) (heq : F (W (nv l)) ≤ F l) :
    l.Perm (W (nv l)) := by
  have hmax : IsMax l := by
    intro l' hl'
    have h1 := W_opt l' (by rw [hl']; exact hn)
    rw [hl'] at h1
    exact le_trans h1 heq
  by_contra hne
  exact absurd heq (not_le.mpr (nocherry_strict l (cand_of_isMax hmax hn) (no_cherry hmax hn) hn hne))

/-- Strict optimality in the spider family, n ≥ 492. -/
theorem spider_strict_large (l : List Child) (hn : 492 ≤ nv l) (hne : ¬ l.Perm (W (nv l))) :
    F l < F (W (nv l)) :=
  lt_of_le_of_ne (W_opt l hn) (fun h => hne (spider_unique_large l hn h.ge))

end SpiderStrict
end R3Cert
