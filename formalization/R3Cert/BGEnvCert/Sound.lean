/-
  R3Cert.BGEnvCert.Sound -- soundness of one cap certificate (2026-09-25).

  `capSound`: if `capCheck tt ld ph d = true` and the shared tables pass `tanOK`/`ldOK`, then for
  every root entry `(n, k, g, Troot, m)` of `d` and every child list `cs` with `k` children, total
  size `n - 1`, all vertices with `≤ d.C` children and at least one non-atom child,
      `log π(cs) - (n-1) fq < Φ(n) / 2^P`.
  The proof decodes the packed tables into the real tables of `Envelope.EnvHyp` / `RootHyp`.
  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Check

namespace R3Cert
namespace EnvCert

open R3Cert.BGSCL

theorem PB_pos : (0 : ℝ) < 2 ^ PB := by positivity

/-- Offsets add: `(a - (c-1)·OFF) + (b - OFF) ≤ L - c·OFF` from `a + b ≤ L`. -/
theorem real_step {a b L c : ℕ} (hc : 1 ≤ c) (h : a + b ≤ L) :
    ((a : ℝ) - ((c - 1 : ℕ) : ℝ) * OFF) / 2 ^ PB + ((b : ℝ) - OFF) / 2 ^ PB
      ≤ ((L : ℝ) - (c : ℝ) * OFF) / 2 ^ PB := by
  have h' : (a : ℝ) + b ≤ L := by exact_mod_cast h
  rw [← add_div, div_le_div_iff_of_pos_right PB_pos, Nat.cast_sub hc]
  push_cast; nlinarith

theorem capSound (tt : TanTab) (ld : LdTab) (ph : PhiTab) (D : ℕ) (d : CapData)
    (hT : tanOK tt 0 HG = true) (hL : ldOK ld D = true) (hD : d.C + 1 ≤ D)
    (hc : capCheck tt ld ph d = true) :
    ∀ e ∈ d.roots, ∀ cs : List Branch, cs.length = e.2.1 → bsizeList cs = e.1 - 1 →
      (∀ x ∈ cs, maxCh x ≤ d.C) → (∃ x ∈ cs, ¬ IsAtom x) →
      phiF (fq : ℝ) cs < (phiOf ph e.1 : ℝ) / 2 ^ PB := by
  unfold capCheck at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hR, hC1⟩, hkC⟩, hC120⟩, hdWa⟩, hdWn⟩, hleaf⟩, htroot⟩, hkmax⟩, hloop⟩ := hc
  have hOFF : 1 ≤ OFF := Nat.one_le_two_pow
  have hWa := dataOK_spec (by omega) (by rw [half_WL]; omega) hdWa
  have hWn := dataOK_spec (by omega) (by rw [half_WL]; omega) hdWn
  have h2O : 2 * OFF ≤ 2 ^ WL := by
    have := pow_half_le WL; rw [half_WL] at this; omega
  have hlev := capLoop_spec tt ld ph d _ 1 le_rfl hloop
  have hlevel : ∀ c, 1 ≤ c → c ≤ max d.C d.kmax → levelOK tt ld ph d c (lvl d (c - 1)) = true :=
    fun c h1 h2 => hlev c h1 (by omega)
  have hH : 0 < HG := by decide
  -- the real tables
  set Sm := d.R - 1 with hSm
  set wa : ℕ → ℕ → ℝ := fun s g => ((lane d.Wa (HG * s + g) : ℝ) - OFF) / 2 ^ PB with hwa
  set wn : ℕ → ℕ → ℝ := fun s g => ((lane d.Wn (HG * s + g) : ℝ) - OFF) / 2 ^ PB with hwn
  set kk : ℕ → ℕ → ℕ → ℝ := fun c N h => ((lane (lvl d (c - 1)).1 (HG * N + h) : ℝ) - (c : ℝ) * OFF) / 2 ^ PB
    with hkk
  set kx : ℕ → ℕ → ℕ → ℝ := fun c N h => ((lane (lvl d (c - 1)).2.1 (HG * N + h) : ℝ) - (c : ℝ) * OFF) / 2 ^ PB
    with hkx
  set rr : ℕ → ℕ → ℕ → ℝ := fun c N h => ((lane (lvl d (c - 1)).2.2 (HG * N + h) : ℝ) - (c : ℝ) * OFF) / 2 ^ PB
    with hrr
  set k1 : ℕ → ℕ → ℝ := fun N h => ((lane (keepGe3 WL HG d.Wa) (HG * N + h) : ℝ) - OFF) / 2 ^ PB with hk1
  have hidx : ∀ N h, N < d.R → h < HG → HG * N + h < HG * d.R := fun N h hN hh => by
    have : HG * N + HG ≤ HG * d.R := by nlinarith
    omega
  have hdrop := dropRow2_rep h2O hR hWa
  have hkeep := keepGe3_rep h2O hR hWa
  -- the Bellman lanes
  have hbell : ∀ c g, 1 ≤ c → c ≤ d.C → g < HG → ∀ (T Wt : ℕ) (Bt : ℕ) (lo : ℕ) (hs : List ℕ),
      Rep WL (HG * d.R) T Bt (lane T) → Bt + OFF ≤ 2 ^ (WL - 1) →
      Rep WL (HG * d.R) Wt (2 * OFF) (lane Wt) → 1 ≤ lo →
      hs.all (witOK1 tt ld c g) = true → bchk WL HG d.R OFF T Wt g lo (pairs tt ld c g hs) = true →
      ∀ s, lo ≤ s → s < d.R → ∃ h < HG, ∃ K : ℤ, cstOf tt ld c g h = some K ∧
        TanB (fq : ℝ) (muQ g : ℝ) (muQ h : ℝ) c ((K : ℝ) / 2 ^ PB) ∧
        (K : ℝ) / 2 ^ PB + ((lane T (HG * (s - 1) + h) : ℝ) - (c : ℝ) * OFF) / 2 ^ PB
          ≤ ((lane Wt (HG * s + g) : ℝ) - OFF) / 2 ^ PB := by
    intro c g hc1 hcC hg T Wt Bt lo hs hTr hBt hWt hlo hwit hb s hs1 hs2
    have hhs : ∀ p ∈ pairs tt ld c g hs, p.1 < HG ∧ 2 * OFF + p.2 ≤ 2 ^ (WL - 1) := by
      intro p hp
      unfold pairs at hp
      obtain ⟨h, hmem, rfl⟩ := List.mem_map.mp hp
      have hw := (List.all_eq_true.mp hwit) h hmem
      unfold witOK1 at hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨hh, hw⟩ := hw
      refine ⟨hh, ?_⟩
      rw [half_WL]
      split at hw
      · rename_i K hK
        simp only [hK, Option.getD_some]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        omega
      · simp at hw
    obtain ⟨p, hp, hle⟩ := bchk_spec WL HG d.R OFF WL_pos (by decide) hTr hWt (by omega) g lo hg hlo _ hhs hb
      s hs1 hs2
    unfold pairs at hp
    obtain ⟨h, hmem, rfl⟩ := List.mem_map.mp hp
    have hw := (List.all_eq_true.mp hwit) h hmem
    unfold witOK1 at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hh, hw⟩ := hw
    split at hw
    · rename_i K hK
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      refine ⟨h, hh, K, hK, tanB_entry tt ld D hT hL c g h hc1 (by omega) hg K hK, ?_⟩
      simp only [hK, Option.getD_some] at hle
      have hle' : ((lane T (HG * (s - 1) + h) : ℤ) + OFF ≤ lane Wt (HG * s + g) + ((c : ℤ) * OFF - K)) := by
        have := hle
        rw [show (((c : ℤ) * OFF - K).toNat : ℕ) = (((c : ℤ) * OFF - K).toNat : ℕ) from rfl] at this
        have hnn : 0 ≤ (c : ℤ) * OFF - K := by omega
        have := (Int.toNat_of_nonneg hnn)
        omega
      have hr : ((lane T (HG * (s - 1) + h) : ℝ) + OFF ≤ lane Wt (HG * s + g) + ((c : ℝ) * OFF - K)) := by
        exact_mod_cast hle'
      rw [← add_div, div_le_div_iff_of_pos_right PB_pos]; linarith
    · simp at hw
  -- the envelope hypotheses
  have hE : EnvHyp (fq : ℝ) (fun g => (muQ g : ℝ)) HG d.C Sm wa wn kk kx k1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- leaf
      intro g hg
      have := (List.all_eq_true.mp hleaf) g (List.mem_range.mpr hg)
      simp only [decide_eq_true_eq] at this
      have h' := (Rat.cast_le (K := ℝ)).mpr this
      push_cast at h'
      simp only [hwa, mul_one]
      rw [le_div_iff₀ PB_pos]; linarith
    · -- k1a
      intro N h _ _ _
      simp only [hkk, hwa, lvl, lv0, Nat.sub_self, Nat.cast_one, one_mul]; exact le_rfl
    · -- ka
      intro c N m h hc2 hcC hN hm1 hmN hh
      have hst := (lvl_step hR hWa hWn (c - 2) (by omega) m N h hm1 hmN (by omega) hh).1
      rw [show c - 2 + 1 = c - 1 by omega] at hst
      have := real_step (c := c) (by omega) hst
      simp only [hkk, hwa]
      rw [show c - 1 - 1 = c - 2 by omega]
      exact this
    · -- k1x
      intro N h _ hN hN2 hh
      simp only [hkx, hwa, lvl, lv0, Nat.sub_self, Nat.cast_one, one_mul]
      rw [lane_of_rep hdrop h2O (hidx N h (by omega) hh)]
      have : ¬ (HG * 2 ≤ HG * N + h ∧ HG * N + h < HG * 3) := by
        rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge N 2 with h3 | h3
        · have : HG * N + h < HG * 2 := by nlinarith
          omega
        · have : 3 ≤ N := by omega
          have : HG * 3 ≤ HG * N := Nat.mul_le_mul_left _ this
          omega
      simp only [this, if_false]; exact le_rfl
    · -- kxa
      intro c N m h hc2 hcC hN hm1 hmN hh
      have hst := (lvl_step hR hWa hWn (c - 2) (by omega) m N h hm1 hmN (by omega) hh).2.1
      rw [show c - 2 + 1 = c - 1 by omega] at hst
      have := real_step (c := c) (by omega) hst
      simp only [hkx, hwa]
      rw [show c - 1 - 1 = c - 2 by omega]
      exact this
    · -- kxb
      intro c N m h hc2 hcC hN hm1 hmN hm2 hh
      have hst := (lvl_step hR hWa hWn (c - 2) (by omega) m N h hm1 hmN (by omega) hh).2.2.1 hm2
      rw [show c - 2 + 1 = c - 1 by omega] at hst
      have := real_step (c := c) (by omega) hst
      simp only [hkk, hkx, hwa]
      rw [show c - 1 - 1 = c - 2 by omega]
      exact this
    · -- k1p
      intro N h hN3 hN hh
      simp only [hk1, hwa]
      rw [lane_of_rep hkeep h2O (hidx N h (by omega) hh)]
      have : ¬ (HG * N + h < HG * 3) := by
        have : HG * 3 ≤ HG * N := Nat.mul_le_mul_left _ hN3
        omega
      simp only [this, if_false]; exact le_rfl
    · -- ba
      intro s g c hs2 hsS hg hc1 hcC
      have hl := hlevel c hc1 (by omega)
      unfold levelOK at hl
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hl
      have hb := hl.1.resolve_left (by omega)
      unfold bellLevel at hb
      have hg' := (List.all_eq_true.mp hb) g (List.mem_range.mpr hg)
      simp only [Bool.and_eq_true] at hg'
      obtain ⟨⟨⟨hwa1, _⟩, hb1⟩, _⟩ := hg'
      obtain ⟨r1, -, -⟩ := lvl_rep hR hWa hWn (c - 1) (by omega)
      obtain ⟨h, hh, K, _, hTan, hle⟩ := hbell c g hc1 hcC hg _ _ _ 2 _ r1
        (by rw [show c - 1 + 1 = c by omega]; exact pow_WL_ge c (by omega)) hWa (by norm_num) hwa1 hb1 s hs2 (by omega)
      exact ⟨h, hh, _, hTan, by simpa only [hkk, hwa] using hle⟩
    · -- bn
      intro s g c hs3 hsS hg hc1 hcC
      have hl := hlevel c hc1 (by omega)
      unfold levelOK at hl
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hl
      have hb := hl.1.resolve_left (by omega)
      unfold bellLevel at hb
      have hg' := (List.all_eq_true.mp hb) g (List.mem_range.mpr hg)
      simp only [Bool.and_eq_true] at hg'
      obtain ⟨⟨⟨_, hwn1⟩, _⟩, hb2⟩ := hg'
      obtain ⟨_, r2, -⟩ := lvl_rep hR hWa hWn (c - 1) (by omega)
      by_cases hc : c = 1
      · subst hc
        simp only [if_true] at hb2
        obtain ⟨h, hh, K, _, hTan, hle⟩ := hbell 1 g le_rfl hcC hg _ _ _ 3 _ (RepL_of hkeep h2O)
          (by rw [half_WL]; omega) hWn (by norm_num) hwn1 hb2 s hs3 (by omega)
        refine ⟨h, hh, _, hTan, ?_⟩
        simp only [if_true, hk1, hwn]
        simpa using hle
      · simp only [hc, if_false] at hb2
        obtain ⟨h, hh, K, _, hTan, hle⟩ := hbell c g hc1 hcC hg _ _ _ 3 _ r2
          (by rw [show c - 1 + 1 = c by omega]; exact pow_WL_ge c (by omega)) hWn (by norm_num) hwn1 hb2 s hs3 (by omega)
        refine ⟨h, hh, _, hTan, ?_⟩
        simp only [hc, if_false, hkx, hwn]
        exact hle
  -- the root hypotheses
  have hRt : RootHyp HG Sm d.kmax wa wn kk rr := by
    refine ⟨?_, ?_, ?_⟩
    · intro N h _ _ _
      simp only [hrr, hwn, lvl, lv0, Nat.sub_self, Nat.cast_one, one_mul]; exact le_rfl
    · intro c N m h hc2 hck hN hm1 hmN hh
      have hst := (lvl_step hR hWa hWn (c - 2) (by omega) m N h hm1 hmN (by omega) hh).2.2.2.1
      rw [show c - 2 + 1 = c - 1 by omega] at hst
      have := real_step (c := c) (by omega) hst
      simp only [hrr, hwa]
      rw [show c - 1 - 1 = c - 2 by omega]
      exact this
    · intro c N m h hc2 hck hN hm3 hmN hh
      have hst := (lvl_step hR hWa hWn (c - 2) (by omega) m N h (by omega) hmN (by omega) hh).2.2.2.2
      rw [show c - 2 + 1 = c - 1 by omega] at hst
      have := real_step (c := c) (by omega) hst
      simp only [hkk, hrr, hwn]
      rw [show c - 1 - 1 = c - 2 by omega]
      exact this
  -- the root
  intro e he cs hlen hsz hcap hna
  obtain ⟨n, k, g, Tr, m⟩ := e
  simp only at hlen hsz ⊢
  have htr := (List.all_eq_true.mp htroot) _ he
  have hkk' := (List.all_eq_true.mp hkmax) _ he
  simp only [decide_eq_true_eq] at hkk'
  unfold trootOK at htr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htr
  obtain ⟨⟨hk1, hlog⟩, htle⟩ := htr
  try simp only at hk1 hlog htle
  have hl := hlevel k hk1 (by omega)
  unfold levelOK at hl
  simp only [Bool.and_eq_true] at hl
  have hro := (List.all_eq_true.mp hl.2) _ he
  unfold rootOK1 at hro
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hro
  obtain ⟨⟨hnR, hg⟩, hlt⟩ := hro
  have hne : cs ≠ [] := by rintro rfl; simp at hlen; omega
  have hμ : (0 : ℝ) < (muQ g : ℝ) := by unfold muQ; push_cast; positivity
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  set t : ℝ := 1 / ((k : ℝ) * (muQ g : ℝ)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htan := phiF_le_tangent (fq : ℝ) cs hne htpos
  have hprice : 1 / ((cs.length : ℝ) * t) = (muQ g : ℝ) := by
    rw [hlen, ht]; field_simp
  rw [hprice] at htan
  have hsum := knap_root hE hRt hkC cs (by rw [hlen]; exact hk1) (by rw [hlen]; exact hkk')
    (by rw [hsz]; omega) hcap hna g hg
  rw [hlen, hsz] at hsum
  -- the root constant
  have hUB := log_le_logUB _ _ hlog
  have hTr := (Rat.cast_le (K := ℝ)).mpr htle
  push_cast at hUB hTr
  have hlogt : Real.log t + 1 / t - 1 ≤ (Tr : ℝ) / 2 ^ PB := by
    rw [le_div_iff₀ PB_pos]
    have e1 : 1 / t = (k : ℝ) * (muQ g : ℝ) := by rw [ht]; field_simp
    rw [e1]
    have e2 : Real.log t = Real.log ((1 : ℝ) / ((k : ℝ) * (muQ g : ℝ))) := by rw [ht]
    rw [e2]
    have h3 := mul_le_mul_of_nonneg_right (show Real.log (1 / ((k : ℝ) * (muQ g : ℝ))) + (k : ℝ) * (muQ g : ℝ) - 1
      ≤ ((logUB (1 / ((k : ℚ) * muQ g)) m : ℚ) : ℝ) + (k : ℝ) * (muQ g : ℝ) - 1 by linarith) PB_pos.le
    linarith
  have hlt' : (lane (lvl d (k - 1)).2.2 (HG * (n - 1) + g) : ℝ) + Tr < phiOf ph n + (k : ℝ) * OFF := by
    exact_mod_cast hlt
  have hfin : (Tr : ℝ) / 2 ^ PB + rr k (n - 1) g < (phiOf ph n : ℝ) / 2 ^ PB := by
    simp only [hrr]
    rw [← add_div, div_lt_div_iff_of_pos_right PB_pos]; linarith
  linarith

end EnvCert
end R3Cert
