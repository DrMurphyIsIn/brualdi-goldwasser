/-
LeanCherry.PBEqMain -- the equality clause of part (B) on all of 0 < lam < 1 + sqrt 5:
  log T(b) = |b| f*(lam)  iff  b is a best arm A_j (f_j = f*).
  eq_config      : a Bellman equality only at the cherry type (1, 0) or at (0, m, y_ch) with m >= 3;
  eq_clause_of   : step (b) of the hand proof, for a leaf-exempt witness with these equality configurations
                   and a strict corner at y_ch;
  part_B_equality, part_B_full_eq : the headline.
-/
import LeanCherry.PBEqS6
import LeanCherry.PBMain

open Real

namespace LeanCherry

noncomputable section

open Classical Br

namespace PB

variable {l : ℝ} (H : PB l)
include H

/-- the equality configurations of a leaf-exempt witness of the common shape -/
lemma eq_config {sm : ℝ} {h : ℝ → ℝ} (Sh : PShape l sm h)
    (hsm : sm ≤ l * yA l 4 * (1 - kapP l * yA l 4)) (h2 : h (yA l 2) < gArm l 2)
    (hflat : ∀ m : ℕ, 5 ≤ m → ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → y ≠ yC l → B0lt l h m y)
    (k m : ℕ) (y : ℝ) (hkm : 1 ≤ k + m) (hy : 0 < m → 0 ≤ y ∧ y ≤ 1 / 2)
    (heq : h (1 / ((k:ℝ) + m + 1 + l * (k + m * y))) =
      fstar l + k * fstar l + m * h y - Real.log (1 + l * (k + m * y) / (k + m + 1))) :
    (k = 1 ∧ m = 0) ∨ (k = 0 ∧ 3 ≤ m ∧ y = yC l) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0
    subst hk0
    have hm1 : 1 ≤ m := by omega
    obtain ⟨hy0, hy1⟩ := hy (by omega)
    simp only [Nat.cast_zero, zero_add, zero_mul, add_zero] at heq
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m) with e | e | e | e | e
    · exfalso; subst e
      have := H.step_m1_lt Sh (PBC.cert_C4 l)
        (PBC.cert_C5 l H.pos.le (by have := H.hi; norm_num at this ⊢; linarith))
        (PBC.cert_C6 (tC l) H.t_pos.le H.t_le') y hy0 hy1
      unfold B0lt at this
      push_cast at this heq
      linarith
    · exfalso; subst e
      by_cases hyc : y = yC l
      · subst hyc
        have := H.arm_at_yc Sh 2
        push_cast at this heq
        linarith
      · have := H.step_arm_lt Sh hsm 2 le_rfl (by norm_num) y hy0 hy1 hyc
        push_cast at this heq
        linarith
    · subst e
      by_cases hyc : y = yC l
      · exact Or.inr ⟨rfl, le_rfl, hyc⟩
      · exfalso
        have := H.step_arm_lt Sh hsm 3 (by norm_num) (by norm_num) y hy0 hy1 hyc
        have hz : h (yA l 3) = 0 := Sh.zero _ H.S2
        have hg := H.gArm_nonneg 3 (by norm_num)
        push_cast at this heq hg hz
        linarith
    · subst e
      by_cases hyc : y = yC l
      · exact Or.inr ⟨rfl, by norm_num, hyc⟩
      · exfalso
        have := H.step_arm_lt Sh hsm 4 (by norm_num) le_rfl y hy0 hy1 hyc
        have hy43 : yA l 4 ≤ yA l 3 := by
          unfold yA; apply one_div_le_one_div_of_le (by have := H.t_pos; positivity); have := H.t_pos; linarith
        have hz : h (yA l 4) = 0 := Sh.zero _ (le_trans hy43 H.S2)
        have hg := H.gArm_nonneg 4 (by norm_num)
        push_cast at this heq hg hz
        linarith
    · by_cases hyc : y = yC l
      · exact Or.inr ⟨rfl, by omega, hyc⟩
      · exfalso
        have := hflat m e y hy0 hy1 hyc
        unfold B0lt at this
        linarith
  · -- k >= 1
    by_cases hnot : k = 1 ∧ m = 0
    · exact Or.inl hnot
    · exfalso
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have := H.step_kpos_lt Sh k 0 0 hkpos hnot le_rfl (by norm_num)
        push_cast at this heq
        simp only [zero_mul, mul_zero, add_zero, zero_add] at this heq
        linarith
      · obtain ⟨hy0, hy1⟩ := hy hmpos
        have := H.step_kpos_lt Sh k m y hkpos hnot hy0 hy1
        linarith

/-- an arm message y(A_m), m >= 3, is strictly below y_ch -/
lemma msg_ne_yc (m : ℕ) (hm : 3 ≤ m) : 1 / ((m:ℝ) + 1 + l * (m * yC l)) ≠ yC l := by
  have ht := H.t_pos; have ht1 := H.t_lt_one
  have hlt := H.l_yc
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have e : (m:ℝ) + 1 + l * (m * yC l) = m + 1 + m * tC l := by rw [← hlt]; ring
  rw [e]
  intro heq
  have hyc : yC l = 1 / (2 + l) := rfl
  have h1 : (1:ℝ) - tC l = 2 / (2 + l) := H.one_sub_t
  have hl := H.pos
  rw [hyc] at heq
  have hp1 : (0:ℝ) < m + 1 + m * tC l := by positivity
  have hp2 : (0:ℝ) < 2 + l := by positivity
  rw [div_eq_div_iff hp1.ne' hp2.ne'] at heq
  have hD : m + 1 + m * tC l = 2 + l := by linarith
  -- (m + 1 + m t)(1 - t) = 2, impossible for m >= 3, 0 < t < 1
  have h2 : (m + 1 + m * tC l) * (1 - tC l) = 2 := by
    rw [hD, h1]; field_simp
  have : (4 + 3 * tC l) * (1 - tC l) ≤ (m + 1 + m * tC l) * (1 - tC l) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith); nlinarith
  have ht6 := H.t_le
  have hpos : 0 < (2 - 3 * tC l) * (1 + tC l) := mul_pos (by norm_num at ht6; linarith) (by linarith)
  have e1 : (4 + 3 * tC l) * (1 - tC l) = 2 + (2 - 3 * tC l) * (1 + tC l) := by ring
  linarith

end PB

namespace Br

/-- the message of a node from its type -/
lemma msgl_type (l : ℝ) (A : Set Br) (cs : List Br) :
    msgl l (.node cs) = 1 / (((exE A cs).card : ℝ) + (nonE A cs).length + 1 +
      l * (((exE A cs).map (msgl l)).sum +
        (nonE A cs).length * (((nonE A cs).map (msgl l)).sum / (nonE A cs).length))) := by
  set N := nonE A cs
  set m := N.length
  set pA : Br → Bool := fun c => decide (c ∈ A)
  have hN : N = cs.filter (fun c => !pA c) := by simp only [N, nonE, pA]; congr 1; funext c; simp
  have hE : exE A cs = ↑(cs.filter pA) := rfl
  have hlen : (cs.length : ℝ) = ((cs.filter pA).length : ℝ) + m := by rw [length_split pA cs, ← hN]; push_cast; ring
  have hmy : (m : ℝ) * ((N.map (msgl l)).sum / m) = (N.map (msgl l)).sum := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have : N = [] := List.length_eq_zero_iff.mp hm0
      simp [this, hm0]
    · field_simp
  have hcardR : ((exE A cs).card : ℝ) + m + 1 = (cs.length : ℝ) + 1 := by rw [hE, Multiset.coe_card, hlen]
  have hR : ((exE A cs).map (msgl l)).sum + m * ((N.map (msgl l)).sum / m) = sumYl l cs := by
    rw [hmy, hE, Multiset.map_coe, Multiset.sum_coe, sumYl_map', sum_split pA (msgl l) cs, ← hN]
  rw [hcardR, hR, msgl_node]

/-- exempt count plus non-exempt count is the number of children -/
lemma card_add_length (A : Set Br) (cs : List Br) : (exE A cs).card + (nonE A cs).length = cs.length := by
  rw [show exE A cs = ↑(cs.filter (fun c => decide (c ∈ A))) from rfl, Multiset.coe_card]
  rw [length_split (fun c => decide (c ∈ A)) cs]; congr 1; simp only [nonE]; congr 2; funext c; simp

/-- no non-exempt child: every child is exempt -/
lemma mem_of_nonE_nil {A : Set Br} {cs : List Br} (h : nonE A cs = []) : ∀ c ∈ cs, c ∈ A := by
  intro c hc
  by_contra hcA
  have : c ∈ nonE A cs := List.mem_filter.mpr ⟨hc, by simpa using hcA⟩
  rw [h] at this; simp at this

/-- no exempt child: the non-exempt children are all the children -/
lemma nonE_eq_of_card_zero {A : Set Br} {cs : List Br} (h : (exE A cs).card = 0) : nonE A cs = cs := by
  have h1 := card_add_length A cs
  rw [h, zero_add] at h1
  exact List.filter_eq_self.mpr (by
    intro c hc
    by_contra hc'
    have hlt : (nonE A cs).length < cs.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨c, hc, hc'⟩
    omega)

end Br

open Br

/-- step (b) of the equality clause, for a leaf-exempt witness on [0, 1/2] whose Bellman inequality is an equality
    only at the cherry type or at (0, m, y_ch) with m >= 3, with a strict corner at y_ch -/
theorem eq_clause_of {l : ℝ} {h : ℝ → ℝ} (W : Witness l (fstar l) {Br.node []} (Set.Icc 0 (1 / 2)) h)
    (hF : 0 < fstar l) (hch : 0 < gB l (fstar l) cherry)
    (hEQ : ∀ (k m : ℕ) (y : ℝ), 1 ≤ k + m → (0 < m → 0 ≤ y ∧ y ≤ 1 / 2) →
      h (1 / ((k:ℝ) + m + 1 + l * (k + m * y))) =
        fstar l + k * fstar l + m * h y - Real.log (1 + l * (k + m * y) / (k + m + 1)) →
      (k = 1 ∧ m = 0) ∨ (k = 0 ∧ 3 ≤ m ∧ y = yC l))
    (hsupp : ∃ s : ℝ, ∀ y : ℝ, y ≠ yC l → h (yC l) + s * (y - yC l) < h y)
    (hym : ∀ m : ℕ, 3 ≤ m → 1 / ((m:ℝ) + 1 + l * (m * yC l)) ≠ yC l)
    (b : Br) (hb : gB l (fstar l) b = 0) : ∃ j : ℕ, 1 ≤ j ∧ b = armB j := by
  set A : Set Br := {Br.node []} with hAdef
  have hl := W.lam_pos.le
  -- the type of a tight non-leaf node, in (k, m, ybar) form
  have typed : ∀ cs : List Br, cs ≠ [] → Br.node cs ∉ A → Witness.TightB l (fstar l) A h (.node cs) →
      (∀ c ∈ nonE A cs, Witness.TightB l (fstar l) A h c) ∧
      (((nonE A cs).map (msgl l)).map h).sum =
        (nonE A cs).length * h ((((nonE A cs).map (msgl l)).sum) / (nonE A cs).length) ∧
      ((exE A cs).card = 1 ∧ (nonE A cs).length = 0 ∨
        (exE A cs).card = 0 ∧ 3 ≤ (nonE A cs).length ∧
          (((nonE A cs).map (msgl l)).sum) / (nonE A cs).length = yC l) := by
    intro cs hne hbA hT
    obtain ⟨hch', hjen, hbel⟩ := (W.tight_node cs hne hbA).mp hT
    refine ⟨hch', hjen, ?_⟩
    set N := nonE A cs with hN
    set m := N.length with hm
    set ybar := (N.map (msgl l)).sum / m with hyb
    set E := exE A cs with hEdef
    have hEA : ∀ a ∈ E, a ∈ A := by
      intro a ha; rw [hEdef, show exE A cs = ↑(cs.filter (fun c => decide (c ∈ A))) from rfl,
        Multiset.mem_coe] at ha
      simpa using (List.mem_filter.mp ha).2
    have hErep : E = Multiset.replicate E.card (Br.node []) :=
      Multiset.eq_replicate.mpr ⟨rfl, fun a ha => by simpa [hAdef] using hEA a ha⟩
    set k := E.card with hk
    have hkm : 1 ≤ k + m := by
      have := card_add_length A cs
      rw [← hEdef, ← hN] at this
      have : 0 < cs.length := List.length_pos_iff.mpr hne
      omega
    have hNI : ∀ c ∈ N, msgl l c ∈ Set.Icc (0:ℝ) (1 / 2) := fun c hc =>
      W.msg_mem (by simpa using (List.mem_filter.mp hc).2)
    have hy : 0 < m → 0 ≤ ybar ∧ ybar ≤ 1 / 2 := by
      intro hmpos
      have hne' : N.map (msgl l) ≠ [] := by
        simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos hmpos
      have hlen' : ((N.map (msgl l)).length : ℝ) = m := by simp [m]
      have := (jensen_list W.convex (N.map (msgl l)) hne' (by
        intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hNI c hc)).1
      rw [hlen'] at this
      exact this
    rw [hErep] at hbel
    simp only [Multiset.map_replicate, Multiset.sum_replicate, Multiset.card_replicate, msgl_node, gB_leaf]
      at hbel
    simp only [List.length_nil, Nat.cast_zero, zero_add, sumYl, mul_zero, add_zero, div_one, nsmul_eq_mul,
      mul_one] at hbel
    have := hEQ k m ybar hkm hy (by rw [← hbel])
    exact this
  -- b is not the leaf, so it is non-exempt and tight
  have hbA : b ∉ A := by
    intro hbA'; rw [hAdef, Set.mem_singleton_iff] at hbA'; rw [hbA', gB_leaf] at hb; linarith
  obtain ⟨hTb, -⟩ := W.tight_of_g_zero hbA hb
  obtain ⟨cs⟩ := b
  have hne : cs ≠ [] := by intro h0; apply hbA; rw [h0]; rfl
  obtain ⟨hchild, hjen, hcase⟩ := typed cs hne hbA hTb
  rcases hcase with ⟨hk1, hm0⟩ | ⟨hk0, hm3, hyc⟩
  · -- the cherry type: b = cherry, but g(cherry) > 0
    exfalso
    have hall := mem_of_nonE_nil (List.length_eq_zero_iff.mp hm0)
    have hlen := card_add_length A cs
    rw [hk1, hm0] at hlen
    obtain ⟨c, hc⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen.symm
    have hcl : c = Br.node [] := by
      have := hall c (by rw [hc]; simp); rwa [hAdef, Set.mem_singleton_iff] at this
    rw [hc, hcl] at hb
    have : Br.node [Br.node []] = cherry := rfl
    rw [this] at hb; linarith
  · -- type (0, m, y_ch): every child has message y_ch (strict corner), so every child is a cherry
    have hNcs := nonE_eq_of_card_zero hk0
    obtain ⟨s, hs⟩ := hsupp
    have hmpos : 0 < (nonE A cs).length := by omega
    have hmsg := W.jensen_eq_forces cs (s := s) (by
        intro y _ hy; rw [hyc] at hy ⊢; exact hs y hy) hmpos hjen
    have hcher : ∀ c ∈ cs, c = cherry := by
      intro c hc
      have hcN : c ∈ nonE A cs := by rw [hNcs]; exact hc
      have hcm : msgl l c = yC l := by rw [hmsg c hcN, hyc]
      have hcA : c ∉ A := by simpa using (List.mem_filter.mp hcN).2
      have hTc := hchild c hcN
      obtain ⟨cs'⟩ := c
      have hne' : cs' ≠ [] := by intro h0; apply hcA; rw [h0]; rfl
      obtain ⟨-, -, hcase'⟩ := typed cs' hne' hcA hTc
      rcases hcase' with ⟨hk1', hm0'⟩ | ⟨hk0', hm3', hyc'⟩
      · have hall := mem_of_nonE_nil (List.length_eq_zero_iff.mp hm0')
        have hlen := card_add_length A cs'
        rw [hk1', hm0'] at hlen
        obtain ⟨d, hd⟩ : ∃ d, cs' = [d] := List.length_eq_one_iff.mp hlen.symm
        have hdl : d = Br.node [] := by
          have := hall d (by rw [hd]; simp); rwa [hAdef, Set.mem_singleton_iff] at this
        rw [hd, hdl]; rfl
      · exfalso
        have hmt := msgl_type l A cs'
        rw [hcm, hk0'] at hmt
        have hE0 : exE A cs' = 0 := Multiset.card_eq_zero.mp hk0'
        rw [hE0, hyc'] at hmt
        simp only [Multiset.map_zero, Multiset.sum_zero, zero_add, Nat.cast_zero] at hmt
        exact hym _ hm3' hmt.symm
    refine ⟨cs.length, ?_, ?_⟩
    · have := card_add_length A cs; omega
    · unfold armB
      congr 1
      exact List.eq_replicate_iff.mpr ⟨rfl, hcher⟩

/-- g(cherry) = eps > 0 on the range -/
lemma gB_cherry_pos {l : ℝ} (H : PB l) : 0 < gB l (fstar l) cherry := by
  unfold gB
  rw [Tl_cherry, log_c_eq H.pos.le]
  have hs : size cherry = 2 := rfl
  rw [hs]; push_cast
  have := H.eps_pos; unfold epsW at this
  linarith

/-- **the equality clause of part (B)**, every 0 < lam < 1 + sqrt 5: a planted branch attains the ceiling exactly
    when it is a best arm -/
theorem part_B_equality {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) (b : Br) :
    Real.log (Tl l b) = size b * fstar l ↔ ∃ j : ℕ, 1 ≤ j ∧ b = armB j ∧ fArm l j = fstar l := by
  have H : PB l := ⟨hl0, hlc⟩
  constructor
  · intro heq
    have hb : gB l (fstar l) b = 0 := by unfold gB; rw [heq]; ring
    have hch := gB_cherry_pos H
    have hF := H.fstar_pos
    have hym := H.msg_ne_yc
    obtain ⟨j, hj, rfl⟩ : ∃ j : ℕ, 1 ≤ j ∧ b = armB j := by
      rcases le_or_gt (3 / 20 : ℝ) l with h3 | h3
      · have Sh := H.hS_shape
        refine eq_clause_of (H.wstar_witness h3) hF hch ?_ (H.supp_strict Sh (H.sm_lt_kap H.S3)) hym b hb
        exact H.eq_config Sh H.S3 (H.S6_lt h3)
          (fun m hm y hy0 hy1 hyc => H.step_flat_lt Sh (fun y => le_max_of_le_left (le_max_right _ _)) H.S4
            m hm y hy0 hy1 hyc)
      · have W : W2Facts l := ⟨H, h3.le, fstar_eq_f3 l hl0 h3.le⟩
        have Sh := W.shape
        refine eq_clause_of W.witness hF hch ?_ (H.supp_strict Sh (H.sm_lt_kap W.sb_le)) hym b hb
        exact H.eq_config Sh W.sb_le W.hg2_lt
          (fun m hm y hy0 hy1 hyc => H.step_flat2_lt Sh (saW l) (h2v l) (sbW l)
            (fun y => le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
            (fun y => le_max_of_le_left (le_max_right _ _))
            W.ydag_lt_y2 W.y2_lt_yc W.sa_mul W.sb_mul W.T5' W.Nd W.N2 (fun m hm _ => W.NC m hm) m hm y hy0 hy1 hyc)
    refine ⟨j, hj, rfl, ?_⟩
    unfold gB at hb
    rw [armB_size] at hb
    unfold fArm
    have hp : (0:ℝ) < 2 * j + 1 := by positivity
    push_cast at hb
    field_simp
    linarith
  · rintro ⟨j, -, rfl, hj⟩
    have := gB_arm_eq_zero hj
    unfold gB at this
    linarith

/-- **part (B) with its equality clause**, every 0 < lam < 1 + sqrt 5 -/
theorem part_B_full_eq {l : ℝ} (hl0 : 0 < l) (hlc : l < 1 + √5) :
    (∀ b : Br, Real.log (Tl l b) ≤ size b * fstar l) ∧
    (∀ b : Br, Real.log (Tl l b) = size b * fstar l ↔ ∃ j : ℕ, 1 ≤ j ∧ b = armB j ∧ fArm l j = fstar l) ∧
    rhoB l = Real.exp (fstar l) ∧
      ∃ j : ℕ, 1 ≤ j ∧ fArm l j = fstar l ∧ ∀ n : ℕ, 1 ≤ n →
        Real.exp (fstar l * size (armB j) * (((n - 1) / size (armB j) : ℕ) : ℝ)) ≤ Mn l n ∧
          Mn l n ≤ (1 + l) * Real.exp (fstar l * ((n : ℝ) - 1)) := by
  obtain ⟨h1, h2, -⟩ := part_B_full hl0 hlc
  obtain ⟨-, j, hj, hfj⟩ := partB_witness_all l hl0 hlc
  have hc : ∀ b : Br, Tl l b ≤ Real.exp (fstar l * size b) := fun b => by
    rw [← Real.exp_log (Tl_pos hl0.le b)]
    exact Real.exp_le_exp.mpr (by linarith [h1 b])
  obtain ⟨-, hMn⟩ := tight_consequences hl0.le hc (gB_arm_eq_zero hfj)
  exact ⟨h1, part_B_equality hl0 hlc, h2, j, hj, hfj, hMn⟩

end

end LeanCherry
