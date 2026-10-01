/-
LeanCherry.Witness -- the witness framework (the definition of a witness, the deficit telescope, and the main
witness theorem (a)-(d)), for planted branches Br with the cavity recursion Tl l.

  g b := |b| F - log T_b                                              (gB l F b)
  type of node cs w.r.t. A: (E, m) = (multiset of the children in A, number of children not in A)   (typeOf A)
  Witness l F A I h:
    lam > 0; I an interval with (0,1/2] ⊆ I ⊆ [0,1];
    (HA) membership in A depends only on the type; every b ∈ A has m = 0;
    (H0) g a >= 0 for a ∈ A;
    (H2) h convex and bounded below on I; if the leaf is not exempt, 1 ∈ I and h 1 <= F;
         Bellman: for every type (E, m) with |E| + m >= 1 whose branches are not exempt, and every ybar ∈ I (any ybar if m = 0),
           F + sum_{a∈E} g a + m h(ybar) - log(1 + lam R/d) >= h(1/(d + lam R)),  d = |E| + m + 1, R = sum_{a∈E} y_a + m ybar.
  Tight: some b* has g b* = 0.
Theorems mt_main_a, mt_main_b, mt_main_c, and for (d) tight_leaf, tight_node, jensen_eq_forces, tight_of_g_zero.
Faithfulness note: Br is an ORDERED rose tree; a "branch" in the mathematics is its class up to reordering (Br.Equiv).  The type uses a
Multiset of exempt children (reordering at the root does not change it); nothing below needs A to be Equiv-closed.
-/
import LeanCherry.Rho

open Finset Filter Topology

namespace LeanCherry

noncomputable section

open Classical

namespace Br

lemma lsum_sub {α : Type*} (f g : α → ℝ) : ∀ L : List α, (L.map (fun x => f x - g x)).sum = (L.map f).sum - (L.map g).sum
  | [] => by simp
  | x :: L => by simp only [List.map_cons, List.sum_cons]; rw [lsum_sub f g L]; ring

lemma lsum_mul_right {α : Type*} (f : α → ℝ) (c : ℝ) : ∀ L : List α, (L.map (fun x => f x * c)).sum = (L.map f).sum * c
  | [] => by simp
  | x :: L => by simp only [List.map_cons, List.sum_cons]; rw [lsum_mul_right f c L]; ring

lemma lsum_mul_left {α : Type*} (f : α → ℝ) (c : ℝ) : ∀ L : List α, (L.map (fun x => c * f x)).sum = c * (L.map f).sum
  | [] => by simp
  | x :: L => by simp only [List.map_cons, List.sum_cons]; rw [lsum_mul_left f c L]; ring

lemma lsum_const {α : Type*} (c : ℝ) : ∀ L : List α, (L.map (fun _ => c)).sum = (L.length : ℝ) * c
  | [] => by simp
  | x :: L => by simp only [List.map_cons, List.sum_cons, List.length_cons]; rw [lsum_const c L]; push_cast; ring

/-- the deficit g(b) = |b| F - log T_b -/
def gB (l F : ℝ) (b : Br) : ℝ := (size b : ℝ) * F - Real.log (Tl l b)

/-- exempt children (as a multiset) and non-exempt children of a root -/
def exE (A : Set Br) (cs : List Br) : Multiset Br := ↑(cs.filter (fun c => decide (c ∈ A)))
def nonE (A : Set Br) (cs : List Br) : List Br := cs.filter (fun c => decide (c ∉ A))

/-- the type (E, m) of a planted branch -/
def typeOf (A : Set Br) : Br → Multiset Br × ℕ
  | .node cs => (exE A cs, (nonE A cs).length)

/-- every branch of type (E, m) is non-exempt -/
def TypeNonExempt (A : Set Br) (E : Multiset Br) (m : ℕ) : Prop := ∀ b, typeOf A b = (E, m) → b ∉ A

/-- the Bellman inequality at (E, m, ybar) -/
def Bellman (l F : ℝ) (h : ℝ → ℝ) (E : Multiset Br) (m : ℕ) (ybar : ℝ) : Prop :=
  h (1 / ((E.card : ℝ) + m + 1 + l * ((E.map (msgl l)).sum + m * ybar))) ≤
    F + (E.map (gB l F)).sum + m * h ybar
      - Real.log (1 + l * ((E.map (msgl l)).sum + m * ybar) / ((E.card : ℝ) + m + 1))

end Br

open Br

/-- a witness -/
structure Witness (l F : ℝ) (A : Set Br) (I : Set ℝ) (h : ℝ → ℝ) : Prop where
  lam_pos : 0 < l
  I_ord : I.OrdConnected
  I_lo : Set.Ioc (0 : ℝ) (1 / 2) ⊆ I
  I_hi : I ⊆ Set.Icc 0 1
  HA_type : ∀ b b' : Br, typeOf A b = typeOf A b' → (b ∈ A ↔ b' ∈ A)
  HA_m : ∀ b ∈ A, (typeOf A b).2 = 0
  H0 : ∀ a ∈ A, 0 ≤ gB l F a
  convex : ConvexOn ℝ I h
  bdd : BddBelow (h '' I)
  leaf : Br.node [] ∉ A → (1 : ℝ) ∈ I ∧ h 1 ≤ F
  bell : ∀ (E : Multiset Br) (m : ℕ), (∀ a ∈ E, a ∈ A) → 1 ≤ E.card + m → TypeNonExempt A E m →
    ∀ ybar : ℝ, (0 < m → ybar ∈ I) → Bellman l F h E m ybar

/-- (H1) -/
def Tight (l F : ℝ) : Prop := ∃ b : Br, gB l F b = 0

namespace Br

/-! ### basic facts -/

lemma gB_leaf (l F : ℝ) : gB l F (.node []) = F := by
  simp [gB, Tl_leaf, size, sizeL]

lemma sum_split {β : Type*} [AddCommMonoid β] (p : Br → Bool) (f : Br → β) : ∀ cs : List Br,
    (cs.map f).sum = ((cs.filter p).map f).sum + ((cs.filter (fun c => !p c)).map f).sum
  | [] => by simp
  | c :: cs => by
      rw [List.map_cons, List.sum_cons, sum_split p f cs]
      cases hc : p c <;> simp [List.filter_cons, hc] <;> abel

lemma length_split (p : Br → Bool) : ∀ cs : List Br,
    cs.length = (cs.filter p).length + (cs.filter (fun c => !p c)).length
  | [] => by simp
  | c :: cs => by
      rw [List.length_cons, length_split p cs]
      cases hc : p c <;> simp [List.filter_cons, hc] <;> omega

lemma sumYl_map' (l : ℝ) (cs : List Br) : sumYl l cs = (cs.map (msgl l)).sum := sumYl_eq_map l cs

lemma log_prodTl {l : ℝ} (hl : 0 ≤ l) : ∀ cs : List Br, Real.log (prodTl l cs) = (cs.map (fun c => Real.log (Tl l c))).sum
  | [] => by simp [prodTl]
  | c :: cs => by
      simp only [prodTl, List.map_cons, List.sum_cons]
      rw [Real.log_mul (Tl_pos hl c).ne' (prodTl_pos hl cs).ne', log_prodTl hl cs]

lemma sizeL_map : ∀ cs : List Br, (sizeL cs : ℝ) = (cs.map (fun c => (size c : ℝ))).sum
  | [] => by simp [sizeL]
  | c :: cs => by simp only [sizeL, List.map_cons, List.sum_cons]; push_cast; rw [sizeL_map cs]

/-- the deficit recursion of the telescope -/
lemma gB_node {l : ℝ} (hl : 0 ≤ l) (F : ℝ) (cs : List Br) :
    gB l F (.node cs) = F + (cs.map (gB l F)).sum - Real.log (1 + l * sumYl l cs / ((cs.length : ℝ) + 1)) := by
  have hpos : 0 < 1 + l * sumYl l cs / ((cs.length : ℝ) + 1) := by
    have := div_nonneg (mul_nonneg hl (sumYl_nonneg hl cs)) (by positivity : (0:ℝ) ≤ (cs.length : ℝ) + 1)
    linarith
  unfold gB
  rw [Tl_node, Real.log_mul (prodTl_pos hl cs).ne' hpos.ne', log_prodTl hl]
  simp only [size]; push_cast
  rw [sizeL_map]
  have : (cs.map (fun b => (size b : ℝ) * F - Real.log (Tl l b))).sum
      = (cs.map (fun c => (size c : ℝ))).sum * F - (cs.map (fun c => Real.log (Tl l c))).sum := by
    rw [lsum_sub, lsum_mul_right]
  rw [this]
  ring

lemma msgl_nonleaf_mem {l : ℝ} (hl : 0 ≤ l) (cs : List Br) (hne : cs ≠ []) :
    msgl l (.node cs) ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
  have := msgl_pos hl (.node cs)
  refine ⟨this, ?_⟩
  rw [msgl_node]
  have h1 : (1:ℝ) ≤ cs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  rw [div_le_div_iff₀ (by have := mul_nonneg hl (sumYl_nonneg hl cs); positivity) (by norm_num)]
  nlinarith [mul_nonneg hl (sumYl_nonneg hl cs)]

/-- Jensen for the mean of a nonempty list -/
lemma jensen_list {I : Set ℝ} {h : ℝ → ℝ} (hc : ConvexOn ℝ I h) : ∀ xs : List ℝ, xs ≠ [] → (∀ x ∈ xs, x ∈ I) →
    xs.sum / xs.length ∈ I ∧ (xs.length : ℝ) * h (xs.sum / xs.length) ≤ (xs.map h).sum
  | [], hne, _ => absurd rfl hne
  | [x], _, hI => by simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, List.map_cons,
      List.map_nil]; norm_num; exact hI x (by simp)
  | x :: y :: ys, _, hI => by
      obtain ⟨hm, hj⟩ := jensen_list hc (y :: ys) (List.cons_ne_nil _ _) (fun z hz => hI z (List.mem_cons_of_mem _ hz))
      set n : ℝ := ((y :: ys).length : ℝ)
      set μ := (y :: ys).sum / n
      have hn : (0:ℝ) < n := by simp [n]; positivity
      have hx := hI x List.mem_cons_self
      have ha : (0:ℝ) ≤ 1 / (n + 1) := by positivity
      have hb : (0:ℝ) ≤ n / (n + 1) := by positivity
      have hab : 1 / (n + 1) + n / (n + 1) = 1 := by
        field_simp; ring
      have e1 : (x :: y :: ys).sum = x + (y :: ys).sum := List.sum_cons
      have e2 : (((x :: y :: ys).length : ℕ) : ℝ) = n + 1 := by
        simp only [n, List.length_cons]; push_cast; ring
      have hmean : (x :: y :: ys).sum / ((x :: y :: ys).length : ℝ) = 1 / (n + 1) * x + n / (n + 1) * μ := by
        rw [e1, e2]
        have hn' : n ≠ 0 := hn.ne'
        simp only [μ]
        field_simp
      rw [hmean]
      refine ⟨hc.1 hx hm ha hb hab, ?_⟩
      have h2 := hc.2 hx hm ha hb hab
      simp only [smul_eq_mul] at h2
      rw [e2, List.map_cons, List.sum_cons]
      have : (n + 1) * h (1 / (n + 1) * x + n / (n + 1) * μ) ≤ h x + n * h μ := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ n + 1)
        calc (n + 1) * h (1 / (n + 1) * x + n / (n + 1) * μ) ≤ (n + 1) * (1 / (n + 1) * h x + n / (n + 1) * h μ) := this
          _ = h x + n * h μ := by field_simp
      linarith

end Br

namespace Witness

variable {l F : ℝ} {A : Set Br} {I : Set ℝ} {h : ℝ → ℝ}

lemma typeNonExempt_of_not_mem (W : Witness l F A I h) {b : Br} (hb : b ∉ A) :
    TypeNonExempt A (typeOf A b).1 (typeOf A b).2 := by
  intro b' hb' hb'A
  exact hb ((W.HA_type b' b (by rw [hb'])).mp hb'A)

lemma msg_mem (W : Witness l F A I h) {b : Br} (hb : b ∉ A) : msgl l b ∈ I := by
  cases b with
  | node cs =>
    rcases eq_or_ne cs [] with rfl | hne
    · rw [msgl_leaf']; exact (W.leaf hb).1
    · exact W.I_lo (msgl_nonleaf_mem W.lam_pos.le cs hne)
where msgl_leaf' : msgl l (.node []) = 1 := by rw [msgl_node]; simp [sumYl]

/-- the witness theorem (a), first clause: h >= 0 on I -/
theorem h_nonneg (W : Witness l F A I h) : ∀ y ∈ I, 0 ≤ h y := by
  intro y0 hy0
  by_contra hneg
  push Not at hneg
  obtain ⟨B, hB⟩ := W.bdd
  have hl := W.lam_pos
  have hy01 := W.I_hi hy0
  obtain ⟨m, hm⟩ := exists_nat_gt ((F - B) / (-h y0))
  have hm1 : 1 ≤ m + 1 := by omega
  have hTNE : TypeNonExempt A 0 (m + 1) := by
    intro b hb hbA
    have := W.HA_m b hbA
    rw [hb] at this; simp at this
  have hbell := W.bell 0 (m + 1) (by simp) (by simp) hTNE y0 (fun _ => hy0)
  unfold Bellman at hbell
  simp only [Multiset.card_zero, Multiset.map_zero, Multiset.sum_zero, Nat.cast_zero, zero_add, add_zero] at hbell
  push_cast at hbell
  have harg : 1 / ((m : ℝ) + 1 + 1 + l * (((m : ℝ) + 1) * y0)) ∈ I := by
    apply W.I_lo
    have hpos : 0 ≤ l * (((m : ℝ) + 1) * y0) := mul_nonneg hl.le (mul_nonneg (by positivity) hy01.1)
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlow : B ≤ h (1 / ((m : ℝ) + 1 + 1 + l * (((m : ℝ) + 1) * y0))) := hB ⟨_, harg, rfl⟩
  have hlog : 0 ≤ Real.log (1 + l * (((m : ℝ) + 1) * y0) / ((m : ℝ) + 1 + 1)) := by
    apply Real.log_nonneg
    have := div_nonneg (mul_nonneg hl.le (mul_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ) + 1) hy01.1))
      (by positivity : (0:ℝ) ≤ (m:ℝ) + 1 + 1)
    linarith
  have hneg' : 0 < -h y0 := by linarith
  have : (F - B) < ((m : ℝ) + 1) * (-h y0) := by
    rw [div_lt_iff₀ hneg'] at hm; nlinarith
  nlinarith

/-- the witness theorem (a): g(b) >= h(y_b) for non-exempt b (the telescope, sign part) -/
theorem g_ge_h (W : Witness l F A I h) : ∀ b : Br, b ∉ A → h (msgl l b) ≤ gB l F b := by
  have hl := W.lam_pos.le
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n → b ∉ A → h (msgl l b) ≤ gB l F b := by
    intro n
    induction n with
    | zero => intro b hb; cases b with | node cs => simp [size] at hb
    | succ n IH =>
      intro b hsz hbA
      cases b with
      | node cs =>
        rcases eq_or_ne cs [] with rfl | hne
        · rw [gB_leaf, Witness.msg_mem.msgl_leaf']; exact (W.leaf hbA).2
        · -- split children
          set pA : Br → Bool := fun c => decide (c ∈ A)
          set N := nonE A cs
          set m := N.length
          have hN : N = cs.filter (fun c => !pA c) := by
            simp only [N, nonE, pA]; congr 1; funext c; simp
          have hE : exE A cs = ↑(cs.filter pA) := rfl
          have hlen : (cs.length : ℝ) = ((cs.filter pA).length : ℝ) + m := by
            rw [length_split pA cs, ← hN]; push_cast; ring
          have hIH : ∀ c ∈ N, h (msgl l c) ≤ gB l F c := by
            intro c hc
            have hcs : c ∈ cs := (List.mem_filter.mp hc).1
            have hcA : c ∉ A := by simpa using (List.mem_filter.mp hc).2
            apply IH c _ hcA
            have := size_le_of_mem cs c hcs; simp only [size] at hsz; omega
          have hNI : ∀ c ∈ N, msgl l c ∈ I := fun c hc => W.msg_mem (by simpa using (List.mem_filter.mp hc).2)
          -- mean message and Jensen
          set ys := N.map (msgl l)
          set ybar := ys.sum / m
          have hjen : (m : ℝ) * h ybar ≤ (ys.map h).sum ∧ (0 < m → ybar ∈ I) := by
            rcases Nat.eq_zero_or_pos m with hm0 | hmpos
            · have : N = [] := List.length_eq_zero_iff.mp hm0
              simp [ys, this, hm0]
            · have hne' : ys ≠ [] := by
                simp only [ys, ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos hmpos
              have hlen' : (ys.length : ℝ) = m := by simp [ys, m]
              obtain ⟨h1, h2⟩ := jensen_list W.convex ys hne' (by
                intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hNI c hc)
              rw [hlen'] at h1 h2
              exact ⟨h2, fun _ => h1⟩
          have hsumN : (ys.map h).sum ≤ (N.map (gB l F)).sum := by
            simp only [ys, List.map_map]
            exact List.sum_le_sum (fun c hc => hIH c hc)
          -- Bellman at (E, m, ybar)
          have hTNE := W.typeNonExempt_of_not_mem hbA
          simp only [typeOf] at hTNE
          have hEA : ∀ a ∈ exE A cs, a ∈ A := by
            intro a ha; rw [hE, Multiset.mem_coe] at ha; simpa [pA] using (List.mem_filter.mp ha).2
          have hcard : 1 ≤ (exE A cs).card + m := by
            have : (exE A cs).card + m = cs.length := by
              rw [hE, Multiset.coe_card]; rw [length_split pA cs, ← hN]
            rw [this]; exact List.length_pos_iff.mpr hne
          have hbell := W.bell (exE A cs) m hEA hcard hTNE ybar hjen.2
          unfold Bellman at hbell
          -- identify d, R, sums
          have hcardR : ((exE A cs).card : ℝ) + m + 1 = (cs.length : ℝ) + 1 := by
            rw [hE, Multiset.coe_card, hlen]
          have hmy : (m : ℝ) * ybar = ys.sum := by
            rcases Nat.eq_zero_or_pos m with hm0 | hmpos
            · have : N = [] := List.length_eq_zero_iff.mp hm0
              simp [ys, this, hm0]
            · simp only [ybar]; field_simp
          have hR : ((exE A cs).map (msgl l)).sum + m * ybar = sumYl l cs := by
            rw [hmy, hE, Multiset.map_coe, Multiset.sum_coe, sumYl_map', sum_split pA (msgl l) cs, ← hN]
          have hG : ((exE A cs).map (gB l F)).sum + (N.map (gB l F)).sum = (cs.map (gB l F)).sum := by
            rw [hE, Multiset.map_coe, Multiset.sum_coe, sum_split pA (gB l F) cs, ← hN]
          rw [hcardR, hR] at hbell
          rw [gB_node hl, ← hG, msgl_node]
          have hd : ((cs.length : ℝ) + 1 + l * sumYl l cs) = (cs.length : ℝ) + 1 + l * sumYl l cs := rfl
          linarith [hjen.1]
  exact fun b hb => H (size b) b le_rfl hb

/-- the witness theorem (a), complete -/
theorem mt_main_a (W : Witness l F A I h) :
    (∀ y ∈ I, 0 ≤ h y) ∧ (∀ b, b ∉ A → h (msgl l b) ≤ gB l F b ∧ 0 ≤ h (msgl l b)) ∧ (∀ b ∈ A, 0 ≤ gB l F b) ∧
      ∀ b : Br, Tl l b ≤ Real.exp (F * size b) := by
  refine ⟨W.h_nonneg, fun b hb => ⟨W.g_ge_h b hb, W.h_nonneg _ (W.msg_mem hb)⟩, W.H0, fun b => ?_⟩
  have hg : 0 ≤ gB l F b := by
    by_cases hb : b ∈ A
    · exact W.H0 b hb
    · exact le_trans (W.h_nonneg _ (W.msg_mem hb)) (W.g_ge_h b hb)
  unfold gB at hg
  have hT := Tl_pos W.lam_pos.le b
  calc Tl l b = Real.exp (Real.log (Tl l b)) := (Real.exp_log hT).symm
    _ ≤ Real.exp (F * size b) := Real.exp_le_exp.mpr (by linarith)

lemma g_nonneg (W : Witness l F A I h) (b : Br) : 0 ≤ gB l F b := by
  by_cases hb : b ∈ A
  · exact W.H0 b hb
  · exact le_trans (W.h_nonneg _ (W.msg_mem hb)) (W.g_ge_h b hb)

end Witness

/-! ### consequences of a ceiling (shared by (b), (c) and Part (B)) -/

lemma rhoB_le_exp {l F : ℝ} (hl : 0 ≤ l) (hc : ∀ b : Br, Tl l b ≤ Real.exp (F * size b)) : rhoB l ≤ Real.exp F := by
  apply csSup_le ⟨1, one_mem_rhoSet l⟩
  rintro x ⟨b, rfl⟩
  have hs : (0:ℝ) < size b := by exact_mod_cast size_pos b
  calc Tl l b ^ (1 / (size b : ℝ)) ≤ (Real.exp (F * size b)) ^ (1 / (size b : ℝ)) :=
        Real.rpow_le_rpow (Tl_pos hl b).le (hc b) (by positivity)
    _ = Real.exp F := by rw [← Real.exp_mul]; congr 1; field_simp

lemma Mn_le_exp {l F : ℝ} (hl : 0 ≤ l) (hc : ∀ b : Br, Tl l b ≤ Real.exp (F * size b)) {n : ℕ} (hn : 1 ≤ n) :
    Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1)) := by
  have h1 := Mn_le_rho hl hn
  have h2 := rhoB_le_exp hl hc
  have hr := one_le_rhoB hl
  calc Mn l n ≤ (1 + l) * rhoB l ^ (n - 1) := h1
    _ ≤ (1 + l) * Real.exp F ^ (n - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 _) (by linarith)
    _ = (1 + l) * Real.exp (F * ((n : ℝ) - 1)) := by
        rw [← Real.exp_nat_mul]; push_cast [Nat.cast_sub hn]; ring_nf

lemma tight_consequences {l F : ℝ} (hl : 0 ≤ l) (hc : ∀ b : Br, Tl l b ≤ Real.exp (F * size b))
    {bs : Br} (hbs : gB l F bs = 0) :
    rhoB l = Real.exp F ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (F * size bs * (((n - 1) / size bs : ℕ) : ℝ)) ≤ Mn l n ∧ Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1)) := by
  have hT : Tl l bs = Real.exp (F * size bs) := by
    unfold gB at hbs
    rw [← Real.exp_log (Tl_pos hl bs)]; congr 1; linarith
  refine ⟨le_antisymm (rhoB_le_exp hl hc) ?_, fun n hn => ⟨?_, Mn_le_exp hl hc hn⟩⟩
  · have hs : (0:ℝ) < size bs := by exact_mod_cast size_pos bs
    apply le_csSup (rhoSet_bdd hl)
    refine ⟨bs, ?_⟩
    rw [hT, ← Real.exp_mul]; congr 1; field_simp
  · have := Mn_ge_block hl hn bs
    rw [hT, ← Real.exp_nat_mul] at this
    calc Real.exp (F * size bs * (((n - 1) / size bs : ℕ) : ℝ))
        = Real.exp ((((n - 1) / size bs : ℕ) : ℝ) * (F * size bs)) := by ring_nf
      _ ≤ Mn l n := this

namespace Witness

variable {l F : ℝ} {A : Set Br} {I : Set ℝ} {h : ℝ → ℝ}

/-- the witness theorem (b) -/
theorem mt_main_b (W : Witness l F A I h) :
    (∀ n : ℕ, 1 ≤ n → Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1))) ∧ rhoB l ≤ Real.exp F :=
  ⟨fun _ hn => Mn_le_exp W.lam_pos.le W.mt_main_a.2.2.2 hn, rhoB_le_exp W.lam_pos.le W.mt_main_a.2.2.2⟩

/-- the witness theorem (c) -/
theorem mt_main_c (W : Witness l F A I h) {bs : Br} (hbs : gB l F bs = 0) :
    rhoB l = Real.exp F ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (F * size bs * (((n - 1) / size bs : ℕ) : ℝ)) ≤ Mn l n ∧ Mn l n ≤ (1 + l) * Real.exp (F * ((n : ℝ) - 1)) :=
  tight_consequences W.lam_pos.le W.mt_main_a.2.2.2 hbs

/-! ### (d) tight branches -/

/-- b is tight: non-exempt with g(b) = h(y_b) -/
def TightB (l F : ℝ) (A : Set Br) (h : ℝ → ℝ) (b : Br) : Prop := b ∉ A ∧ gB l F b = h (msgl l b)

/-- (d), leaf: a non-exempt leaf is tight iff h(1) = F -/
theorem tight_leaf (_W : Witness l F A I h) (hA : Br.node [] ∉ A) : TightB l F A h (.node []) ↔ h 1 = F := by
  unfold TightB
  rw [gB_leaf, msg_mem.msgl_leaf']
  constructor
  · rintro ⟨_, h1⟩; exact h1.symm
  · intro h1; exact ⟨hA, h1.symm⟩

/-- the three nonnegative brackets of sigma_root: g(b) - h(y_b) = sum_i (g c_i - h y_ci) + Jensen gap + Bellman slack -/
lemma decomp (W : Witness l F A I h) (cs : List Br) :
    let N := nonE A cs
    let m := N.length
    let ybar := (N.map (msgl l)).sum / m
    gB l F (.node cs) - h (msgl l (.node cs)) =
      (N.map (fun c => gB l F c - h (msgl l c))).sum
      + (((N.map (msgl l)).map h).sum - m * h ybar)
      + (F + ((exE A cs).map (gB l F)).sum + m * h ybar
          - Real.log (1 + l * (((exE A cs).map (msgl l)).sum + m * ybar) / (((exE A cs).card : ℝ) + m + 1))
          - h (1 / (((exE A cs).card : ℝ) + m + 1 + l * (((exE A cs).map (msgl l)).sum + m * ybar)))) := by
  intro N m ybar
  have hl := W.lam_pos.le
  set pA : Br → Bool := fun c => decide (c ∈ A)
  have hN : N = cs.filter (fun c => !pA c) := by simp only [N, nonE, pA]; congr 1; funext c; simp
  have hE : exE A cs = ↑(cs.filter pA) := rfl
  have hlen : (cs.length : ℝ) = ((cs.filter pA).length : ℝ) + m := by rw [length_split pA cs, ← hN]; push_cast; ring
  have hmy : (m : ℝ) * ybar = (N.map (msgl l)).sum := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have : N = [] := List.length_eq_zero_iff.mp hm0
      simp [this, hm0]
    · simp only [ybar]; field_simp
  have hcardR : ((exE A cs).card : ℝ) + m + 1 = (cs.length : ℝ) + 1 := by rw [hE, Multiset.coe_card, hlen]
  have hR : ((exE A cs).map (msgl l)).sum + m * ybar = sumYl l cs := by
    rw [hmy, hE, Multiset.map_coe, Multiset.sum_coe, sumYl_map', sum_split pA (msgl l) cs, ← hN]
  have hG : ((exE A cs).map (gB l F)).sum + (N.map (gB l F)).sum = (cs.map (gB l F)).sum := by
    rw [hE, Multiset.map_coe, Multiset.sum_coe, sum_split pA (gB l F) cs, ← hN]
  rw [hcardR, hR, gB_node hl, ← hG, msgl_node, lsum_sub, List.map_map]
  simp only [Function.comp_def]
  ring

lemma sum_nonneg_eq_zero_iff {f : Br → ℝ} : ∀ L : List Br, (∀ c ∈ L, 0 ≤ f c) →
    ((L.map f).sum = 0 ↔ ∀ c ∈ L, f c = 0)
  | [], _ => by simp
  | c :: L, h0 => by
      have h1 := h0 c List.mem_cons_self
      have h2 : 0 ≤ (L.map f).sum := List.sum_nonneg (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h0 y (List.mem_cons_of_mem _ hy))
      have IH := sum_nonneg_eq_zero_iff L (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
      constructor
      · intro h; exact ⟨by linarith, IH.mp (by linarith)⟩
      · rintro ⟨ha, hb⟩; rw [ha, IH.mpr hb]; ring

/-- the witness theorem (d), non-leaf: a non-leaf non-exempt branch is tight iff every non-exempt child is tight, Jensen is an equality,
    and the Bellman inequality is an equality at (E, m, ybar) -/
theorem tight_node (W : Witness l F A I h) (cs : List Br) (hne : cs ≠ []) (hbA : Br.node cs ∉ A) :
    let N := nonE A cs
    let m := N.length
    let ybar := (N.map (msgl l)).sum / m
    TightB l F A h (.node cs) ↔
      (∀ c ∈ N, TightB l F A h c) ∧ ((N.map (msgl l)).map h).sum = m * h ybar ∧
      h (1 / (((exE A cs).card : ℝ) + m + 1 + l * (((exE A cs).map (msgl l)).sum + m * ybar))) =
        F + ((exE A cs).map (gB l F)).sum + m * h ybar
          - Real.log (1 + l * (((exE A cs).map (msgl l)).sum + m * ybar) / (((exE A cs).card : ℝ) + m + 1)) := by
  intro N m ybar
  have hl := W.lam_pos.le
  have hD := W.decomp cs
  simp only at hD
  have hNA : ∀ c ∈ N, c ∉ A := fun c hc => by simpa using (List.mem_filter.mp hc).2
  -- the three brackets are nonnegative
  have b1 : ∀ c ∈ N, 0 ≤ gB l F c - h (msgl l c) := fun c hc => by linarith [W.g_ge_h c (hNA c hc)]
  have hNI : ∀ c ∈ N, msgl l c ∈ I := fun c hc => W.msg_mem (hNA c hc)
  have b2 : (m : ℝ) * h ybar ≤ ((N.map (msgl l)).map h).sum := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have : N = [] := List.length_eq_zero_iff.mp hm0
      simp [this, hm0]
    · have hne' : N.map (msgl l) ≠ [] := by simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos hmpos
      have hlen' : ((N.map (msgl l)).length : ℝ) = m := by simp [m]
      have := (jensen_list W.convex (N.map (msgl l)) hne' (by
        intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hNI c hc)).2
      rwa [hlen'] at this
  have hybarI : 0 < m → ybar ∈ I := by
    intro hmpos
    have hne' : N.map (msgl l) ≠ [] := by simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos hmpos
    have hlen' : ((N.map (msgl l)).length : ℝ) = m := by simp [m]
    have := (jensen_list W.convex (N.map (msgl l)) hne' (by
      intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hNI c hc)).1
    rwa [hlen'] at this
  have hTNE := W.typeNonExempt_of_not_mem hbA
  simp only [typeOf] at hTNE
  have hEA : ∀ a ∈ exE A cs, a ∈ A := by
    intro a ha; rw [show exE A cs = ↑(cs.filter (fun c => decide (c ∈ A))) from rfl, Multiset.mem_coe] at ha
    simpa using (List.mem_filter.mp ha).2
  have hcard : 1 ≤ (exE A cs).card + m := by
    have : (exE A cs).card + m = cs.length := by
      rw [show exE A cs = ↑(cs.filter (fun c => decide (c ∈ A))) from rfl, Multiset.coe_card]
      rw [length_split (fun c => decide (c ∈ A)) cs]; congr 1; simp only [m, N, nonE]; congr 2; funext c; simp
    rw [this]; exact List.length_pos_iff.mpr hne
  have b3 := W.bell (exE A cs) m hEA hcard hTNE ybar hybarI
  unfold Bellman at b3
  have hS1 : 0 ≤ (N.map (fun c => gB l F c - h (msgl l c))).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact b1 c hc)
  constructor
  · rintro ⟨_, ht⟩
    have hzero : gB l F (.node cs) - h (msgl l (.node cs)) = 0 := by rw [ht]; ring
    rw [hD] at hzero
    have e1 : (N.map (fun c => gB l F c - h (msgl l c))).sum = 0 := by linarith
    refine ⟨fun c hc => ⟨hNA c hc, ?_⟩, by linarith, by linarith⟩
    have := ((sum_nonneg_eq_zero_iff N b1).mp e1) c hc
    linarith
  · rintro ⟨hc, hj, hb⟩
    refine ⟨hbA, ?_⟩
    have e1 : (N.map (fun c => gB l F c - h (msgl l c))).sum = 0 :=
      (sum_nonneg_eq_zero_iff N b1).mpr (fun c hc' => by rw [(hc c hc').2]; ring)
    linarith

/-- the witness theorem (d), Jensen equality at a strict supporting line forces equal messages
    (the corner hypothesis of the hand proof gives such a line; that step is not formalized here) -/
theorem jensen_eq_forces (W : Witness l F A I h) (cs : List Br) {s : ℝ}
    (hsupp : ∀ y ∈ I, y ≠ (((nonE A cs).map (msgl l)).sum / (nonE A cs).length) →
      h ((((nonE A cs).map (msgl l)).sum / (nonE A cs).length)) + s * (y - (((nonE A cs).map (msgl l)).sum / (nonE A cs).length)) < h y)
    (hmpos : 0 < (nonE A cs).length)
    (heq : (((nonE A cs).map (msgl l)).map h).sum = ((nonE A cs).length : ℝ) * h ((((nonE A cs).map (msgl l)).sum / (nonE A cs).length))) :
    ∀ c ∈ nonE A cs, msgl l c = (((nonE A cs).map (msgl l)).sum / (nonE A cs).length) := by
  set N := nonE A cs
  set m := N.length
  set ybar := (N.map (msgl l)).sum / m
  have hNI : ∀ c ∈ N, msgl l c ∈ I := fun c hc => W.msg_mem (by simpa using (List.mem_filter.mp hc).2)
  have hm : (m : ℝ) * ybar = (N.map (msgl l)).sum := by simp only [ybar]; field_simp
  -- sum of (h y_c - h ybar - s (y_c - ybar)) = 0, each term >= 0
  set f : Br → ℝ := fun c => h (msgl l c) - h ybar - s * (msgl l c - ybar)
  have hf0 : ∀ c ∈ N, 0 ≤ f c := by
    intro c hc
    by_cases hy : msgl l c = ybar
    · simp [f, hy]
    · have := hsupp _ (hNI c hc) hy; simp only [f]; linarith
  have hsum : (N.map f).sum = 0 := by
    have e1 : (N.map f).sum = (N.map (fun c => h (msgl l c))).sum - (m : ℝ) * h ybar
        - s * ((N.map (msgl l)).sum - (m : ℝ) * ybar) := by
      simp only [f]
      rw [show (fun c => h (msgl l c) - h ybar - s * (msgl l c - ybar))
          = (fun c => (h (msgl l c) - h ybar) - s * (msgl l c - ybar)) from rfl,
        lsum_sub, lsum_sub, lsum_const, lsum_mul_left, lsum_sub, lsum_const]
    rw [List.map_map] at heq
    simp only [Function.comp_def] at heq
    rw [e1, heq, hm]; ring
  intro c hc
  have h0 := ((sum_nonneg_eq_zero_iff N hf0).mp hsum) c hc
  by_contra hne
  have := hsupp _ (hNI c hc) hne
  simp only [f] at h0; linarith

/-- the witness theorem (d), last sentence: a non-exempt branch with g(b) = 0 is tight and has h(y_b) = 0 -/
theorem tight_of_g_zero (W : Witness l F A I h) {b : Br} (hb : b ∉ A) (hg : gB l F b = 0) :
    TightB l F A h b ∧ h (msgl l b) = 0 := by
  have h1 := W.g_ge_h b hb
  have h2 := W.h_nonneg _ (W.msg_mem hb)
  have : h (msgl l b) = 0 := by linarith
  exact ⟨⟨hb, by rw [hg, this]⟩, this⟩

end Witness

end

end LeanCherry
