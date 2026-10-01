/-
LeanCherry.Rho -- the general one-block formula for every l >= 0.
  rhoB l := sSup {T_b^(1/|b|) : b planted branch}
  Tl_le_pow    : T_b <= (1 + l)^(|b| - 1)
  rhoB_le      : rhoB l <= 1 + l
  Mn_ge_block  : T_b^⌊(n-1)/|b|⌋ <= M_n          (k copies of b and the remaining leaves joined to a new centre)
  Mn_le_rho    : M_n <= (1 + l) rhoB^(n-1)       (root step, R <= k)
  Mn_tendsto_rho : M_n^(1/n) -> rhoB l           (l > 0)
-/
import LeanCherry.Growth

open Finset Filter Topology

namespace LeanCherry

noncomputable section

namespace Br

/-- T_b <= (1 + l)^(|b| - 1), real exponent form -/
theorem Tl_le_rpow {l : ℝ} (hl : 0 ≤ l) : ∀ b : Br, Tl l b ≤ (1 + l) ^ ((size b : ℝ) - 1) := by
  have hb : (1:ℝ) ≤ 1 + l := by linarith
  have hb0 : (0:ℝ) < 1 + l := by linarith
  have H : ∀ n : ℕ, ∀ b : Br, size b ≤ n → Tl l b ≤ (1 + l) ^ ((size b : ℝ) - 1) := by
    intro n
    induction n with
    | zero => intro b hb'; cases b with | node cs => simp [size] at hb'
    | succ n IH =>
      intro b hsz
      cases b with
      | node cs =>
        have hch : ∀ c ∈ cs, Tl l c ≤ (1 + l) ^ ((size c : ℝ) - 1) := by
          intro c hc; apply IH; have := size_le_of_mem cs c hc; simp only [size] at hsz; omega
        -- product over children
        have hprod : ∀ L : List Br, (∀ c ∈ L, Tl l c ≤ (1 + l) ^ ((size c : ℝ) - 1)) →
            prodTl l L ≤ (1 + l) ^ ((sizeL L : ℝ) - L.length) := by
          intro L
          induction L with
          | nil => intro _; simp [prodTl, sizeL]
          | cons c L ih =>
            intro hL
            simp only [prodTl, sizeL, List.length_cons]
            push_cast
            rw [show ((size c : ℝ) + sizeL L) - (L.length + 1) = ((size c : ℝ) - 1) + ((sizeL L : ℝ) - L.length) by ring,
              Real.rpow_add hb0]
            exact mul_le_mul (hL c List.mem_cons_self) (ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)))
              (prodTl_pos hl L).le (Real.rpow_nonneg hb0.le _)
        have hP := hprod cs hch
        rw [Tl_node]
        simp only [size]; push_cast
        rcases eq_or_ne cs [] with rfl | hne
        · simp [prodTl, sumYl, sizeL]
        · have hk : (1:ℝ) ≤ cs.length := by exact_mod_cast List.length_pos_iff.mpr hne
          have hfac : 1 + l * sumYl l cs / ((cs.length : ℝ) + 1) ≤ (1 + l) ^ (1:ℝ) := by
            rw [Real.rpow_one]
            have : l * sumYl l cs / ((cs.length : ℝ) + 1) ≤ l := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith [sumYl_le_length hl cs, mul_nonneg hl (sumYl_nonneg hl cs)]
            linarith
          have hfac0 : 0 ≤ 1 + l * sumYl l cs / ((cs.length : ℝ) + 1) := by
            have := div_nonneg (mul_nonneg hl (sumYl_nonneg hl cs)) (by positivity : (0:ℝ) ≤ (cs.length : ℝ) + 1)
            linarith
          calc prodTl l cs * (1 + l * sumYl l cs / ((cs.length : ℝ) + 1))
              ≤ (1 + l) ^ ((sizeL cs : ℝ) - cs.length) * (1 + l) ^ (1:ℝ) :=
                mul_le_mul hP hfac hfac0 (Real.rpow_nonneg hb0.le _)
            _ = (1 + l) ^ ((sizeL cs : ℝ) - cs.length + 1) := by rw [← Real.rpow_add hb0]
            _ ≤ (1 + l) ^ ((sizeL cs : ℝ) + 1 - 1) :=
                Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  exact fun b => H (size b) b le_rfl

lemma size_pos (b : Br) : 1 ≤ size b := by cases b; simp [size]

/-- T_b <= (1 + l)^(|b| - 1) -/
theorem Tl_le_pow {l : ℝ} (hl : 0 ≤ l) (b : Br) : Tl l b ≤ (1 + l) ^ (size b - 1) := by
  have h := Tl_le_rpow hl b
  rwa [show (size b : ℝ) - 1 = ((size b - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub (size_pos b)]; ring,
    Real.rpow_natCast] at h

end Br

/-- rho(l) = sup over planted branches of T_b^(1/|b|) -/
def rhoSet (l : ℝ) : Set ℝ := {x | ∃ b : Br, x = Br.Tl l b ^ (1 / (Br.size b : ℝ))}
def rhoB (l : ℝ) : ℝ := sSup (rhoSet l)

lemma rhoSet_le {l : ℝ} (hl : 0 ≤ l) : ∀ x ∈ rhoSet l, x ≤ 1 + l := by
  rintro x ⟨b, rfl⟩
  have hb0 : (0:ℝ) < 1 + l := by linarith
  have hs : (0:ℝ) < Br.size b := by exact_mod_cast Br.size_pos b
  calc Br.Tl l b ^ (1 / (Br.size b : ℝ)) ≤ ((1 + l) ^ ((Br.size b : ℝ) - 1)) ^ (1 / (Br.size b : ℝ)) :=
        Real.rpow_le_rpow (Br.Tl_pos hl b).le (Br.Tl_le_rpow hl b) (by positivity)
    _ = (1 + l) ^ (((Br.size b : ℝ) - 1) * (1 / (Br.size b : ℝ))) := by rw [← Real.rpow_mul hb0.le]
    _ ≤ (1 + l) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        rw [mul_one_div, div_le_one hs]; linarith
    _ = 1 + l := Real.rpow_one _

lemma rhoSet_bdd {l : ℝ} (hl : 0 ≤ l) : BddAbove (rhoSet l) := ⟨1 + l, rhoSet_le hl⟩

lemma one_mem_rhoSet (l : ℝ) : (1 : ℝ) ∈ rhoSet l := ⟨.node [], by rw [Br.Tl_leaf]; simp⟩

/-- rho(l) <= 1 + l -/
theorem rhoB_le {l : ℝ} (hl : 0 ≤ l) : rhoB l ≤ 1 + l := csSup_le ⟨1, one_mem_rhoSet l⟩ (rhoSet_le hl)

lemma one_le_rhoB {l : ℝ} (hl : 0 ≤ l) : 1 ≤ rhoB l := le_csSup (rhoSet_bdd hl) (one_mem_rhoSet l)

/-- consistency with rho_eq -/
theorem rhoB_eq_cherry {l : ℝ} (hl : 1 + √5 ≤ l) : rhoB l = √(1 + l / 2) := rho_eq hl

lemma Tl_le_rhoB_pow {l : ℝ} (hl : 0 ≤ l) (b : Br) : Br.Tl l b ≤ rhoB l ^ Br.size b := by
  have hs : (0:ℝ) < Br.size b := by exact_mod_cast Br.size_pos b
  have hx : Br.Tl l b ^ (1 / (Br.size b : ℝ)) ≤ rhoB l := le_csSup (rhoSet_bdd hl) ⟨b, rfl⟩
  have hT := Br.Tl_pos hl b
  calc Br.Tl l b = (Br.Tl l b ^ (1 / (Br.size b : ℝ))) ^ (Br.size b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le, one_div_mul_cancel hs.ne', Real.rpow_one]
    _ ≤ rhoB l ^ Br.size b := pow_le_pow_left₀ (Real.rpow_nonneg hT.le _) hx _

namespace Br

/-- the block witness: k copies of b and r leaves joined to a new centre -/
def blk (b : Br) (k r : ℕ) : Br := .node (List.replicate k b ++ List.replicate r (.node []))

lemma blk_size (b : Br) (k r : ℕ) : size (blk b k r) = k * size b + r + 1 := by
  simp only [blk, size, sizeL_append, sizeL_replicate]; simp [size, sizeL]

lemma blk_ZTl {l : ℝ} (hl : 0 ≤ l) (b : Br) (k r : ℕ) : Tl l b ^ k ≤ ZTl l (blk b k r) := by
  rw [blk, ZTl_node hl, prodTl_append, prodTl_replicate, prodTl_replicate, Tl_leaf, one_pow, mul_one]
  have hb : 0 ≤ Tl l b ^ k := pow_nonneg (Tl_pos hl b).le _
  have hf : 0 ≤ l * sumYl l (List.replicate k b ++ List.replicate r (Br.node [])) /
      ((List.replicate k b ++ List.replicate r (Br.node [])).length : ℝ) :=
    div_nonneg (mul_nonneg hl (sumYl_nonneg hl _)) (by positivity)
  nlinarith

end Br

lemma ZTl_le_Mn {l : ℝ} {n : ℕ} (hn : 1 ≤ n) (b : Br) (hb : Br.size b = n) : Br.ZTl l b ≤ Mn l n := by
  classical
  subst hb
  unfold Mn
  rw [dif_pos (trees_nonempty hn)]
  obtain ⟨htree, hpi⟩ := Br.realize_br b
  rw [← hpi l]
  exact le_sup' (fun G => piL l G) (mem_filter.mpr ⟨mem_univ _, htree⟩)

/-- the block lower bound -/
theorem Mn_ge_block {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) (b : Br) :
    Br.Tl l b ^ ((n - 1) / Br.size b) ≤ Mn l n := by
  set k := (n - 1) / Br.size b
  have hk : k * Br.size b ≤ n - 1 := Nat.div_mul_le_self _ _
  have hsize : Br.size (Br.blk b k (n - 1 - k * Br.size b)) = n := by rw [Br.blk_size]; omega
  exact (Br.blk_ZTl hl b k _).trans (ZTl_le_Mn hn _ hsize)

/-- the rho upper bound -/
theorem Mn_le_rho {l : ℝ} (hl : 0 ≤ l) {n : ℕ} (hn : 1 ≤ n) : Mn l n ≤ (1 + l) * rhoB l ^ (n - 1) := by
  classical
  unfold Mn
  rw [dif_pos (trees_nonempty hn)]
  apply sup'_le
  intro G hG
  obtain ⟨b, f, hf, _, hsize, he⟩ := Br.tree_realize (Fintype.card (Fin n)) G (mem_filter.mp hG).2 rfl
  rw [Br.piL_eq_ZTl G hf he l]
  rw [Fintype.card_fin] at hsize
  subst hsize
  have hr1 := one_le_rhoB hl
  cases b with
  | node cs =>
    rw [Br.ZTl_node hl]
    have hsz : Br.size (.node cs) - 1 = Br.sizeL cs := by simp [Br.size]
    rw [hsz]
    -- product bound
    have hprod : ∀ L : List Br, Br.prodTl l L ≤ rhoB l ^ Br.sizeL L := by
      intro L
      induction L with
      | nil => simp [Br.prodTl, Br.sizeL]
      | cons c L ih =>
        simp only [Br.prodTl, Br.sizeL, pow_add]
        exact mul_le_mul (Tl_le_rhoB_pow hl c) ih (Br.prodTl_pos hl L).le (pow_nonneg (by linarith) _)
    have hP := hprod cs
    have hfac : 1 + l * Br.sumYl l cs / (cs.length : ℝ) ≤ 1 + l := by
      rcases eq_or_ne cs [] with rfl | hne
      · simp; exact hl
      · have hk : (0:ℝ) < cs.length := by exact_mod_cast List.length_pos_iff.mpr hne
        have : l * Br.sumYl l cs / (cs.length : ℝ) ≤ l := by
          rw [div_le_iff₀ hk]; exact mul_le_mul_of_nonneg_left (Br.sumYl_le_length hl cs) hl
        linarith
    have hfac0 : 0 ≤ 1 + l * Br.sumYl l cs / (cs.length : ℝ) := by
      have := div_nonneg (mul_nonneg hl (Br.sumYl_nonneg hl cs)) (by positivity : (0:ℝ) ≤ (cs.length : ℝ))
      linarith
    calc Br.prodTl l cs * (1 + l * Br.sumYl l cs / (cs.length : ℝ)) ≤ rhoB l ^ Br.sizeL cs * (1 + l) :=
          mul_le_mul hP hfac hfac0 (pow_nonneg (by linarith) _)
      _ = (1 + l) * rhoB l ^ Br.sizeL cs := by ring

/-- lim M_n^(1/n) = rho -/
theorem Mn_tendsto_rho {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => Mn l n ^ (1 / (n : ℝ))) atTop (𝓝 (rhoB l)) := by
  have hl0 := hl.le
  have hr1 := one_le_rhoB hl0
  have hr0 : 0 < rhoB l := by linarith
  have hb1 : 0 < 1 + l := by linarith
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hMpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ Mn l n := fun n hn =>
    le_trans (pow_nonneg (Br.Tl_pos hl0 (.node [])).le _) (Mn_ge_block hl0 hn (.node []))
  rw [tendsto_order]
  constructor
  · -- liminf >= rho
    intro a ha
    obtain ⟨x, ⟨b, rfl⟩, hxa⟩ := exists_lt_of_lt_csSup ⟨1, one_mem_rhoSet l⟩ ha
    set s := Br.size b
    have hs : (0:ℝ) < s := by exact_mod_cast Br.size_pos b
    have hT := Br.Tl_pos hl0 b
    -- exponent k_n / n -> 1/s
    have hup : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / s * (1 / (n : ℝ))) atTop (𝓝 (1 / s)) := by
      have : (fun n : ℕ => ((n : ℝ) - 1) / s * (1 / (n : ℝ))) =ᶠ[atTop] (fun n : ℕ => 1 / s - (1 / s) * (1 / (n : ℝ))) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' this]
      have := (tendsto_const_nhds (x := (1 / s : ℝ))).sub (hinv.const_mul (1 / (s : ℝ)))
      rw [mul_zero, sub_zero] at this; exact this
    have hlow : Tendsto (fun n : ℕ => ((n : ℝ) - 1 - s) / s * (1 / (n : ℝ))) atTop (𝓝 (1 / s)) := by
      have : (fun n : ℕ => ((n : ℝ) - 1 - s) / s * (1 / (n : ℝ))) =ᶠ[atTop]
          (fun n : ℕ => 1 / s - ((1 + s) / s) * (1 / (n : ℝ))) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rw [tendsto_congr' this]
      have := (tendsto_const_nhds (x := (1 / s : ℝ))).sub (hinv.const_mul ((1 + (s : ℝ)) / s))
      rw [mul_zero, sub_zero] at this; exact this
    have hk : Tendsto (fun n : ℕ => (((n - 1) / s : ℕ) : ℝ) * (1 / (n : ℝ))) atTop (𝓝 (1 / s)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have h1 : n - 1 < s * ((n - 1) / s) + s := by
          have := Nat.lt_div_mul_add (a := n - 1) (Br.size_pos b); rw [mul_comm]; linarith
        have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
        have h3 : ((n - 1 : ℕ) : ℝ) < (s : ℝ) * (((n - 1) / s : ℕ) : ℝ) + s := by exact_mod_cast h1
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_iff₀ hs]; nlinarith
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have h1 : s * ((n - 1) / s) ≤ n - 1 := Nat.mul_div_le _ _
        have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
        have h3 : (s : ℝ) * (((n - 1) / s : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [le_div_iff₀ hs]; nlinarith
    have hlim : Tendsto (fun n : ℕ => Br.Tl l b ^ ((((n - 1) / s : ℕ) : ℝ) * (1 / (n : ℝ)))) atTop
        (𝓝 (Br.Tl l b ^ (1 / (s : ℝ)))) := tendsto_const_nhds.rpow hk (Or.inl hT.ne')
    filter_upwards [hlim.eventually (lt_mem_nhds hxa), eventually_ge_atTop 1] with n h1 hn
    calc a < Br.Tl l b ^ ((((n - 1) / s : ℕ) : ℝ) * (1 / (n : ℝ))) := h1
      _ = (Br.Tl l b ^ ((n - 1) / s)) ^ (1 / (n : ℝ)) := by rw [Real.rpow_mul hT.le, Real.rpow_natCast]
      _ ≤ Mn l n ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg hT.le _) (Mn_ge_block hl0 hn b) (by positivity)
  · -- limsup <= rho
    intro a ha
    have he : Tendsto (fun n : ℕ => ((n : ℝ) - 1) * (1 / (n : ℝ))) atTop (𝓝 1) := by
      have : (fun n : ℕ => ((n : ℝ) - 1) * (1 / (n : ℝ))) =ᶠ[atTop] (fun n : ℕ => 1 - 1 / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' this]
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
      rw [sub_zero] at this; exact this
    have hU : Tendsto (fun n : ℕ => (1 + l) ^ (1 / (n : ℝ)) * rhoB l ^ (((n : ℝ) - 1) * (1 / (n : ℝ)))) atTop
        (𝓝 (rhoB l)) := by
      have h1 : Tendsto (fun n : ℕ => (1 + l) ^ (1 / (n : ℝ))) atTop (𝓝 ((1 + l) ^ (0 : ℝ))) :=
        tendsto_const_nhds.rpow hinv (Or.inl hb1.ne')
      have h2 : Tendsto (fun n : ℕ => rhoB l ^ (((n : ℝ) - 1) * (1 / (n : ℝ)))) atTop (𝓝 (rhoB l ^ (1 : ℝ))) :=
        tendsto_const_nhds.rpow he (Or.inl hr0.ne')
      simpa using h1.mul h2
    filter_upwards [hU.eventually (gt_mem_nhds ha), eventually_ge_atTop 1] with n h1 hn
    calc Mn l n ^ (1 / (n : ℝ)) ≤ ((1 + l) * rhoB l ^ (n - 1)) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (hMpos n hn) (Mn_le_rho hl0 hn) (by positivity)
      _ = (1 + l) ^ (1 / (n : ℝ)) * rhoB l ^ (((n : ℝ) - 1) * (1 / (n : ℝ))) := by
          rw [Real.mul_rpow hb1.le (pow_nonneg hr0.le _), ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
          push_cast [Nat.cast_sub hn]; ring_nf
      _ < a := h1

end

end LeanCherry
