/-
  BGUnique.Controls -- the three negative controls of the uniqueness Comparator challenge
  (`comparator/BGUniqueNeg*.lean`) are false: their negations are proved here.
-/
import BGUnique.Mathlib

namespace R3Cert
namespace BGUnique

open R3Cert.Step3 R3Cert.BGStatement R3Cert.AllUnique R3Cert.RerootIso R3Cert.RerootEquiv

/-- The ratio in the controls' notation is `lapRatio`. -/
theorem ratio_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) = lapRatio G := (lapRatio_eq G).symm

/-- A copy on `Fin m`. -/
theorem copy_fin' {V : Type} [Fintype V] (G : SimpleGraph V) {m : ℕ} (hm : Fintype.card V = m) :
    ∃ G₀ : SimpleGraph (Fin m), Nonempty (G₀ ≃g G) :=
  ⟨G.comap (Fintype.equivFinOfCardEq hm).symm, ⟨SimpleGraph.Iso.comap (Fintype.equivFinOfCardEq hm).symm G⟩⟩

theorem card_real_21 : Fintype.card (AVert (Step3.realize (dtRealize (BGMaximizerAll.bgMax 21)))) = 21 := by
  rw [card_verts_realize _ (by have := (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1; omega),
    (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1]

theorem card_real_S21 : Fintype.card (AVert (Step3.realize (dtRealize S21))) = 21 := by
  rw [card_verts_realize _ (by rw [usize_S21]; omega), usize_S21]

/-- Control `BGUniqueNegAt21` is false: uniqueness fails at `n = 21`. -/
theorem not_negAt21 :
    ¬ ∀ (n : ℕ) (_ : 4 ≤ n)
      {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      {W : Type} [Fintype W] [DecidableEq W] (G' : SimpleGraph W) [DecidableRel G'.Adj]
      (_ : G.IsTree) (_ : Fintype.card V = n) (_ : G'.IsTree) (_ : Fintype.card W = n)
      (_ : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = n →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)))
      (_ : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = n →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G'.lapMatrix ℝ).permanent / (∏ v, (G'.degree v : ℝ))),
      Nonempty (G ≃g G') := by
  classical
  intro h
  obtain ⟨hA, hB, hne⟩ := bg_maximizers_21_mathlib
  have hsz := (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1
  obtain ⟨ψ⟩ := h 21 (by norm_num) (real (BGMaximizerAll.bgMax 21)) (real S21)
    (real_isTree _ (by omega)) card_real_21 (real_isTree _ (by rw [usize_S21]; omega)) card_real_S21
    (fun X _ _ H _ hH hX => by rw [ratio_eq, ratio_eq]; exact hA X H hH hX)
    (fun X _ _ H _ hH hX => by rw [ratio_eq, ratio_eq]; exact hB X H hH hX)
  exact hne.false ψ

/-- Control `BGUniqueNegOneClass21` is false: the maximizers at `n = 21` form two isomorphism classes. -/
theorem not_negOneClass21 :
    ¬ ∃ (G₁ : SimpleGraph (Fin 21)) (_ : DecidableRel G₁.Adj), G₁.IsTree ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ))) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) = (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) →
          Nonempty (H ≃g G₁)) := by
  classical
  rintro ⟨G₁, inst, t1, hmax, hall⟩
  obtain ⟨hA, hB, hne⟩ := bg_maximizers_21_mathlib
  have hsz := (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1
  have m1 : IsBGMax 21 G₁ := by
    intro X _ H hH hX
    have h := hmax X H hH hX
    rwa [ratio_eq, ratio_eq] at h
  have eqA : lapRatio (real (BGMaximizerAll.bgMax 21)) = lapRatio G₁ :=
    le_antisymm (m1 _ _ (real_isTree _ (by omega)) card_real_21) (hA _ G₁ t1 (Fintype.card_fin 21))
  have eqB : lapRatio (real S21) = lapRatio G₁ :=
    le_antisymm (m1 _ _ (real_isTree _ (by rw [usize_S21]; omega)) card_real_S21) (hB _ G₁ t1 (Fintype.card_fin 21))
  obtain ⟨a⟩ := hall _ (real (BGMaximizerAll.bgMax 21)) (real_isTree _ (by omega)) card_real_21
    (by rw [ratio_eq, ratio_eq]; exact eqA)
  obtain ⟨b⟩ := hall _ (real S21) (real_isTree _ (by rw [usize_S21]; omega)) card_real_S21
    (by rw [ratio_eq, ratio_eq]; exact eqB)
  exact hne.false (a.trans b.symm)

/-- The star `K_{1,3}`, rooted at its centre. -/
def star4 : UTree := .node [.node [], .node [], .node []]

theorem usize_star4 : usize star4 = 4 := by decide +kernel

theorem lvR_star4 : lvR star4 = 3 := by decide +kernel

theorem lvR_bgMax4 : lvR (BGMaximizerAll.bgMax 4) = 2 := by
  unfold BGMaximizerAll.bgMax; decide +kernel

/-- The star on four vertices is not a maximizer. -/
theorem star4_not_max : ¬ IsBGMax 4 (real star4) := by
  intro h
  have hsz := (BGMaximizerAll.bg_maximizer_all 4 (by norm_num)).1
  have hcard : Fintype.card (AVert (Step3.realize (dtRealize star4))) = 4 := by
    rw [card_verts_realize _ (by rw [usize_star4]; omega), usize_star4]
  rcases (bg_maximizers_mathlib 4 (by norm_num) (real star4) (real_isTree _ (by rw [usize_star4]; omega)) hcard).mp h
    with ψ | ⟨h21, _⟩
  · have hr := (rerootRel_iff_uiso _ _).mpr
      ((uiso_iff_aGraph star4 (BGMaximizerAll.bgMax 4) (by rw [usize_star4]; omega) (by omega)).mpr ψ)
    have := lvR_rel hr
    rw [lvR_star4, lvR_bgMax4] at this
    omega
  · omega

/-- Control `BGUniqueNegEveryTree` is false: not every tree on four vertices is a maximizer. -/
theorem not_negEveryTree :
    ¬ ∀ (n : ℕ) (_ : 4 ≤ n) (_ : n ≠ 21)
      {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (_ : G.IsTree) (_ : Fintype.card V = n),
      ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = n →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)) := by
  classical
  intro h
  have hcard : Fintype.card (AVert (Step3.realize (dtRealize star4))) = 4 := by
    rw [card_verts_realize _ (by rw [usize_star4]; omega), usize_star4]
  apply star4_not_max
  intro X _ H hH hX
  have := h 4 (by norm_num) (by norm_num) (real star4) (real_isTree _ (by rw [usize_star4]; omega)) hcard X H hH hX
  rwa [ratio_eq, ratio_eq] at this

end BGUnique
end R3Cert
