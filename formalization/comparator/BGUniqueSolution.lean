/-
  The Comparator SOLUTION for uniqueness: the same statements as `BGUniqueChallenge.lean`, proved.
-/
import BGUnique.Mathlib

open R3Cert R3Cert.BGUnique R3Cert.AllUnique R3Cert.Step3 R3Cert.BGStatement

namespace BGUniqueComparator

theorem isBGMax_of {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n →
        (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ))) :
    IsBGMax n G := by
  intro X _ H hH hX
  classical
  have h := hmax X H hH hX
  rwa [← lapRatio_eq, ← lapRatio_eq] at h

theorem unique (n : ℕ) (h4 : 4 ≤ n) (h21 : n ≠ 21)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Type} [Fintype W] [DecidableEq W] (G' : SimpleGraph W) [DecidableRel G'.Adj]
    (hG : G.IsTree) (hV : Fintype.card V = n) (hG' : G'.IsTree) (hW : Fintype.card W = n)
    (hmax : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n →
        (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G.lapMatrix ℝ).permanent / (∏ v, (G.degree v : ℝ)))
    (hmax' : ∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
      H.IsTree → Fintype.card X = n →
        (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G'.lapMatrix ℝ).permanent / (∏ v, (G'.degree v : ℝ))) :
    Nonempty (G ≃g G') := by
  obtain ⟨φ⟩ := bg_maximizer_unique_mathlib n h4 h21 G hG hV (isBGMax_of G hmax)
  obtain ⟨ψ⟩ := bg_maximizer_unique_mathlib n h4 h21 G' hG' hW (isBGMax_of G' hmax')
  exact ⟨φ.trans ψ.symm⟩

/-- A copy of a graph on `Fin m`, with the isomorphism. -/
theorem copy_fin {V : Type} [Fintype V] (G : SimpleGraph V) {m : ℕ} (hm : Fintype.card V = m) :
    ∃ G₀ : SimpleGraph (Fin m), Nonempty (G₀ ≃g G) :=
  ⟨G.comap (Fintype.equivFinOfCardEq hm).symm,
    ⟨SimpleGraph.Iso.comap (Fintype.equivFinOfCardEq hm).symm G⟩⟩

theorem two_at_21 :
    ∃ (G₁ G₂ : SimpleGraph (Fin 21)) (_ : DecidableRel G₁.Adj) (_ : DecidableRel G₂.Adj),
      G₁.IsTree ∧ G₂.IsTree ∧ IsEmpty (G₁ ≃g G₂) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) ≤ (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ))) ∧
      (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) = (G₂.lapMatrix ℝ).permanent / (∏ v, (G₂.degree v : ℝ)) ∧
      (∀ (X : Type) [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj],
        H.IsTree → Fintype.card X = 21 →
          (H.lapMatrix ℝ).permanent / (∏ v, (H.degree v : ℝ)) = (G₁.lapMatrix ℝ).permanent / (∏ v, (G₁.degree v : ℝ)) →
          Nonempty (H ≃g G₁) ∨ Nonempty (H ≃g G₂)) := by
  classical
  obtain ⟨hA, hB, hne⟩ := bg_maximizers_21_mathlib
  have hsz := (BGMaximizerAll.bg_maximizer_all 21 (by norm_num)).1
  obtain ⟨G₁, ⟨e₁⟩⟩ := copy_fin (real (BGMaximizerAll.bgMax 21)) (by rw [card_verts_realize _ (by omega), hsz])
  obtain ⟨G₂, ⟨e₂⟩⟩ := copy_fin (real S21) (by rw [card_verts_realize _ (by rw [usize_S21]; omega), usize_S21])
  have h1 : IsBGMax 21 G₁ := (isBGMax_iso 21 G₁ _ e₁).mpr hA
  have h2 : IsBGMax 21 G₂ := (isBGMax_iso 21 G₂ _ e₂).mpr hB
  have t1 : G₁.IsTree := e₁.symm.isTree_iff.mp (real_isTree _ (by omega))
  have t2 : G₂.IsTree := e₂.symm.isTree_iff.mp (real_isTree _ (by rw [usize_S21]; omega))
  refine ⟨G₁, G₂, inferInstance, inferInstance, t1, t2, ⟨fun ψ => hne.false (e₁.symm.trans (ψ.trans e₂))⟩, ?_, ?_, ?_⟩
  · intro X _ _ H _ hH hX
    have h := h1 X H hH hX
    rwa [lapRatio_eq, lapRatio_eq] at h
  · have a := h1 _ G₂ t2 (Fintype.card_fin 21)
    have b := h2 _ G₁ t1 (Fintype.card_fin 21)
    rw [← lapRatio_eq, ← lapRatio_eq]; exact le_antisymm b a
  · intro X _ _ H _ hH hX heq
    have heq' : lapRatio H = lapRatio G₁ := by rw [lapRatio_eq, lapRatio_eq]; exact heq
    have hH' : IsBGMax 21 H := by
      intro Y _ K hK hY
      rw [heq']; exact h1 Y K hK hY
    rcases (bg_maximizers_mathlib 21 (by norm_num) H hH hX).mp hH' with ψ | ⟨_, ψ⟩
    · obtain ⟨ψ⟩ := ψ; exact Or.inl ⟨ψ.trans e₁.symm⟩
    · obtain ⟨ψ⟩ := ψ; exact Or.inr ⟨ψ.trans e₂.symm⟩

end BGUniqueComparator
