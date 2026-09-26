/-
  R4-R7 campaign, PHASE 7: the structural DECODE (tree->hub, Pass 5).

  The deep-perm anchor (`deepPerm_Aobj`) reduced the tree->hub composition to a purely STRUCTURAL
  decode: every defect-zero tree is deep-perm equivalent to a hub-backbone,

      strDefect t = 0  ->  exists s : List Hub, DeepPerm t (backboneU s).

  With that, `tree_to_hub_of_progress_decode` yields the literal `tree_to_hub`, leaving only
  `StraightProgress` (the Kelmans-straighten move existence).

  This file builds the decode from recognizer inverses (`isCherry_eq`, `isArm_eq`) and a
  piece-list regrouping permutation.

  What is PROVED here (no `sorry`, axiom-clean):
    * `isCherry_eq`   -- a recognized cherry IS `cherryU`;
    * `isArm_eq`      -- a recognized arm IS some `armU j`;
    * `pieces_perm`   -- an all-piece child list permutes to arms-block ++ cherry-block.

  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R7Straighten
import R3Cert.R47R7DeepPerm

namespace R3Cert
namespace Step3

open RTree

/-! ### Recognizer inverses -/

theorem isLeaf_eq {K : UTree} (h : isLeaf K = true) : K = UTree.node [] := by
  cases K with
  | node cs =>
    cases cs with
    | nil => rfl
    | cons a b => rw [isLeaf] at h; exact absurd h (by simp)

theorem isCherry_eq {K : UTree} (h : isCherry K = true) : K = cherryU := by
  cases K with
  | node cs =>
    cases cs with
    | nil => rw [isCherry] at h; exact absurd h (by simp)
    | cons c rest =>
      cases rest with
      | nil =>
        rw [isCherry] at h
        rw [isLeaf_eq h]; rfl
      | cons c2 rest2 => rw [isCherry] at h; exact absurd h (by simp)

theorem all_cherry_replicate {cs : List UTree} (h : cs.all isCherry = true) :
    cs = List.replicate cs.length cherryU := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hrest⟩ := h
    rw [isCherry_eq hc, List.length_cons, List.replicate_succ]
    congr 1
    exact ih hrest

theorem isArm_eq {cs : List UTree} (h : isArm (UTree.node cs) = true) :
    UTree.node cs = armU cs.length := by
  rw [isArm] at h
  rw [armU]
  congr 1
  exact all_cherry_replicate h

theorem isArm_exists {K : UTree} (h : isArm K = true) : ∃ j, K = armU j := by
  cases K with
  | node cs => exact ⟨cs.length, isArm_eq h⟩

/-! ### An all-piece child list regroups (up to permutation) into arms ++ cherries -/

theorem pieces_perm {cs : List UTree} (h : ∀ x ∈ cs, isPiece x = true) :
    ∃ (arms : List ℕ) (c : ℕ), cs.Perm (arms.map armU ++ List.replicate c cherryU) := by
  induction cs with
  | nil => exact ⟨[], 0, by simp⟩
  | cons K rest ih =>
    obtain ⟨arms, c, hperm⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hK : isPiece K = true := h K (by simp)
    rw [isPiece, Bool.or_eq_true] at hK
    rcases hK with harm | hcher
    · obtain ⟨j, rfl⟩ := isArm_exists harm
      refine ⟨j :: arms, c, ?_⟩
      rw [List.map_cons, List.cons_append]
      exact hperm.cons _
    · obtain rfl := isCherry_eq hcher
      refine ⟨arms, c + 1, ?_⟩
      have h1 : (cherryU :: rest).Perm (cherryU :: (arms.map armU ++ List.replicate c cherryU)) :=
        hperm.cons _
      have h2 : (cherryU :: (arms.map armU ++ List.replicate c cherryU)).Perm
          (arms.map armU ++ cherryU :: List.replicate c cherryU) :=
        (List.perm_middle (l₁ := arms.map armU) (a := cherryU)
          (l₂ := List.replicate c cherryU)).symm
      rw [List.replicate_succ]
      exact h1.trans h2

/-! ### `npCount` decompositions -/

theorem npCount_zero_pieces {cs : List UTree} (h : npCount cs = 0) :
    ∀ x ∈ cs, isPiece x = true := by
  induction cs with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons K rest ih =>
    rw [npCount] at h
    have hpk : isPiece K = true ∧ npCount rest = 0 := by
      by_cases hp : isPiece K = true
      · rw [if_pos hp] at h; exact ⟨hp, by omega⟩
      · rw [if_neg hp] at h; exact absurd h (by omega)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hpk.1
    · exact ih hpk.2 x hx'

theorem npCount_one_decomp {cs : List UTree} (h : npCount cs = 1) :
    ∃ (pre : List UTree) (d : UTree) (post : List UTree),
      cs = pre ++ d :: post ∧ isPiece d = false ∧ npCount pre = 0 ∧ npCount post = 0 := by
  induction cs with
  | nil => rw [npCount] at h; exact absurd h (by omega)
  | cons K rest ih =>
    rw [npCount] at h
    by_cases hp : isPiece K = true
    · rw [if_pos hp] at h
      obtain ⟨pre, d, post, hcs, hd, hpre, hpost⟩ := ih (by omega)
      exact ⟨K :: pre, d, post, by rw [hcs, List.cons_append], hd,
        by rw [npCount, if_pos hp]; omega, hpost⟩
    · rw [if_neg hp] at h
      rw [Bool.not_eq_true] at hp
      exact ⟨[], K, rest, rfl, hp, by rw [npCount], by omega⟩

/-- Deep-perm reflexivity across an append with one replaced middle element. -/
theorem forall2_refl_cons_refl (pre post : List UTree) {d d' : UTree} (hdd : DeepPerm d d') :
    List.Forall₂ DeepPerm (pre ++ d :: post) (pre ++ d' :: post) := by
  induction pre with
  | nil => exact List.Forall₂.cons hdd (deepPerm_refl_list post)
  | cons a rest ih => exact List.Forall₂.cons (deepPerm_refl a) ih

/-! ### Two small structural facts -/

/-- A tree deep-perm to a leaf is a leaf. -/
theorem deepPerm_children_nil {t : UTree} (h : DeepPerm t (UTree.node [])) : t = UTree.node [] := by
  cases h with
  | @mk cs ds es hcong hperm =>
    have hds : ds = [] := List.perm_nil.mp hperm
    subst hds
    cases hcong
    rfl

/-- The defect sum of a piece-flanked single non-piece is that non-piece's defect. -/
theorem npDefectSum_decomp {pre : List UTree} {d : UTree} {post : List UTree}
    (hpre : npCount pre = 0) (hpost : npCount post = 0) (hd : isPiece d = false) :
    npDefectSum (pre ++ d :: post) = strDefect d := by
  rw [npDefectSum_append, npDefectSum_pieces (npCount_zero_pieces hpre),
    npDefectSum, npDefectSum_pieces (npCount_zero_pieces hpost)]
  simp [hd]

/-! ### The decode -/

/-- **The structural decode.**  Every defect-zero tree is deep-perm equivalent to a hub-backbone.
    Fuel-bounded induction on `sizeOf`: a defect-zero node has all-piece children (single hub) or
    all-piece children plus one defect-zero non-piece tail (recurse), regrouped into
    `backboneU` order by a permutation. -/
theorem strDefect_decode : ∀ (n : ℕ) (t : UTree), sizeOf t ≤ n → strDefect t = 0 →
    ∃ s : List Hub, DeepPerm t (backboneU s) := by
  intro n
  induction n with
  | zero => intro t hsz _; exact absurd hsz (by cases t; simp)
  | succ n ih =>
    intro t h_sz h0
    cases t with
    | node cs =>
      obtain ⟨hle, hds⟩ : npCount cs ≤ 1 ∧ npDefectSum cs = 0 := by rw [strDefect] at h0; omega
      by_cases hz : npCount cs = 0
      · obtain ⟨arms, c, hperm⟩ := pieces_perm (npCount_zero_pieces hz)
        refine ⟨[(arms, c)], ?_⟩
        have hb : backboneU [(arms, c)]
            = UTree.node (arms.map armU ++ List.replicate c cherryU) := by
          rw [backboneU_eq]; simp [tailU]
        rw [hb]
        exact DeepPerm.mk (deepPerm_refl_list cs) hperm
      · have h1 : npCount cs = 1 := by omega
        obtain ⟨pre, d, post, hcs, hd, hpre, hpost⟩ := npCount_one_decomp h1
        have hstrd : strDefect d = 0 := by
          rw [hcs, npDefectSum_decomp hpre hpost hd] at hds; exact hds
        have hsz_d : sizeOf d ≤ n := by
          have hmem : d ∈ cs := by rw [hcs]; simp
          have hlt : sizeOf d < sizeOf cs := List.sizeOf_lt_of_mem hmem
          simp only [UTree.node.sizeOf_spec] at h_sz
          omega
        obtain ⟨s', hdp⟩ := ih d hsz_d hstrd
        have hs' : s' ≠ [] := by
          rintro rfl
          have hdl : d = UTree.node [] := deepPerm_children_nil hdp
          rw [hdl] at hd; simp [isPiece, isArm] at hd
        have hpiecesall : ∀ x ∈ pre ++ post, isPiece x = true := by
          intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact npCount_zero_pieces hpre x hh
          · exact npCount_zero_pieces hpost x hh
        obtain ⟨arms, c, hpp⟩ := pieces_perm hpiecesall
        refine ⟨(arms, c) :: s', ?_⟩
        have htail : tailU s' = [backboneU s'] := by
          cases s' with
          | nil => exact absurd rfl hs'
          | cons a t => rfl
        have hb : backboneU ((arms, c) :: s')
            = UTree.node (arms.map armU ++ List.replicate c cherryU ++ [backboneU s']) := by
          rw [backboneU_eq, htail]
        rw [hcs, hb]
        refine DeepPerm.mk (ds := pre ++ backboneU s' :: post) ?_ ?_
        · exact forall2_refl_cons_refl pre post hdp
        · have hmove : (pre ++ backboneU s' :: post).Perm ((pre ++ post) ++ [backboneU s']) := by
            have h1' : (backboneU s' :: post).Perm (post ++ [backboneU s']) := by
              simpa using (List.perm_append_comm (l₁ := [backboneU s']) (l₂ := post))
            have h2 := h1'.append_left pre
            rw [List.append_assoc]; exact h2
          exact hmove.trans (hpp.append_right [backboneU s'])

/-- **`tree_to_hub`, resting on `StraightProgress` alone.**  The decode discharges the second
    obligation of `tree_to_hub_of_progress_decode`, so the literal tree->hub reduction now depends
    only on the Kelmans-straighten move existence `StraightProgress`. -/
theorem tree_to_hub_of_progress (hprog : StraightProgress) :
    ∀ t : UTree, ∃ s : List Hub, Aobj t ≤ Aobj (backboneU s) :=
  tree_to_hub_of_progress_decode hprog (fun t h => strDefect_decode (sizeOf t) t le_rfl h)

end Step3
end R3Cert
