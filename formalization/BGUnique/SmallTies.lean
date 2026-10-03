import Mathlib
import BGUnique.StrictTableX
import BGUnique.RerootEquiv
import R3Cert.BGSpiderTableAll
import BGUnique.SmallSweep.All

namespace R3Cert
namespace SpiderStrict

open R3Cert.RTree R3Cert.Step3 BGSpiderOpt BGSpiderRule BGSpiderTable RerootEquiv

/-- Closure of a predicate under the spider exceptions of the check. -/
theorem pred_of_checkX (n : ℕ) (hn : 2 ≤ n) (hcN : checkN n = true)
    (exB : List (ℕ × ℕ)) (ex1 : List Child) (ex2 : List (Child × Child))
    (hc : checkX n exB ex1 ex2 = true) (P : UTree → Prop)
    (hP : ∀ t t', RerootRel t t' → P t' → P t)
    (hB : ∀ p ∈ exB, P (spiderU (canonB n p))) (h1 : ∀ c ∈ ex1, P (spiderU [c]))
    (h2 : ∀ q ∈ ex2, P (spiderU [q.1, q.2]))
    (l : List Child) (hl : nv l = n) (hge : F (tab n) ≤ F l) : P (spiderU l) := by
  rcases spider_cases_of_checkX n hn hcN exB ex1 ex2 hc l hl hge with ⟨p, hp, hperm⟩ | ⟨c, hc1, rfl⟩ |
      ⟨q, hq, rfl⟩
  · exact hP _ _ (spiderU_perm hperm) (hB p hp)
  · exact h1 c hc1
  · exact h2 q hq

/-- The maximizer statement for one size: equal to the table spider up to rerooting, or (only at 21)
    to the all-cherry spider. -/
def TieGoal (n : ℕ) (t : UTree) : Prop :=
  RerootRel t (spiderU (tab n)) ∨ (n = 21 ∧ RerootRel t (spiderU (List.replicate 10 Child.cherry)))

theorem tieGoal_closed (n : ℕ) : ∀ t t', RerootRel t t' → TieGoal n t' → TieGoal n t := by
  rintro t t' h (h' | ⟨e, h'⟩)
  · exact Or.inl (h.trans h')
  · exact Or.inr ⟨e, h.trans h'⟩

theorem tieGoal_tab (n : ℕ) {l : List Child} (h : l = tab n) : TieGoal n (spiderU l) :=
  Or.inl (by rw [h]; exact Relation.ReflTransGen.refl)

theorem tie_7 (l : List Child) (hl : nv l = 7) (hge : F (tab 7) ≤ F l) : TieGoal 7 (spiderU l) := by
  have htab : tab 7 = List.replicate 3 Child.cherry := by decide
  refine pred_of_checkX 7 (by norm_num) (checkN_all 7 (by norm_num) (by norm_num)) [(3, 0)] []
    [(Child.arm 0, Child.arm 2), (Child.arm 2, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 7) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 7 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 2
    · left; rw [htab]; exact leafArm 2

theorem tie_9 (l : List Child) (hl : nv l = 9) (hge : F (tab 9) ≤ F l) : TieGoal 9 (spiderU l) := by
  have htab : tab 9 = List.replicate 4 Child.cherry := by decide
  refine pred_of_checkX 9 (by norm_num) (checkN_all 9 (by norm_num) (by norm_num)) [(4, 0)] []
    [(Child.arm 0, Child.arm 3), (Child.arm 3, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 9) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 9 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 3
    · left; rw [htab]; exact leafArm 3

theorem tie_11 (l : List Child) (hl : nv l = 11) (hge : F (tab 11) ≤ F l) : TieGoal 11 (spiderU l) := by
  have htab : tab 11 = List.replicate 5 Child.cherry := by decide
  refine pred_of_checkX 11 (by norm_num) (checkN_all 11 (by norm_num) (by norm_num)) [(5, 0)] []
    [(Child.arm 0, Child.arm 4), (Child.arm 4, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 11) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 11 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 4
    · left; rw [htab]; exact leafArm 4

theorem tie_13 (l : List Child) (hl : nv l = 13) (hge : F (tab 13) ≤ F l) : TieGoal 13 (spiderU l) := by
  have htab : tab 13 = List.replicate 6 Child.cherry := by decide
  refine pred_of_checkX 13 (by norm_num) (checkN_all 13 (by norm_num) (by norm_num)) [(6, 0)] []
    [(Child.arm 0, Child.arm 5), (Child.arm 5, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 13) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 13 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 5
    · left; rw [htab]; exact leafArm 5

theorem tie_15 (l : List Child) (hl : nv l = 15) (hge : F (tab 15) ≤ F l) : TieGoal 15 (spiderU l) := by
  have htab : tab 15 = List.replicate 7 Child.cherry := by decide
  refine pred_of_checkX 15 (by norm_num) (checkN_all 15 (by norm_num) (by norm_num)) [(7, 0)] []
    [(Child.arm 0, Child.arm 6), (Child.arm 6, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 15) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 15 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 6
    · left; rw [htab]; exact leafArm 6

theorem tie_17 (l : List Child) (hl : nv l = 17) (hge : F (tab 17) ≤ F l) : TieGoal 17 (spiderU l) := by
  have htab : tab 17 = List.replicate 8 Child.cherry := by decide
  refine pred_of_checkX 17 (by norm_num) (checkN_all 17 (by norm_num) (by norm_num)) [(8, 0)] []
    [(Child.arm 0, Child.arm 7), (Child.arm 7, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 17) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 17 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 7
    · left; rw [htab]; exact leafArm 7

theorem tie_19 (l : List Child) (hl : nv l = 19) (hge : F (tab 19) ≤ F l) : TieGoal 19 (spiderU l) := by
  have htab : tab 19 = List.replicate 9 Child.cherry := by decide
  refine pred_of_checkX 19 (by norm_num) (checkN_all 19 (by norm_num) (by norm_num)) [(9, 0)] []
    [(Child.arm 0, Child.arm 8), (Child.arm 8, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 19) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 19 (by rw [htab]; decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact leafArm' 8
    · left; rw [htab]; exact leafArm 8

theorem tie_8 (l : List Child) (hl : nv l = 8) (hge : F (tab 8) ≤ F l) : TieGoal 8 (spiderU l) := by
  have htab : tab 8 = List.replicate 2 Child.cherry ++ [Child.arm 1] := by decide
  refine pred_of_checkX 8 (by norm_num) (checkN_all 8 (by norm_num) (by norm_num)) [(2, 1)] []
    [(Child.cherry, Child.arm 2), (Child.arm 2, Child.cherry)] (by decide +kernel) _ (tieGoal_closed 8) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp
    exact tieGoal_tab 8 (by decide)
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · left; rw [htab]; exact swap 1 2
    · left; rw [htab]; exact (spiderU_perm (List.Perm.swap _ _ [])).trans (swap 1 2)

theorem tie_12 (l : List Child) (hl : nv l = 12) (hge : F (tab 12) ≤ F l) : TieGoal 12 (spiderU l) := by
  have htab : tab 12 = List.replicate 2 Child.cherry ++ [Child.arm 3] := by decide
  refine pred_of_checkX 12 (by norm_num) (checkN_all 12 (by norm_num) (by norm_num)) [(2, 1), (3, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 12) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 12 (by decide)
    · left
      rw [show canonB 12 (3, 1) = List.replicate 3 Child.cherry ++ [Child.arm 2] by decide, htab]
      exact swap 3 2
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_16 (l : List Child) (hl : nv l = 16) (hge : F (tab 16) ≤ F l) : TieGoal 16 (spiderU l) := by
  have htab : tab 16 = List.replicate 3 Child.cherry ++ [Child.arm 4] := by decide
  refine pred_of_checkX 16 (by norm_num) (checkN_all 16 (by norm_num) (by norm_num)) [(3, 1), (4, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 16) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 16 (by decide)
    · left
      rw [show canonB 16 (4, 1) = List.replicate 4 Child.cherry ++ [Child.arm 3] by decide, htab]
      exact swap 4 3
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_20 (l : List Child) (hl : nv l = 20) (hge : F (tab 20) ≤ F l) : TieGoal 20 (spiderU l) := by
  have htab : tab 20 = List.replicate 4 Child.cherry ++ [Child.arm 5] := by decide
  refine pred_of_checkX 20 (by norm_num) (checkN_all 20 (by norm_num) (by norm_num)) [(4, 1), (5, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 20) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 20 (by decide)
    · left
      rw [show canonB 20 (5, 1) = List.replicate 5 Child.cherry ++ [Child.arm 4] by decide, htab]
      exact swap 5 4
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_24 (l : List Child) (hl : nv l = 24) (hge : F (tab 24) ≤ F l) : TieGoal 24 (spiderU l) := by
  have htab : tab 24 = List.replicate 5 Child.cherry ++ [Child.arm 6] := by decide
  refine pred_of_checkX 24 (by norm_num) (checkN_all 24 (by norm_num) (by norm_num)) [(5, 1), (6, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 24) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 24 (by decide)
    · left
      rw [show canonB 24 (6, 1) = List.replicate 6 Child.cherry ++ [Child.arm 5] by decide, htab]
      exact swap 6 5
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_28 (l : List Child) (hl : nv l = 28) (hge : F (tab 28) ≤ F l) : TieGoal 28 (spiderU l) := by
  have htab : tab 28 = List.replicate 6 Child.cherry ++ [Child.arm 7] := by decide
  refine pred_of_checkX 28 (by norm_num) (checkN_all 28 (by norm_num) (by norm_num)) [(6, 1), (7, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 28) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 28 (by decide)
    · left
      rw [show canonB 28 (7, 1) = List.replicate 7 Child.cherry ++ [Child.arm 6] by decide, htab]
      exact swap 7 6
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_32 (l : List Child) (hl : nv l = 32) (hge : F (tab 32) ≤ F l) : TieGoal 32 (spiderU l) := by
  have htab : tab 32 = List.replicate 7 Child.cherry ++ [Child.arm 8] := by decide
  refine pred_of_checkX 32 (by norm_num) (checkN_all 32 (by norm_num) (by norm_num)) [(7, 1), (8, 1)] [] []
    (by decide +kernel) _ (tieGoal_closed 32) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 32 (by decide)
    · left
      rw [show canonB 32 (8, 1) = List.replicate 8 Child.cherry ++ [Child.arm 7] by decide, htab]
      exact swap 8 7
  · intro c hc; simp at hc
  · intro q hq; simp at hq

theorem tie_21 (l : List Child) (hl : nv l = 21) (hge : F (tab 21) ≤ F l) : TieGoal 21 (spiderU l) := by
  refine pred_of_checkX 21 (by norm_num) (checkN_all 21 (by norm_num) (by norm_num)) [(3, 2), (10, 0)] []
    [(Child.arm 0, Child.arm 9), (Child.arm 9, Child.arm 0)] (by decide +kernel) _ (tieGoal_closed 21) ?_ ?_ ?_ l hl hge
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact tieGoal_tab 21 (by decide)
    · right; refine ⟨rfl, ?_⟩
      rw [show canonB 21 (10, 0) = List.replicate 10 Child.cherry by decide]
      exact Relation.ReflTransGen.refl
  · intro c hc; simp at hc
  · intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr ⟨rfl, leafArm' 9⟩
    · exact Or.inr ⟨rfl, leafArm 9⟩

/-- **Spider-family maximizers, `7 ≤ n ≤ 149`.**  A spider reaching the table value is the table spider
    up to rerooting, or (only at `n = 21`) the all-cherry spider up to rerooting. -/
theorem spider_small_tie (n : ℕ) (h7 : 7 ≤ n) (h149 : n ≤ 149) (l : List Child) (hl : nv l = n)
    (hge : F (tab n) ≤ F l) : TieGoal n (spiderU l) := by
  by_cases hf : n ∈ failSmall
  · simp only [failSmall, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tie_7 l hl hge
    · exact tie_8 l hl hge
    · exact tie_9 l hl hge
    · exact tie_11 l hl hge
    · exact tie_12 l hl hge
    · exact tie_13 l hl hge
    · exact tie_15 l hl hge
    · exact tie_16 l hl hge
    · exact tie_17 l hl hge
    · exact tie_19 l hl hge
    · exact tie_20 l hl hge
    · exact tie_21 l hl hge
    · exact tie_24 l hl hge
    · exact tie_28 l hl hge
    · exact tie_32 l hl hge
  · left
    exact spiderU_perm (spider_unique_of_check n (by omega) (checkN_all n (by omega) (by omega))
      (checkNS_small n h7 h149 hf) l hl hge)

end SpiderStrict
end R3Cert
