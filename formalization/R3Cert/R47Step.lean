/-
  R4-R7 campaign, PHASE 2b: the Step relation -- the unified topped-up merge.

  Per P2B_MERGE_DESIGN.md, the rewrite layer's single hub-merge constructor is the
  TOPPED-UP MERGE: for adjacent hubs `a` (arms `armsA`, load `cA`) and `b` (arms `armsB`,
  load `cb <= 5`) where `b` carries at least `k = 5 - cb` load-5 arms, downgrade `k` of
  `b`'s load-5 arms to load 4 (the borrows, fused into the move), raise `b`'s load to 5,
  move all of `b`'s other neighbours (remaining arms + backbone tail) to `a`, and leave
  `b` as a canonical load-5 arm of `a`.  Donor load 5 (`k = 0`) recovers the plain
  Kelmans merge.  The `tail` constructor lets the merge fire anywhere along the backbone.

  Machine-checked here (the P2b deliverables):
  * `Step.balanced`   -- NO DEBRIS: the balanced {4,5}-arm / load-<=5 family is invariant
    (the residue is `k` load-4 arms + one load-5 arm, all inside the family);
  * `Step.length_lt`  -- the measure: each step removes exactly one hub;
  * `step_wf`         -- TERMINATION: the step-inverse relation is well-founded;
  * `merge_applicable`-- NO STUCK STATES at the head pair: a count witness
    (`5 - cb <= armsB.count 5`) always yields a merge;
  * `exists_normalForm` -- every state rewrites to a Step-normal form;
  * `single_hub_normal` -- a single hub is normal (the sink shape);
  * `Aobj_mono_chain` -- CONDITIONAL A-dominance along rewrite chains, given the
    per-step monotonicity (the P4/P5 certificate layer: the 36-cell topped-up table).

  The per-step monotonicity `Step a b -> Aobj (backboneU a) <= Aobj (backboneU b)` is NOT
  asserted here -- it is the named hypothesis the P4/P5 discharges must supply (exact
  bilinear identity + corner certificates at cap 3/16).  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47BackboneAmp

namespace R3Cert
namespace Step3

open RTree

/-! ### The balanced family -/

/-- Arms all carry load 4 or 5. -/
def BalancedArms (arms : List ℕ) : Prop := ∀ j ∈ arms, j = 4 ∨ j = 5

/-- The balanced hub family: every hub's arms carry load 4 or 5 and its own cherry
    load is at most 5. -/
def Balanced (s : List Hub) : Prop := ∀ h ∈ s, BalancedArms h.1 ∧ h.2 ≤ 5

/-! ### The Step relation -/

/-- **The unified topped-up merge** as an arithmetic move on hub states.  The `merge`
    constructor absorbs the second hub into the first: `k = 5 - cb` of its load-5 arms
    are downgraded to load 4 (the fused borrows), its load is topped up to 5 and it
    becomes a load-5 arm of the absorber, and its remaining arms and backbone tail move
    to the absorber.  The `tail` constructor localizes the move anywhere on the
    backbone. -/
inductive Step : List Hub → List Hub → Prop
  | merge {armsA : List ℕ} {cA : ℕ} {armsB others : List ℕ} {cb : ℕ} {rest : List Hub}
      (hcb : cb ≤ 5)
      (hsplit : armsB.Perm (List.replicate (5 - cb) 5 ++ others)) :
      Step ((armsA, cA) :: (armsB, cb) :: rest)
        ((armsA ++ List.replicate (5 - cb) 4 ++ others ++ [5], cA) :: rest)
  | tail {h : Hub} {s s' : List Hub} : Step s s' → Step (h :: s) (h :: s')

/-! ### No debris: the balanced family is invariant -/

/-- **Preservation.** The topped-up merge leaves the balanced family: the residue is
    load-4 arms plus one load-5 arm, and hub loads are untouched. -/
theorem Step.balanced {s s' : List Hub} (hst : Step s s') :
    Balanced s → Balanced s' := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit =>
    intro hb h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · refine ⟨?_, (hb (armsA, cA) (by simp)).2⟩
      intro j hj
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hj
      rcases hj with ((hj | ⟨-, rfl⟩) | hj) | rfl
      · exact (hb (armsA, cA) (by simp)).1 j hj
      · exact Or.inl rfl
      · exact (hb (armsB, cb) (by simp)).1 j
          (hsplit.mem_iff.mpr (List.mem_append.mpr (Or.inr hj)))
      · exact Or.inr rfl
    · exact hb h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
  | @tail hd s s' hst ih =>
    intro hb h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact hb _ (by simp)
    · exact ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _ hh

/-! ### The measure and termination -/

/-- Each step removes exactly one hub. -/
theorem Step.length_lt {s s' : List Hub} (h : Step s s') : s'.length < s.length := by
  induction h with
  | merge hcb hsplit => simp only [List.length_cons]; omega
  | tail hst ih => simp only [List.length_cons]; omega

/-- **Termination of the merge layer**: the step-inverse relation is well-founded --
    there are no infinite rewrite chains. -/
theorem step_wf : WellFounded (fun s' s : List Hub => Step s s') :=
  (InvImage.wf List.length wellFounded_lt).mono fun _ _ h => Step.length_lt h

/-! ### No stuck states at the head pair -/

/-- **Applicability.** Any adjacent hub pair whose donor carries at least `5 - cb`
    load-5 arms admits a topped-up merge -- the count witness is enough. -/
theorem merge_applicable {armsA : List ℕ} {cA : ℕ} {armsB : List ℕ} {cb : ℕ}
    {rest : List Hub} (hcb : cb ≤ 5) (hcount : 5 - cb ≤ armsB.count 5) :
    ∃ s', Step ((armsA, cA) :: (armsB, cb) :: rest) s' := by
  have hsub : List.Subperm (List.replicate (5 - cb) 5) armsB := by
    rw [List.subperm_iff_count]
    intro a
    by_cases ha : a = 5
    · subst ha; simpa using hcount
    · simp [List.count_replicate, Ne.symm ha]
  obtain ⟨l, hlp, hls⟩ := hsub
  obtain ⟨others, hoth⟩ := hls.exists_perm_append
  exact ⟨_, Step.merge hcb (hoth.trans (hlp.append_right others))⟩

/-! ### Normal forms -/

/-- The empty state is stuck (vacuously normal). -/
theorem step_nil {u : List Hub} (h : Step [] u) : False := by cases h

/-- A single hub is a normal form -- the sink shape of the merge layer. -/
theorem single_hub_normal (h : Hub) (u : List Hub) : ¬ Step [h] u := by
  intro hu
  cases hu with
  | tail hst => exact step_nil hst

/-- **Normal-form existence**: well-foundedness rewrites every state to a normal form. -/
theorem exists_normalForm (s : List Hub) :
    ∃ t, Relation.ReflTransGen Step s t ∧ ∀ u, ¬ Step t u := by
  refine step_wf.induction
    (C := fun s => ∃ t, Relation.ReflTransGen Step s t ∧ ∀ u, ¬ Step t u) s ?_
  intro x ih
  by_cases hx : ∃ y, Step x y
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨t, hyt, hnf⟩ := ih y hy
    exact ⟨t, Relation.ReflTransGen.head hy hyt, hnf⟩
  · exact ⟨x, Relation.ReflTransGen.refl, fun u hu => hx ⟨u, hu⟩⟩

/-! ### Conditional A-dominance along chains -/

/-- **The conditional assembly seam**: given per-step monotonicity of the objective
    (the P4/P5 certificate layer), the objective is monotone along every rewrite
    chain.  With `exists_normalForm` this pushes any state's objective up to a normal
    form's. -/
theorem Aobj_mono_chain
    (hmono : ∀ ⦃a b : List Hub⦄, Step a b → Aobj (backboneU a) ≤ Aobj (backboneU b))
    {s t : List Hub} (h : Relation.ReflTransGen Step s t) :
    Aobj (backboneU s) ≤ Aobj (backboneU t) := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (hmono hbc)

end Step3
end R3Cert
