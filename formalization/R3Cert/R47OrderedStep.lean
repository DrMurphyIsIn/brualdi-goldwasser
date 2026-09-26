/-
  R4-R7 campaign, PHASE 5e (part 3, first file): the ORDERED merge relation with BOTH
  directions -- the hubward merge and its anti-hubward MIRROR.

  Per P5_SEAM_DESIGN.md: the certified table needs the absorber's degree to dominate
  the donor's.  `OrderedStep` carries the side condition per merge, in BOTH roles:
  * `merge`    -- the absorber is the FIRST hub (P2b's surgery + the ordering);
  * `mergeRev` -- the absorber is the SECOND hub (the mirror surgery: the first hub's
    load tops up to 5 from its OWN arms and it lands as a load-5 arm of the second;
    validated exactly, 59/59 including monotonicity, same certificate table at the
    swapped instantiation);
  * `tail`     -- backbone localization.
  With both directions, EVERY adjacent hub pair admits an ordered merge (absorb into
  the larger; the mirror's ordering is STRICT so it stays valid at any backbone depth
  -- the donor carries the prefix's up-edge -- and hubward covers the equality case,
  so coverage is complete at all depths) -- the S5 ordering stops being a residual.

  This file lifts the P2b structural layer to OrderedStep:
  * `length_lt` (measure), `ordered_wf` (termination);
  * `balanced`/`capped` (family invariance, both directions);
  * `stateSize_eq` (FIXED-n: the mirror's bookkeeping is `1 + 2cA + 11k' = 9k' + 11`
    at `cA + k' = 5`, the same identity with roles renamed);
  * `exists_normalForm'` (every state reaches an OrderedStep-normal form).
  The hubward cases delegate inline to the P2b `Step` lemmas (same surgery).
  The monotonicity of both directions (via the Vee identities + rotation) is the next
  file.  Nothing here asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Capped

namespace R3Cert
namespace Step3

open RTree

/-! ### The ordered relation, both directions -/

/-- The ordered topped-up merge: hubward (`merge`, absorber first), anti-hubward
    (`mergeRev`, absorber second), localized by `tail`.  The ordering side conditions
    compare structural degrees in the encoding (arms + backbone edges). -/
inductive OrderedStep : List Hub → List Hub → Prop
  | merge {armsA : List ℕ} {cA : ℕ} {armsB others : List ℕ} {cb : ℕ} {rest : List Hub}
      (hcb : cb ≤ 5)
      (hsplit : armsB.Perm (List.replicate (5 - cb) 5 ++ others))
      (hord : armsB.length + (tailU rest).length ≤ armsA.length) :
      OrderedStep ((armsA, cA) :: (armsB, cb) :: rest)
        ((armsA ++ List.replicate (5 - cb) 4 ++ others ++ [5], cA) :: rest)
  | mergeRev {armsA othersA : List ℕ} {cA : ℕ} {armsB : List ℕ} {cb : ℕ}
      {rest : List Hub}
      (hcA : cA ≤ 5)
      (hsplit : armsA.Perm (List.replicate (5 - cA) 5 ++ othersA))
      (hord : armsA.length + 1 ≤ armsB.length + (tailU rest).length) :
      OrderedStep ((armsA, cA) :: (armsB, cb) :: rest)
        ((armsB ++ List.replicate (5 - cA) 4 ++ othersA ++ [5], cb) :: rest)
  | tail {h : Hub} {s s' : List Hub} :
      OrderedStep s s' → OrderedStep (h :: s) (h :: s')

/-! ### Measure and termination -/

theorem OrderedStep.length_lt {s s' : List Hub} (h : OrderedStep s s') :
    s'.length < s.length := by
  induction h with
  | merge hcb hsplit hord => simp only [List.length_cons]; omega
  | mergeRev hcA hsplit hord => simp only [List.length_cons]; omega
  | tail hst ih => simp only [List.length_cons]; omega

theorem orderedStep_wf : WellFounded (fun s' s : List Hub => OrderedStep s s') :=
  (InvImage.wf List.length wellFounded_lt).mono fun _ _ h => OrderedStep.length_lt h

/-! ### Family invariance, both directions -/

theorem OrderedStep.balanced {s s' : List Hub} (hst : OrderedStep s s') :
    Balanced s → Balanced s' := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit hord =>
    exact Step.balanced (Step.merge hcb hsplit)
  | @mergeRev armsA othersA cA armsB cb rest hcA hsplit hord =>
    intro hb h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · refine ⟨?_, (hb (armsB, cb) (by simp)).2⟩
      intro j hj
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hj
      rcases hj with ((hj | ⟨-, rfl⟩) | hj) | rfl
      · exact (hb (armsB, cb) (by simp)).1 j hj
      · exact Or.inl rfl
      · exact (hb (armsA, cA) (by simp)).1 j
          (hsplit.mem_iff.mpr (List.mem_append.mpr (Or.inr hj)))
      · exact Or.inr rfl
    · exact hb h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
  | @tail hd s s' hst ih =>
    intro hb h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact hb _ (by simp)
    · exact ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _ hh

theorem OrderedStep.capped {s s' : List Hub} (hst : OrderedStep s s') :
    Capped s → Capped s' := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit hord =>
    exact Step.capped (Step.merge hcb hsplit)
  | @mergeRev armsA othersA cA armsB cb rest hcA hsplit hord =>
    intro hc h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · have hB : 5 ≤ armsB.length := hc (armsB, cb) (by simp)
      simp only [List.length_append]
      omega
    · exact hc h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
  | @tail hd s s' hst ih =>
    intro hc h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact hc _ (by simp)
    · exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) _ hh

/-! ### Fixed-n, both directions -/

theorem OrderedStep.stateSize_eq {s s' : List Hub} (hst : OrderedStep s s') :
    stateSize s' = stateSize s := by
  induction hst with
  | @merge armsA cA armsB others cb rest hcb hsplit hord =>
    exact Step.stateSize_eq (Step.merge hcb hsplit)
  | @mergeRev armsA othersA cA armsB cb rest hcA hsplit hord =>
    have hlen := hsplit.length_eq
    have hsum := hsplit.sum_eq
    simp only [List.length_append, List.length_replicate, List.sum_append,
      List.sum_const_nat] at hlen hsum
    simp only [stateSize, List.map_cons, List.sum_cons, hubSize, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, List.sum_append,
      List.sum_const_nat, List.sum_cons, List.sum_nil]
    omega
  | @tail hd s s' hst ih =>
    simp only [stateSize, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-! ### Normal forms -/

theorem exists_normalForm' (s : List Hub) :
    ∃ t, Relation.ReflTransGen OrderedStep s t ∧ ∀ u, ¬ OrderedStep t u := by
  refine orderedStep_wf.induction
    (C := fun s => ∃ t, Relation.ReflTransGen OrderedStep s t ∧ ∀ u, ¬ OrderedStep t u)
    s ?_
  intro x ih
  by_cases hx : ∃ y, OrderedStep x y
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨t, hyt, hnf⟩ := ih y hy
    exact ⟨t, Relation.ReflTransGen.head hy hyt, hnf⟩
  · exact ⟨x, Relation.ReflTransGen.refl, fun u hu => hx ⟨u, hu⟩⟩

end Step3
end R3Cert
