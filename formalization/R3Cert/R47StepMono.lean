/-
  R4-R7 campaign, PHASE 5e (capstone file): STEP MONOTONICITY and the chain corollary.

  * `OrderedStep.inv`  -- positional inversion: every ordered step is a hubward or
    anti-hubward merge at some backbone position (the tail constructor accumulates
    the prefix);
  * `Aobj_at`          -- the rotation glue: `Aobj (backboneU (pre ++ h :: down))
    = AobjV pre.reverse h down` (from `Aobj_eq_AobjV` via `reverseAux_eq`);
  * `step_mono`        -- **AN ORDERED MERGE NEVER DECREASES THE OBJECTIVE** on the
    certified family: invert to the position, rotate to the absorber, apply the
    matching direction of the dispatched monotonicity;
  * `chain_mono`, `chain_to_normalForm` -- **THE MERGE-LAYER CAPSTONE**: every
    Balanced-and-Capped state rewrites, monotonically in `per L/∏deg` (via
    `pi_utree`), to an ordered-merge normal form.

  HONEST SCOPE: this closes the MERGE LAYER of the reduction on the certified
  family.  The (L)/(B) normalization layer (bringing arbitrary trees INTO the
  family), R5/R6, the stratum-(i) rate port, and the R7' assembly remain named open
  layers.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47OrderedStep
import R3Cert.R47VeeDispatch

namespace R3Cert
namespace Step3

open RTree

/-! ### Positional inversion -/

theorem OrderedStep.inv {s s' : List Hub} (h : OrderedStep s s') :
    (∃ pre armsA cA armsB others cb rest,
        s = pre ++ (armsA, cA) :: (armsB, cb) :: rest
      ∧ s' = pre ++ (armsA ++ List.replicate (5 - cb) 4 ++ others ++ [5], cA) :: rest
      ∧ cb ≤ 5 ∧ armsB.Perm (List.replicate (5 - cb) 5 ++ others)
      ∧ armsB.length + (tailU rest).length ≤ armsA.length)
  ∨ (∃ pre armsA othersA cA armsB cb rest,
        s = pre ++ (armsA, cA) :: (armsB, cb) :: rest
      ∧ s' = pre ++ (armsB ++ List.replicate (5 - cA) 4 ++ othersA ++ [5], cb) :: rest
      ∧ cA ≤ 5 ∧ armsA.Perm (List.replicate (5 - cA) 5 ++ othersA)
      ∧ armsA.length + 1 ≤ armsB.length + (tailU rest).length) := by
  induction h with
  | @merge armsA cA armsB others cb rest hcb hsplit hord =>
    exact Or.inl ⟨[], armsA, cA, armsB, others, cb, rest, rfl, rfl, hcb, hsplit, hord⟩
  | @mergeRev armsA othersA cA armsB cb rest hcA hsplit hord =>
    exact Or.inr ⟨[], armsA, othersA, cA, armsB, cb, rest, rfl, rfl, hcA, hsplit, hord⟩
  | @tail hd s s' hst ih =>
    rcases ih with ⟨pre, aA, cA, aB, ot, cb, rest, hs, hs', h1, h2, h3⟩
      | ⟨pre, aA, ot, cA, aB, cb, rest, hs, hs', h1, h2, h3⟩
    · exact Or.inl ⟨hd :: pre, aA, cA, aB, ot, cb, rest,
        by rw [hs, List.cons_append], by rw [hs', List.cons_append], h1, h2, h3⟩
    · exact Or.inr ⟨hd :: pre, aA, ot, cA, aB, cb, rest,
        by rw [hs, List.cons_append], by rw [hs', List.cons_append], h1, h2, h3⟩

/-! ### The rotation glue -/

theorem Aobj_at (pre : List Hub) (h : Hub) (down : List Hub) :
    Aobj (backboneU (pre ++ h :: down)) = AobjV pre.reverse h down := by
  have hrot := Aobj_eq_AobjV pre.reverse h down
  rwa [List.reverseAux_eq, List.reverse_reverse] at hrot

/-- The state tail block has at most one element. -/
theorem tailU_length_le (l : List Hub) : (tailU l).length ≤ 1 := by
  cases l with
  | nil => rw [tailU_nil]; simp
  | cons h t => rw [tailU_cons]; simp

/-! ### Membership extraction helpers -/

theorem Balanced.sub_append {pre post : List Hub} (h : Balanced (pre ++ post)) :
    Balanced pre ∧ Balanced post :=
  ⟨fun x hx => h x (List.mem_append.mpr (Or.inl hx)),
   fun x hx => h x (List.mem_append.mpr (Or.inr hx))⟩

theorem Capped.sub_append {pre post : List Hub} (h : Capped (pre ++ post)) :
    Capped pre ∧ Capped post :=
  ⟨fun x hx => h x (List.mem_append.mpr (Or.inl hx)),
   fun x hx => h x (List.mem_append.mpr (Or.inr hx))⟩

theorem Balanced.reverse {l : List Hub} (h : Balanced l) : Balanced l.reverse :=
  fun x hx => h x (List.mem_reverse.mp hx)

theorem Capped.reverse {l : List Hub} (h : Capped l) : Capped l.reverse :=
  fun x hx => h x (List.mem_reverse.mp hx)

/-- Movers of a balanced donor are balanced (permutation membership). -/
theorem BalancedArms.of_perm_right {arms fives others : List ℕ}
    (h : BalancedArms arms) (hp : arms.Perm (fives ++ others)) :
    BalancedArms others :=
  fun j hj => h j (hp.mem_iff.mpr (List.mem_append.mpr (Or.inr hj)))

/-! ### STEP MONOTONICITY -/

/-- **An ordered merge never decreases the objective** on the certified family. -/
theorem step_mono {s s' : List Hub} (hst : OrderedStep s s')
    (hbal : Balanced s) (hcap : Capped s) :
    Aobj (backboneU s) ≤ Aobj (backboneU s') := by
  rcases hst.inv with ⟨pre, aA, cA, aB, ot, cb, rest, hs, hs', hcb, hsplit, hord⟩
    | ⟨pre, aA, ot, cA, aB, cb, rest, hs, hs', hcA, hsplit, hord⟩
  · subst hs
    subst hs'
    obtain ⟨hbalP, hbalM⟩ := Balanced.sub_append hbal
    obtain ⟨hcapP, hcapM⟩ := Capped.sub_append hcap
    rw [Aobj_at pre (aA, cA) ((aB, cb) :: rest), Aobj_at pre _ rest]
    apply vee_merge_le aA cA aB ot cb (5 - cb) rest pre.reverse
      ((hbalM (aA, cA) (by simp)).2) hcb rfl hsplit
      ((hbalM (aA, cA) (by simp)).1)
      (BalancedArms.of_perm_right ((hbalM (aB, cb) (by simp)).1) hsplit)
      (fun x hx => hcapM x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      (Capped.reverse hcapP)
      (hcapM (aB, cb) (by simp))
    omega
  · subst hs
    subst hs'
    obtain ⟨hbalP, hbalM⟩ := Balanced.sub_append hbal
    obtain ⟨hcapP, hcapM⟩ := Capped.sub_append hcap
    rw [Aobj_at pre (aA, cA) ((aB, cb) :: rest), Aobj_at pre _ rest]
    have hshift : AobjV pre.reverse (aA, cA) ((aB, cb) :: rest)
        = AobjV ((aA, cA) :: pre.reverse) (aB, cb) rest := AobjV_shift _ _ _ _
    rw [hshift]
    apply mirror_merge_le aA ot cA aB cb (5 - cA) rest pre.reverse
      hcA ((hbalM (aB, cb) (by simp)).2) rfl hsplit
      ((hbalM (aB, cb) (by simp)).1)
      (BalancedArms.of_perm_right ((hbalM (aA, cA) (by simp)).1) hsplit)
      (fun x hx => hcapM x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      (Capped.reverse hcapP)
      (hcapM (aA, cA) (by simp))
    have htl := tailU_length_le pre.reverse
    omega

/-! ### THE CHAIN COROLLARY -/

theorem Balanced.chain {s t : List Hub}
    (h : Relation.ReflTransGen OrderedStep s t) (hb : Balanced s) : Balanced t := by
  induction h with
  | refl => exact hb
  | tail _ hbc ih => exact hbc.balanced ih

theorem Capped.chain {s t : List Hub}
    (h : Relation.ReflTransGen OrderedStep s t) (hc : Capped s) : Capped t := by
  induction h with
  | refl => exact hc
  | tail _ hbc ih => exact hbc.capped ih

/-- **The objective is monotone along every ordered-merge chain** on the certified
    family. -/
theorem chain_mono {s t : List Hub} (h : Relation.ReflTransGen OrderedStep s t)
    (hbal : Balanced s) (hcap : Capped s) :
    Aobj (backboneU s) ≤ Aobj (backboneU t) := by
  induction h with
  | refl => exact le_refl _
  | @tail b c hab hbc ih =>
    exact le_trans ih (step_mono hbc (Balanced.chain hab hbal) (Capped.chain hab hcap))

/-- **THE MERGE-LAYER CAPSTONE**: every certified state rewrites, monotonically in
    the objective, to an ordered-merge normal form. -/
theorem chain_to_normalForm (s : List Hub) (hbal : Balanced s) (hcap : Capped s) :
    ∃ t, Relation.ReflTransGen OrderedStep s t ∧ (∀ u, ¬ OrderedStep t u)
      ∧ Aobj (backboneU s) ≤ Aobj (backboneU t) := by
  obtain ⟨t, hst, hnf⟩ := exists_normalForm' s
  exact ⟨t, hst, hnf, chain_mono hst hbal hcap⟩

end Step3
end R3Cert
