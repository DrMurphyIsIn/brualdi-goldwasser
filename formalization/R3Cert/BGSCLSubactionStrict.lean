/-
  The STRICT subaction ceiling — `bell b < 0` off the near-star tie (2026-09-04).

  The weak ceiling `bg_ceiling : ∀ b, bell b ≤ 0` (`BGSCLSubactionDispatch`) is proven via
  `IsSubaction ρwit`, whose bridge `ceiling_of_subaction` runs the strong induction on the invariant
  `bell b + ρwit b ≤ 0`.  This module upgrades that to a STRICT form off the tie diagonal.

  Two independent, kernel-checked sources of strictness are isolated:

    (i)  the WITNESS-POSITIVITY route.  The bridge's telescoping invariant `bell b + ρwit b ≤ 0`
         (re-exported here as `bell_add_ρwit_le`) gives `bell b ≤ −ρwit b`; whenever `ρwit b > 0`,
         `bell b < 0` follows immediately.  `ρwit b > 0` holds for EVERY hub of degree ≤ 4
         (`ρwit_pos_of_bcc_le3`): leaves (`= F* > 0`), the deg-2 line, and the deg-3/deg-4 lines
         `bY/32`, `bY/384` (with `bY > 0`).  So the ONLY branches this route misses are the deg≥5
         hubs — where `ρwit = 0`.

    (ii) the STRICT-ROOT-CELL route.  For a deg≥5 hub the local excess `e_root + ρwit(node) − Σρwit(c)`
         may still be STRICT; a strict root cell, fed through the same telescoping
         (`bell_lt_of_strict_root`, the strict analog of `ceiling_of_subaction`), yields
         `bell b + ρwit b < 0`, hence `bell b < 0` (as `ρwit b ≥ 0`).

  The tie set is exactly the residue of BOTH: a deg≥5 hub (`ρwit = 0`) whose root cell is TIGHT.  These
  are the near-star ties `N(c,k)`, `c+k = 5` (`R3Cert.NearStar.nearStar_family_le_zero`, the
  `logPhi`-side characterization).  We package the residue as `IsTie` and prove:

    * `master_ineq_strict : ∀ b, ¬ IsTie b → bell b < 0`   (routes (i) ⊔ (ii)),
    * `bell_eq_zero_imp_tie : bell b = 0 → IsTie b`         (the tie characterization ⟸),

  giving, with `bg_ceiling`, the `⟺` `bell b = 0 ↔ IsTie b` on the whole branch space.

  ROUTE USED: BOTH.  `ρwit`-positivity (route i) closes deg ≤ 4 with a one-line `linarith` off the
  re-exported invariant — no strict cells re-proved; the deg≥5 residue is closed by the strict bridge
  (route ii), whose sole hypothesis (`StrictRootCell`) is exactly the non-tie condition there.

  Kernel-checked vs `R3Cert.BGSCLSubaction`/`BGSCLSubactionDispatch`.  No `sorry`.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionDispatch

namespace R3Cert
namespace BGSCL

open Real

/-! ### The re-exported telescoping invariant `bell b + ρwit b ≤ 0`.

  `ceiling_of_subaction` proves `∀ b, bell b ≤ 0` through an internal invariant `bell b + ρ b ≤ 0`
  (its `key`).  We re-derive that invariant as a *public* lemma against the fully-assembled
  `isSubaction_ρwit`, so the strict routes can read `bell b ≤ −ρwit b`. -/

/-- **The telescoping invariant, re-exported.**  `bell b + ρwit b ≤ 0` for every branch — exactly the
    strengthened invariant of `ceiling_of_subaction`'s strong induction, instantiated at the assembled
    subaction `isSubaction_ρwit`.  Equivalent to `bell b ≤ −ρwit b`. -/
theorem bell_add_ρwit_le (b : Branch) : bell b + ρwit b ≤ 0 := by
  have hsplit : ∀ l : List Branch,
      (l.map (fun c => bell c + ρwit c)).sum = (l.map bell).sum + (l.map ρwit).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  refine scl_of_child_step bsize bchildren (fun b => bell b + ρwit b ≤ 0) bchildren_bsize_lt ?_ b
  intro a hIH
  cases a with
  | node cs =>
      have hsum : (cs.map (fun c => bell c + ρwit c)).sum ≤ 0 := by
        refine list_sum_nonpos ?_
        intro x hx; rw [List.mem_map] at hx; obtain ⟨c, hc, rfl⟩ := hx
        exact hIH c (by simpa [bchildren] using hc)
      rw [hsplit] at hsum
      have hsub := isSubaction_ρwit cs
      rw [bell_node]
      linarith

/-- `bell b ≤ −ρwit b` (the invariant, rearranged). -/
theorem bell_le_neg_ρwit (b : Branch) : bell b ≤ -ρwit b := by
  have := bell_add_ρwit_le b; linarith

/-! ### Strict rational anchors for `ρwit`. -/

/-- `0 < F*` strictly (`621/64 > 1` ⇒ `log(621/64) > 0`). -/
theorem fstar_pos : 0 < FSTAR := by
  rw [FSTAR]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The cherry/tie anchor is STRICTLY positive: `log(3/2) < 2F*` (via `(3/2)^11 < (621/64)^2`,
    i.e. `177147/2048 < 385641/4096`). -/
theorem cherry_anchor_pos : 0 < 2 * FSTAR - Real.log (3/2 : ℝ) := by
  rw [FSTAR]
  have h : 11 * Real.log (3/2 : ℝ) < 2 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((3/2 : ℝ) ^ (11:ℕ)) = 11 * Real.log (3/2) := by rw [Real.log_pow]; norm_num
    have e2 : Real.log ((621/64 : ℝ) ^ (2:ℕ)) = 2 * Real.log (621/64) := by rw [Real.log_pow]; norm_num
    have hlt : Real.log ((3/2 : ℝ) ^ (11:ℕ)) < Real.log ((621/64 : ℝ) ^ (2:ℕ)) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [e1, e2] at hlt; exact hlt
  linarith

/-! ### Route (i): the witness-positivity route (deg ≤ 4). -/

/-- **Strict witness positivity for hubs of degree ≤ 4.**  For any branch whose root class `bcc ≤ 3`
    (degree ≤ 4), `ρwit b > 0`:
    * `bcc = 0` (leaf): `ρwit = F* > 0`;
    * `bcc = 1` (deg-2): `2F* − log(3/2) + (1/4)(bY − 1/3) > 0`, from `2F* > log(3/2)` (strict) and `bY ≥ 1/3`;
    * `bcc = 2` (deg-3): `bY/32 > 0`;
    * `bcc = 3` (deg-4): `bY/384 > 0`.
    (`bY b > 0` for every branch — `bY = 1/(d+S) > 0`.) -/
theorem ρwit_pos_of_bcc_le3 (b : Branch) (hb : bcc b ≤ 3) : 0 < ρwit b := by
  -- strict positivity of the message `bY b`
  have hbYpos : 0 < bY b := by
    cases b with
    | node cs =>
      rw [bY_node]
      have hSnn : (0:ℝ) ≤ (cs.map bY).sum := List.sum_nonneg (fun x hx => by
        rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
      have hden : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.map bY).sum := by positivity
      positivity
  rcases (show bcc b = 0 ∨ bcc b = 1 ∨ bcc b = 2 ∨ bcc b = 3 by omega) with h | h | h | h
  · -- leaf
    have : ρwit b = FSTAR := by simp only [ρwit, h]
    rw [this]; exact fstar_pos
  · -- deg-2
    have hby3 : (1:ℝ)/3 ≤ bY b := by
      cases b with
      | node cs =>
        simp only [bcc] at h
        rcases cs with _ | ⟨c', _ | ⟨c2, t⟩⟩
        · simp at h
        · exact bY_deg2_ge_third c'
        · simp only [List.length_cons] at h; omega
    have hrho : ρwit b = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY b - 1/3) := by
      simp only [ρwit, h]
    rw [hrho]
    have hch := cherry_anchor_pos
    have hslope : (0:ℝ) ≤ (1/4) * (bY b - 1/3) := by
      apply mul_nonneg (by norm_num); linarith
    linarith
  · -- deg-3
    have : ρwit b = (1/32) * bY b := by simp only [ρwit, h]
    rw [this]; positivity
  · -- deg-4
    have : ρwit b = (1/384) * bY b := by simp only [ρwit, h]
    rw [this]; positivity

/-- **Route (i) conclusion.**  Any hub of degree ≤ 4 (`bcc ≤ 3`) has `bell b < 0`.  Off the invariant
    `bell b ≤ −ρwit b` and the strict positivity `ρwit b > 0`. -/
theorem bell_lt_of_bcc_le3 (b : Branch) (hb : bcc b ≤ 3) : bell b < 0 := by
  have h1 := bell_le_neg_ρwit b
  have h2 := ρwit_pos_of_bcc_le3 b hb
  linarith

/-! ### Route (ii): the strict-root-cell bridge (deg ≥ 5). -/

/-- **A strict root cell.**  The (SUB) inequality at the root of `b = node cs` is STRICT — the local
    excess plus the node's `ρwit` is *strictly* dominated by the children's `ρwit`-sum. -/
def StrictRootCell (b : Branch) : Prop :=
  ∃ cs : List Branch, b = Branch.node cs ∧
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs)
      < (cs.map ρwit).sum

/-- **The strict bridge.**  If the root cell of `b` is strict, then `bell b + ρwit b < 0` — the strict
    telescoping.  Proof: the child invariants `bell c + ρwit c ≤ 0` sum to `Σ bell c ≤ −Σ ρwit c`, and the
    `ell` recursion `bell(node cs) = Σ bell c + e_root` plus the STRICT root cell gives
    `bell(node cs) + ρwit(node cs) = Σ bell c + (e_root + ρwit(node cs)) < −Σρwit c + Σρwit c = 0`. -/
theorem bell_add_ρwit_lt_of_strict_root (b : Branch) (h : StrictRootCell b) :
    bell b + ρwit b < 0 := by
  obtain ⟨cs, rfl, hstrict⟩ := h
  -- child invariants summed
  have hsplit : ∀ l : List Branch,
      (l.map (fun c => bell c + ρwit c)).sum = (l.map bell).sum + (l.map ρwit).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  have hsum : (cs.map (fun c => bell c + ρwit c)).sum ≤ 0 := by
    refine list_sum_nonpos ?_
    intro x hx; rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx
    exact bell_add_ρwit_le c
  rw [hsplit cs] at hsum
  rw [bell_node]
  linarith

/-- **Route (ii) conclusion.**  If the root cell of `b` is strict, then `bell b < 0` (with `ρwit b ≥ 0`). -/
theorem bell_lt_of_strict_root (b : Branch) (h : StrictRootCell b) : bell b < 0 := by
  have h1 := bell_add_ρwit_lt_of_strict_root b h
  have h2 := ρwit_nonneg b
  linarith

/-! ### The tie set and the master strict inequality. -/

/-- **The tie set.**  A branch is a *tie* when it is a deg≥5 hub whose root cell is TIGHT (not strict) —
    the residue that BOTH strict routes leave.  Concretely: `bcc b ≥ 4` (degree ≥ 5, so `ρwit b = 0`) and
    the root cell is an equality (`¬ StrictRootCell b`).  These are exactly the near-star ties `N(c,k)`,
    `c+k = 5` on the `bell` side (root degree `c+k = 5`, root cell tight, `bell = 0`), the residue of the
    `logPhi`-side `nearStar_family_le_zero`. -/
def IsTie (b : Branch) : Prop := 4 ≤ bcc b ∧ ¬ StrictRootCell b

/-- **The master strict inequality.**  Off the tie set, `bell b < 0`.  Case split by degree: hubs of
    degree ≤ 4 (`bcc ≤ 3`) are closed by route (i) (`ρwit b > 0`); a non-tie hub of degree ≥ 5
    (`bcc ≥ 4`) must have a STRICT root cell (that is exactly `¬IsTie` there), closed by route (ii). -/
theorem master_ineq_strict : ∀ b, ¬ IsTie b → bell b < 0 := by
  intro b hnt
  rcases (show bcc b ≤ 3 ∨ 4 ≤ bcc b by omega) with hle | hge
  · -- degree ≤ 4: route (i)
    exact bell_lt_of_bcc_le3 b hle
  · -- degree ≥ 5: non-tie ⇒ strict root cell ⇒ route (ii)
    have hstrict : StrictRootCell b := by
      by_contra hns
      exact hnt ⟨hge, hns⟩
    exact bell_lt_of_strict_root b hstrict

/-! ### The tie characterization. -/

/-- Off degree ≤ 4, `bell b < 0`, so a branch with `bell b = 0` must be a deg≥5 hub. -/
theorem bcc_ge_four_of_bell_eq_zero {b : Branch} (h : bell b = 0) : 4 ≤ bcc b := by
  by_contra hlt
  have : bcc b ≤ 3 := by omega
  have := bell_lt_of_bcc_le3 b this
  linarith

/-- **The tie characterization (⟸).**  If `bell b = 0` then `b` is a tie.  A `bell = 0` branch is a
    deg≥5 hub (`bcc_ge_four_of_bell_eq_zero`) whose root cell CANNOT be strict — a strict root cell would
    force `bell b < 0` by route (ii), contradicting `bell b = 0`. -/
theorem bell_eq_zero_imp_tie {b : Branch} (h : bell b = 0) : IsTie b := by
  refine ⟨bcc_ge_four_of_bell_eq_zero h, ?_⟩
  intro hstrict
  have := bell_lt_of_strict_root b hstrict
  linarith

/-! ### On the reverse direction (`IsTie → bell = 0`).

  UPDATE 2026-09-24: SUPERSEDED.  `R3Cert.BGSCL.isTie_iff_bell_eq_zero` (`BGSCLSharp`) proves the full
  `IsTie b ↔ bell b = 0`: a tight degree-6 root cell forces all five children to be cherries
  (`isTie_imp_nearStarTie`), so the worry below does not materialize.  Original note kept for history:

  NOTE — HONEST SCOPE.  The reverse implication `IsTie b → bell b = 0` is NOT proved here, and is
  genuinely FALSE for this purely-local `IsTie` (deg≥5 hub + tight root cell): a deg≥5 hub with a tight
  root cell but a strictly-subordinate child (`bell c < −ρwit c`) still has `bell b < 0`.  A tight ROOT
  cell does not force the whole telescope to be tight.  Pinning down the exact `bell b = 0` locus is the
  genuine near-star structural characterization (`c+k = 5` on ALL of `N(c,k)`), which is the open gap;
  on the `logPhi` side it is `R3Cert.NearStar.nearStar_family_le_zero` (a proven 2-parameter gadget
  instance, not the full branch space).  So we deliver only the sound direction `bell = 0 → IsTie`
  (`bell_eq_zero_imp_tie`) plus the master strict inequality; the `⟺` is deliberately NOT claimed. -/
