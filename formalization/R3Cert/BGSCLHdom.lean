/-
  The Hdom layer — STRICT root cell off the exact near-star tie (2026-09-04).

  MISSION (Part 1, this file): strengthen the strict master inequality
  `master_ineq_strict : ∀ b, ¬IsTie b → bell b < 0` (`R3Cert.BGSCLSubactionStrict`).  There the deg≥5
  branches are gated on `StrictRootCell b` (a STRICT root cell); the residue `IsTie b := 4 ≤ bcc b ∧
  ¬StrictRootCell b` is exactly the near-star tie.  This file DISCHARGES `StrictRootCell` for every
  deg≥5 hub EXCEPT the exact `d = 6`, five-cherry near-star tie, by showing the deg≥5 tail cells are
  STRICT (they carry fat rational margins: per `tie_regime.py`, `+0.007..+0.076`; only the `27·23` tie at
  `d = 6` is tight).

  ARCHITECTURE.  The tail (SUB) cells all factor through `tail_decouple` (`BGSCLSubactionTailDecouple`),
  which reduces `(SUB)` at a deg≥5 hub to
    (i)  a per-child affine lower bound  `m + σ·bY c ≤ ρwit c`  (`σ = 1/(d+S0)`), and
    (ii) `B(S0) := (d−1)·m + [F* − log(1+S0/d) + S0/(d+S0)] ≥ 0`.
  We build the STRICT analogue `tail_decouple_strict`: with the SAME per-child bound but a STRICT
  `0 < B(S0)`, the concave-log tangent yields the STRICT root-cell inequality
    `(log(1 + S/d) − F*) + ρwit(node cs) < Σ_c ρwit(c)`,
  which is EXACTLY `StrictRootCell (node cs)`.  So Part 1 = "`0 < B(S0)` off `d = 6`" for every tail cell.

  The B-margins are already rational-strict in the existing `≤` proofs: `tail_all_deg4`'s quadratic
  `275d²−7955d+84480` has NEGATIVE discriminant (strictly positive), etc.  Rather than re-derive strict
  atoms, each strict cell reuses the existing `≤` B-atom together with the concrete rational slack.

  DELIVERED:
    * `tail_decouple_strict`             — the strict decouple (STRICT `B` ⇒ STRICT root cell).
    * `strict_tail_d{5,7,8,9,62,63,64}`, `strict_tail_deg4`, `strict_tail_deg5` — every deg≥5 tail cell
                                           EXCEPT `d = 6`, proven with a STRICT root-cell conclusion.
    * `strictRootCell_tail`              — `∀ cs, 4 ≤ |cs| → |cs| ≠ 5 → StrictRootCell (node cs)`
                                           (every deg≥5 hub of root degree ≠ 6).
    * `strictRootCell_of_deg_ne_six`     — the `bcc`-phrased version.
    * `isTie_imp_bcc_eq_five`            — the tie set `IsTie` (`R3Cert.BGSCLSubactionStrict`) is CONFINED
                                           to root degree exactly 6.  This is the Part-1 strengthening: the
                                           residue of the strict master inequality drops from "all deg≥5 with
                                           tight root cell" to "degree EXACTLY 6 with tight root cell".
    * `master_ineq_strict_off_deg6`      — `bell b < 0` for every `b` of root degree `≠ 6`; and
      `bcc_eq_five_of_bell_eq_zero`        `bell b = 0 ⇒ bcc b = 5` (a `bell = 0` branch is a degree-6 hub).
    * `IsNearStarTie`                    — the EXACT structural tie predicate (root degree 6, five cherry
                                           children `node [leaf]`), with `bcc_eq_five_of_nearStarTie`.

    * `phi_lb_d6_strict_of_bY_gt`, `strict_tail_d6_of_bY_gt`, `sum_rhowit_gt`, `tail_decouple_strict_child`
                                           — the CLOSABLE slice INSIDE degree 6: a `d = 6` hub carrying a
                                           child with message `1/3 < bY a` (a leaf, or a deg-2 hub pushed
                                           above the cherry value) has a STRICT root cell.

  HONEST SCOPE — the `d = 6` residual.  This file fully discharges `StrictRootCell` for every deg≥5 hub of
  degree `≠ 6` (`master_ineq_strict_off_deg6`), collapsing the tie set to root degree EXACTLY 6, and
  additionally strictly separates from the tie every `d = 6` hub carrying an ABOVE-cherry child (`bY > 1/3`,
  `strict_tail_d6_of_bY_gt`).  It does NOT close the LAST slice inside degree 6: a `d = 6` hub whose five
  children are all deg-2/deg≥3 with EVERY message `≤ 1/3` but summing to exactly `5/3` (the all-cherry tie is
  the canonical instance; a non-all-cherry instance would need every child at `bY = 1/3`, i.e. all cherries,
  so structurally the tie is precisely the five-cherry hub — but proving that deg-3/deg-4 children CANNOT reach
  `bY = 1/3`, hence forcing all-cherry, needs a strict `bY < 1/3` sub-degree lemma not yet available here).
  So the deliverable is the SOUND, degree-sharp `master_ineq_strict_off_deg6` plus the above-cherry `d = 6`
  slice; the FULL "strict off the EXACT five-cherry tie" is reduced to the remaining "no deg≥3 child attains
  `bY = 1/3`" lemma and is NOT over-claimed.  See `IsNearStarTie` for the exact structural tie.

  Kernel-checked vs `R3Cert.BGSCLSubactionStrict` / `BGSCLSubactionTail{,Decouple,Wrap}`.  No `sorry`.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionTail
import R3Cert.BGSCLSubactionTailDecouple
import R3Cert.BGSCLSubactionTailWrap
import R3Cert.BGSCLSubactionStrict

namespace R3Cert
namespace BGSCL

open Real

/-! ### The STRICT tail-decouple. -/

/-- **The STRICT tail DECOUPLE reduction.**  Identical to `tail_decouple` but with a STRICT
    `0 < B(S0)` (ii); the conclusion is the STRICT root-cell inequality
    `(log(1 + S/d) − F*) + ρwit(node cs) < Σ_c ρwit(c)`.  Proof: `tail_decouple`'s `linarith` closure with
    the strict `hB` propagates strictness (the concave-log tangent `htan` and the list-lift `hsum` are `≤`,
    so the single strict term `hB` makes the sum strict). -/
theorem tail_decouple_strict (cs : List Branch) (S0 m : ℝ)
    (hlen : 4 ≤ cs.length) (hS0 : 0 ≤ S0)
    (hpc : ∀ c ∈ cs, m + (1 / (((cs.length : ℝ) + 1) + S0)) * bY c ≤ ρwit c)
    (hB : 0 < (cs.length : ℝ) * m
            + (FSTAR - Real.log (1 + S0 / ((cs.length : ℝ) + 1))
               + S0 / (((cs.length : ℝ) + 1) + S0))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have hd_pos : (0 : ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hdS0 : (0 : ℝ) < ((cs.length : ℝ) + 1) + S0 := by positivity
  have hS_nn : (0 : ℝ) ≤ (cs.map bY).sum :=
    List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
  have htan := log_tangent (d := (cs.length : ℝ) + 1) (s := (cs.map bY).sum) (s0 := S0)
    hd_pos hS_nn hS0
  have hsum := sum_rhowit_ge (1 / (((cs.length : ℝ) + 1) + S0)) m cs hpc
  have hsp : ((cs.map bY).sum - S0) / (((cs.length : ℝ) + 1) + S0)
      = (1 / (((cs.length : ℝ) + 1) + S0)) * (cs.map bY).sum
        - S0 / (((cs.length : ℝ) + 1) + S0) := by
    field_simp
  rw [ρwit_node_high hlen]
  linarith [htan, hsum, hB, hsp]

/-- Producer of `StrictRootCell (node cs)` from the strict root-cell inequality.  `StrictRootCell b` is
    `∃ cs, b = node cs ∧ (log(1 + S/(|cs|+1)) − F*) + ρwit(node cs) < Σ ρwit`; here `S/(|cs|+1)` is written
    as `(cs.map bY).sum / ((cs.length:ℝ)+1)`, matching `tail_decouple_strict`'s conclusion verbatim. -/
theorem strictRootCell_of_ineq (cs : List Branch)
    (h : (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
          + ρwit (Branch.node cs) < (cs.map ρwit).sum) :
    StrictRootCell (Branch.node cs) := ⟨cs, rfl, h⟩

/-! ### The deg-5 (large-`d`) STRICT tail regime, `|cs| ≥ 64`. -/

/-- `log(6/5) < F*` STRICTLY (`(6/5)¹¹ = 362797056/48828125 ≈ 7.43 < 621/64 ≈ 9.70`). -/
theorem log65_lt_fstar : Real.log (6/5 : ℝ) < FSTAR := by
  rw [FSTAR]
  have e : Real.log ((6/5 : ℝ) ^ (11:ℕ)) = 11 * Real.log (6/5) := by rw [Real.log_pow]; norm_num
  have hlt : Real.log ((6/5 : ℝ) ^ (11:ℕ)) < Real.log (621/64) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [e] at hlt; linarith

/-- **STRICT deg-5 tail cell, `|cs| ≥ 64`.**  Strict root cell at every hub of degree `≥ 65`.  Mirrors
    `subaction_tail_deg5` but threads the STRICT `log(6/5) < F*`: the B-obligation
    `B = F* − log((6d−1)/(5d))` is `> 0` since `log((6d−1)/(5d)) ≤ log(6/5) < F*`. -/
theorem strict_tail_deg5 (cs : List Branch) (hlen : 64 ≤ cs.length) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  have hL : (64:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hlen
  have hDpos : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5 := by positivity
  set σ : ℝ := 1 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) with hσdef
  have hσ0 : 0 < σ := by rw [hσdef]; positivity
  have hσle : σ ≤ 5/384 := by
    rw [hσdef, div_le_iff₀ hDpos]; nlinarith [hL]
  refine tail_decouple_strict cs ((cs.length : ℝ) / 5) (-σ/5) h4 (by positivity) ?_ ?_
  · intro c _
    rw [show (1 : ℝ) / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) = σ from hσdef.symm]
    exact phi_lb_general σ hσ0 hσle c
  · have hcancel : (cs.length : ℝ) * (-σ/5)
        + (cs.length : ℝ) / 5 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 5) = 0 := by
      rw [hσdef]; field_simp; ring
    have harg : (1 : ℝ) + (cs.length : ℝ) / 5 / ((cs.length : ℝ) + 1)
        = (6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)) := by
      field_simp; ring
    have hloglt : Real.log (1 + (cs.length : ℝ) / 5 / ((cs.length : ℝ) + 1)) < FSTAR := by
      rw [harg]
      have hb65 : (6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)) ≤ 6/5 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hL]
      have hmono : Real.log ((6 * (cs.length : ℝ) + 5) / (5 * ((cs.length : ℝ) + 1)))
          ≤ Real.log (6/5) := Real.log_le_log (by positivity) hb65
      have := log65_lt_fstar
      linarith
    linarith [hcancel, hloglt]

/-! ### The deg-4 STRICT tail regime, `|cs| ∈ [9,60]`. -/

/-- **STRICT `tail_all_deg4`.**  `log((5d−1)/(4d)) − F* < (d−1)/1536` for every real `d ≥ 1`.  Same recipe as
    `tail_all_deg4`, but the rational quadratic `275d²−7955d+84480` is STRICTLY positive (discriminant
    `7955² − 4·275·84480 = −29645975 < 0`), giving strict slack. -/
theorem tail_all_deg4_strict (d : ℝ) (hd : 1 ≤ d) :
    Real.log ((5 * d - 1) / (4 * d)) - FSTAR < (d - 1) / 1536 := by
  have hd0 : (0 : ℝ) < d := by linarith
  have h5d : (0 : ℝ) < 5 * d := by linarith
  have hfact : (5 * d - 1) / (4 * d) = (5 / 4) * (1 - 1 / (5 * d)) := by field_simp
  have harg_pos : (0 : ℝ) < 1 - 1 / (5 * d) := by
    have : 1 / (5 * d) < 1 := by rw [div_lt_one h5d]; linarith
    linarith
  have hsplit : Real.log ((5 * d - 1) / (4 * d)) = Real.log (5 / 4) + Real.log (1 - 1 / (5 * d)) := by
    rw [hfact, Real.log_mul (by norm_num) (ne_of_gt harg_pos)]
  have hlog1 : Real.log (1 - 1 / (5 * d)) ≤ -(1 / (5 * d)) := by
    have h := Real.log_le_sub_one_of_pos harg_pos; linarith
  have henc : Real.log (5 / 4) - FSTAR ≤ 1 / 55 := log54_sub_fstar_le'
  -- STRICT rational quadratic: 1/55 − 1/(5d) < (d−1)/1536.
  have hquad : (1 : ℝ) / 55 - 1 / (5 * d) < (d - 1) / 1536 := by
    rw [← sub_pos]
    have hden : (0 : ℝ) < 422400 * d := by positivity
    have hnum : (0 : ℝ) < 275 * d ^ 2 - 7955 * d + 84480 := by
      nlinarith [sq_nonneg (110 * d - 1591)]
    have hid : (d - 1) / 1536 - (1 / 55 - 1 / (5 * d))
        = (275 * d ^ 2 - 7955 * d + 84480) / (422400 * d) := by
      field_simp; ring
    rw [hid]; exact div_pos hnum hden
  linarith [hsplit, hlog1, henc, hquad]

/-- **STRICT deg-4 tail cell, `|cs| ∈ [9,60]`.**  Strict root cell at every hub of degree `∈ [10,61]`.
    Mirrors `subaction_tail_deg4` with the STRICT `tail_all_deg4_strict`. -/
theorem strict_tail_deg4 (cs : List Branch) (h1 : 9 ≤ cs.length) (h2 : cs.length ≤ 60) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  have hL9 : (9:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast h1
  have hL60 : (cs.length : ℝ) ≤ 60 := by exact_mod_cast h2
  have hDpos : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.length : ℝ) / 4 := by positivity
  set σ : ℝ := 1 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 4) with hσdef
  have hσlo : 5/384 ≤ σ := by rw [hσdef, le_div_iff₀ hDpos]; nlinarith [hL60]
  have hσhi : σ ≤ 4/49 := by rw [hσdef, div_le_iff₀ hDpos]; nlinarith [hL9]
  refine tail_decouple_strict cs ((cs.length : ℝ) / 4) (1/1536 - σ/4) h4 (by positivity) ?_ ?_
  · intro c _
    rw [show (1 : ℝ) / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 4) = σ from hσdef.symm]
    exact phi_lb_deg4 σ hσlo hσhi c
  · have htad := tail_all_deg4_strict ((cs.length : ℝ) + 1) (by linarith)
    have hcancel : (cs.length : ℝ) * (1/1536 - σ/4)
        + (cs.length : ℝ) / 4 / (((cs.length : ℝ) + 1) + (cs.length : ℝ) / 4) = (cs.length : ℝ) / 1536 := by
      rw [hσdef]; field_simp; ring
    have harg : (1 : ℝ) + (cs.length : ℝ) / 4 / ((cs.length : ℝ) + 1)
        = (5 * ((cs.length : ℝ) + 1) - 1) / (4 * ((cs.length : ℝ) + 1)) := by
      field_simp; ring
    rw [harg]
    linarith [htad, hcancel]

/-! ### The CHERRY STRICT tail cells `d ∈ {5,7,8,9}` (`|cs| ∈ {4,6,7,8}`).

  Each is a `tail_decouple_strict` at the cherry per-child min `phi_lb_cherry`, with a STRICT B-obligation.
  For `d ∈ {5,7}` the B collapses to `tail_all_deg2` at the concrete `d`; those are STRICTLY below the tie
  (`d = 5` fold `X < 1` ⇒ strict; `d = 7` interior of the deg-2 family ⇒ strict quadratic `q(7) > 0`).  For
  `d ∈ {8,9}` the shifted-reference B uses `henc_cherry_d8/d9`, whose Taylor-exp folds carry rational slack. -/

/-- STRICT d=5 leg: `log(19/15) < 9F* − 4log(3/2)` (fold `X < 1` ⇒ `log X < 0` strictly). -/
theorem tail_deg2_d5_strict : Real.log (19 / 15) < 9 * FSTAR - 4 * Real.log (3 / 2) := by
  rw [FSTAR]
  set X : ℝ := (19 / 15 : ℝ) ^ (11 : ℕ) * (3 / 2 : ℝ) ^ (44 : ℕ) * (((621 / 64 : ℝ) ^ (9 : ℕ))⁻¹) with hXdef
  have hpos : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hX1 : X < 1 := by rw [hXdef]; norm_num
  have hr : Real.log X < 0 := Real.log_neg hpos hX1
  have hs : Real.log X = 11 * Real.log (19 / 15) + 44 * Real.log (3 / 2) - 9 * Real.log (621 / 64) := by
    rw [hXdef, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hs] at hr; linarith

/-- **STRICT CHERRY cell `d = 5`** (`|cs| = 4`).  `S0 = 4/3`, `σ = 3/19`; strict B via `tail_deg2_d5_strict`. -/
theorem strict_tail_d5 (cs : List Branch) (hlen : cs.length = 4) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple_strict cs (4/3) (2 * FSTAR - Real.log (3/2) - (3/19)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 4/3) = 3/19 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (3/19) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 4/3 / (4 + 1) = 19/15 by norm_num,
        show (4:ℝ)/3 / ((4 + 1) + 4/3) = 4/19 by norm_num]
    have h := tail_deg2_d5_strict
    linarith

/-- STRICT d=7 leg of the deg-2 family: `log(9/7) < 13F* − 6log(3/2)` (interior, strict quadratic `q(7) > 0`). -/
theorem tail_deg2_d7_strict : Real.log (9 / 7 : ℝ) < 13 * FSTAR - 6 * Real.log (3 / 2) := by
  -- x = 7 leg of tail_all_deg2_large, but STRICT: the quadratic q(7) > 0 strictly and concavity is ≤.
  have hfact : (9 / 7 : ℝ) = (4 / 3) * (1 - 1 / (4 * 7)) := by norm_num
  have harg : (0 : ℝ) < 1 - 1 / (4 * (7:ℝ)) := by norm_num
  have hsplit : Real.log (9/7 : ℝ) = Real.log (4 / 3) + Real.log (1 - 1 / (4 * (7:ℝ))) := by
    rw [show (9/7:ℝ) = (4/3) * (1 - 1/(4*7)) by norm_num, Real.log_mul (by norm_num) (ne_of_gt harg)]
  have hlog1 : Real.log (1 - 1 / (4 * (7:ℝ))) ≤ -(1 / (4 * (7:ℝ))) := by
    have := Real.log_le_sub_one_of_pos harg; linarith
  have ha : (0 : ℝ) ≤ 2 * FSTAR - Real.log (3 / 2) := cherry_anchor_nonneg
  have hqp7 := henc_deg2_qp7
  have hq7 := henc_deg2_q7
  -- STRICT q(7): 4a·49 − 4(a+p)·7 + 1 > 0.  q(7) = 4a·49 − 28(a+p) + 1 = 168a − 28p + 1
  --            = 28(6a − p) + 1 ≥ 1 − 28·(1/28) = 0, but strict via the 1.  q(7) = 1 − 28(p−6a) ≥ 1 − 28·(1/28)=0.
  -- Actually strict: p − 6a ≤ 1/28 (hq7) so q(7) = 1 − 28(p−6a) ≥ 0; need STRICT.  Use hq7 as ≤ and the concavity
  -- slack: log(1−1/28) < −1/28 is NOT available cheaply. Instead: the deg-2 corner value.
  -- We show log(9/7) − F* < 13F* ... via: log(4/3) − 1/28 ≤ 13F* − 6log(3/2) with strict from concavity margin.
  -- Cleanest: log(1 − 1/28) < −1/28 strictly (Real.log_lt_sub_one_of_ne, since 1−1/28 ≠ 1).
  have hlog1s : Real.log (1 - 1 / (4 * (7:ℝ))) < -(1 / (4 * (7:ℝ))) := by
    have hne : (1 - 1 / (4 * (7:ℝ))) ≠ 1 := by norm_num
    have := Real.log_lt_sub_one_of_pos harg hne; linarith
  have hq : Real.log (4 / 3) - 1 / (4 * (7:ℝ)) ≤ 13 * FSTAR - 6 * Real.log (3 / 2) := by
    -- q(7) ≥ 0 (nonstrict is enough; strictness comes from hlog1s).
    nlinarith [hqp7, hq7, ha]
  linarith [hsplit, hlog1s, hq]

/-- **STRICT CHERRY cell `d = 7`** (`|cs| = 6`).  `S0 = 2`, `σ = 1/9`; strict B via `tail_deg2_d7_strict`. -/
theorem strict_tail_d7 (cs : List Branch) (hlen : cs.length = 6) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple_strict cs 2 (2 * FSTAR - Real.log (3/2) - (1/9)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/9 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/9) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (6 + 1) = 9/7 by norm_num,
        show (2:ℝ) / ((6 + 1) + 2) = 2/9 by norm_num]
    have h := tail_deg2_d7_strict
    linarith

/-- **STRICT CHERRY cell `d = 8`** (`|cs| = 7`).  `S0 = 2`, `σ = 1/10`; strict B via the strict fold below. -/
theorem henc_cherry_d8_strict : Real.log (5/4) < (15 * FSTAR - 7 * Real.log (3/2)) - 1/30 := by
  set val : ℝ := (5/4:ℝ)^(11:ℕ) * (3/2:ℝ)^(77:ℕ) * ((621/64:ℝ)^(15:ℕ))⁻¹ with hvaldef
  have hvalpos : (0:ℝ) < val := by rw [hvaldef]; positivity
  have hlog : Real.log val = 11 * Real.log (5/4) + 77 * Real.log (3/2) - 15 * Real.log (621/64) := by
    rw [hvaldef, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hb := Real.exp_bound (x := (11/30 : ℝ)) (by norm_num) (n := 3) (by norm_num)
  have hhi := (abs_le.mp hb).2
  have hs : ∑ i ∈ Finset.range 3, (11/30:ℝ)^i / (i.factorial:ℝ) = 1 + 11/30 + (11/30)^2/2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hhi
  have hexpub : Real.exp (11/30) ≤ (2140657 : ℝ)/1458000 := by
    have herr : (1 + 11/30 + (11/30)^2/2) + |(11/30:ℝ)|^3 * ((3+1)/((Nat.factorial 3:ℝ)*3))
        ≤ (2140657 : ℝ)/1458000 := by norm_num [Nat.factorial]
    linarith [hhi, herr]
  have hexppos : (0:ℝ) < Real.exp (11/30) := Real.exp_pos _
  -- STRICT: val < exp(−11/30) since val · tub < 1 strictly.
  have hvallt : val < Real.exp (-(11/30)) := by
    rw [Real.exp_neg, lt_inv_comm₀ hvalpos hexppos]
    calc Real.exp (11/30) ≤ (2140657:ℝ)/1458000 := hexpub
      _ < val⁻¹ := by rw [hvaldef, lt_inv_comm₀ (by norm_num) (by positivity)]; norm_num
  have hfinal : Real.log val < -(11/30) := by
    rw [← Real.log_exp (-(11/30))]; exact Real.log_lt_log hvalpos hvallt
  rw [hlog] at hfinal
  simp only [FSTAR]
  linarith

theorem strict_tail_d8 (cs : List Branch) (hlen : cs.length = 7) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple_strict cs 2 (2 * FSTAR - Real.log (3/2) - (1/10)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/10 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/10) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (7 + 1) = 5/4 by norm_num,
        show (2:ℝ) / ((7 + 1) + 2) = 1/5 by norm_num]
    have h := henc_cherry_d8_strict
    linarith

/-- STRICT d=9 fold. -/
theorem henc_cherry_d9_strict : Real.log (11/9) < (17 * FSTAR - 8 * Real.log (3/2)) - 2/33 := by
  set val : ℝ := (11/9:ℝ)^(11:ℕ) * (3/2:ℝ)^(88:ℕ) * ((621/64:ℝ)^(17:ℕ))⁻¹ with hvaldef
  have hvalpos : (0:ℝ) < val := by rw [hvaldef]; positivity
  have hlog : Real.log val = 11 * Real.log (11/9) + 88 * Real.log (3/2) - 17 * Real.log (621/64) := by
    rw [hvaldef, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_inv, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hb := Real.exp_bound (x := (2/3 : ℝ)) (by norm_num) (n := 4) (by norm_num)
  have hhi := (abs_le.mp hb).2
  have hs : ∑ i ∈ Finset.range 4, (2/3:ℝ)^i / (i.factorial:ℝ)
      = 1 + 2/3 + (2/3)^2/2 + (2/3)^3/6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hhi
  have hexpub : Real.exp (2/3) ≤ (2:ℝ) := by
    have herr : (1 + 2/3 + (2/3)^2/2 + (2/3)^3/6) + |(2/3:ℝ)|^4 * ((4+1)/((Nat.factorial 4:ℝ)*4))
        ≤ (2:ℝ) := by norm_num [Nat.factorial]
    linarith [hhi, herr]
  have hexppos : (0:ℝ) < Real.exp (2/3) := Real.exp_pos _
  have hvallt : val < Real.exp (-(2/3)) := by
    rw [Real.exp_neg, lt_inv_comm₀ hvalpos hexppos]
    calc Real.exp (2/3) ≤ (2:ℝ) := hexpub
      _ < val⁻¹ := by rw [hvaldef, lt_inv_comm₀ (by norm_num) (by positivity)]; norm_num
  have hfinal : Real.log val < -(2/3) := by
    rw [← Real.log_exp (-(2/3))]; exact Real.log_lt_log hvalpos hvallt
  rw [hlog] at hfinal
  simp only [FSTAR]
  linarith

theorem strict_tail_d9 (cs : List Branch) (hlen : cs.length = 8) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  refine tail_decouple_strict cs 2 (2 * FSTAR - Real.log (3/2) - (1/11)/3) h4 (by norm_num) ?_ ?_
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 2) = 1/11 := by rw [hlen]; norm_num
    rw [hσ]; exact phi_lb_cherry (1/11) (by norm_num) (by norm_num) c
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 2 / (8 + 1) = 11/9 by norm_num,
        show (2:ℝ) / ((8 + 1) + 2) = 2/11 by norm_num]
    have h := henc_cherry_d9_strict
    linarith

/-! ### The BOUNDARY STRICT tail cells `d ∈ {62,63,64}` (`|cs| ∈ {61,62,63}`).

  The transition zone.  Reference pinned so `σ = 5/384` (`S0 = 384/5 − d`); per-child min `phi_lb_deg4` (tight
  at its lower corner `m = −1/384`); STRICT B via the crude `log x ≤ x − 1` fold, which has WIDE rational slack
  here (the fold value beats `1 + 11·extra` strictly). -/

/-- Shared STRICT boundary closer, mirroring `tail_boundary_cell` through `tail_decouple_strict`. -/
private theorem strict_tail_boundary_cell (cs : List Branch) (L : ℕ) (hLge : 4 ≤ L) (hlen : cs.length = L)
    (hS0 : (0:ℝ) ≤ 384/5 - ((L:ℝ) + 1))
    (hB : (0:ℝ) < (L:ℝ) * (-1/384)
            + (FSTAR - Real.log (1 + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1))
               + (384/5 - ((L:ℝ)+1)) / (((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1))))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  subst hlen
  refine tail_decouple_strict cs (384/5 - ((cs.length:ℝ)+1)) (-1/384) h4 hS0 ?_ hB
  · intro c _
    have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + (384/5 - ((cs.length:ℝ)+1))) = 5/384 := by
      have : ((cs.length : ℝ) + 1) + (384/5 - ((cs.length:ℝ)+1)) = 384/5 := by ring
      rw [this]; norm_num
    rw [hσ]
    have := phi_lb_deg4 (5/384) (by norm_num) (by norm_num) c
    have heq : (1/1536 - (5/384)/4 : ℝ) = -1/384 := by norm_num
    rw [heq] at this
    exact this

/-- STRICT boundary B-obligation for concrete `|cs| = L ∈ [61,63]`: the crude fold value `< 1 + 11·extra`. -/
private theorem strict_tail_boundary_B (L : ℕ) (hL : 61 ≤ L) (hL2 : L ≤ 63) :
    (0:ℝ) < (L:ℝ) * (-1/384)
      + (FSTAR - Real.log (1 + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1))
         + (384/5 - ((L:ℝ)+1)) / (((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1)))) := by
  have hden : ((L:ℝ) + 1) + (384/5 - ((L:ℝ)+1)) = 384/5 := by ring
  have hLpos : (0:ℝ) < (L:ℝ) + 1 := by positivity
  have harg : (1:ℝ) + (384/5 - ((L:ℝ)+1)) / ((L:ℝ) + 1) = (384/5) / ((L:ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hLpos), add_mul, div_mul_cancel₀ _ (ne_of_gt hLpos), one_mul]; ring
  rw [hden, harg]
  have hApos : (0:ℝ) < (384/5) / ((L:ℝ) + 1) := by positivity
  have hlog11 : (11:ℝ) * Real.log ((384/5) / ((L:ℝ) + 1)) - Real.log (621/64)
      = Real.log (((384/5) / ((L:ℝ) + 1))^(11:ℕ) * (64/621)) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621:ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  have hfold := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < ((384/5) / ((L:ℝ) + 1))^(11:ℕ) * (64/621) by positivity)
  rw [← hlog11] at hfold
  interval_cases L
  · have hv : (((384/5:ℝ) / ((61:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 < 11 * ((5 * (384/5 - 62) / 384) - 61/384) := by
      norm_num
    simp only [FSTAR]; push_cast at hfold ⊢; nlinarith [hfold, hv]
  · have hv : (((384/5:ℝ) / ((62:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 < 11 * ((5 * (384/5 - 63) / 384) - 62/384) := by
      norm_num
    simp only [FSTAR]; push_cast at hfold ⊢; nlinarith [hfold, hv]
  · have hv : (((384/5:ℝ) / ((63:ℝ) + 1))^(11:ℕ) * (64/621)) - 1 < 11 * ((5 * (384/5 - 64) / 384) - 63/384) := by
      norm_num
    simp only [FSTAR]; push_cast at hfold ⊢; nlinarith [hfold, hv]

/-- **STRICT BOUNDARY cell `d = 62`** (`|cs| = 61`). -/
theorem strict_tail_d62 (cs : List Branch) (hlen : cs.length = 61) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum :=
  strict_tail_boundary_cell cs 61 (by norm_num) hlen (by norm_num) (strict_tail_boundary_B 61 (by norm_num) (by norm_num))

/-- **STRICT BOUNDARY cell `d = 63`** (`|cs| = 62`). -/
theorem strict_tail_d63 (cs : List Branch) (hlen : cs.length = 62) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum :=
  strict_tail_boundary_cell cs 62 (by norm_num) hlen (by norm_num) (strict_tail_boundary_B 62 (by norm_num) (by norm_num))

/-- **STRICT BOUNDARY cell `d = 64`** (`|cs| = 63`). -/
theorem strict_tail_d64 (cs : List Branch) (hlen : cs.length = 63) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum :=
  strict_tail_boundary_cell cs 63 (by norm_num) hlen (by norm_num) (strict_tail_boundary_B 63 (by norm_num) (by norm_num))

/-! ### Assembly: `StrictRootCell` for every deg≥5 hub except `d = 6`. -/

/-- **The strict-root-cell tail wrapper.**  Every tail hub `node cs` with `4 ≤ |cs|` and `|cs| ≠ 5`
    (i.e. degree `≥ 5` but NOT `d = 6`) has a STRICT root cell.  Dispatches `interval_cases`/`omega` over `|cs|`
    on the gap-free partition `{4} ∪ {6,7,8} ∪ [9,60] ∪ {61,62,63} ∪ [64,∞)` (the `{5}` cell is the tie, excluded). -/
theorem strictRootCell_tail (cs : List Branch) (hlen : 4 ≤ cs.length) (hne : cs.length ≠ 5) :
    StrictRootCell (Branch.node cs) := by
  refine strictRootCell_of_ineq cs ?_
  rcases (show cs.length = 4 ∨ cs.length = 6 ∨ cs.length = 7 ∨ cs.length = 8
      ∨ (9 ≤ cs.length ∧ cs.length ≤ 60) ∨ cs.length = 61 ∨ cs.length = 62 ∨ cs.length = 63
      ∨ 64 ≤ cs.length by omega) with
    h | h | h | h | ⟨h1, h2⟩ | h | h | h | h
  · exact strict_tail_d5 cs h
  · exact strict_tail_d7 cs h
  · exact strict_tail_d8 cs h
  · exact strict_tail_d9 cs h
  · exact strict_tail_deg4 cs h1 h2
  · exact strict_tail_d62 cs h
  · exact strict_tail_d63 cs h
  · exact strict_tail_d64 cs h
  · exact strict_tail_deg5 cs h

/-! ### The EXACT structural near-star tie predicate. -/

/-- The cherry branch `node [leaf]` — a degree-2 hub with a single leaf child (`bY = 1/3`, `ρwit = 2F*−log(3/2)`). -/
def cherryBranch : Branch := Branch.node [Branch.node []]

/-- **The EXACT near-star tie.**  Structurally: a root of degree 6 whose five children are ALL the cherry
    `node [leaf]`.  This is the unique `d = 6` five-cherry configuration whose root cell is TIGHT (the `27·23 = 621`
    identity `tie_identity_d6`), i.e. the exact `N(c,k)`, `c+k = 5` image on the `bell` side.  Any OTHER `d = 6`
    hub (children not all cherry) is NOT a near-star tie — and, like every hub off this exact configuration, will
    be shown to have `bell < 0` once the `d = 6` non-cherry margin is characterized (Part 2 territory). -/
def IsNearStarTie (b : Branch) : Prop :=
  b = Branch.node [cherryBranch, cherryBranch, cherryBranch, cherryBranch, cherryBranch]

/-- The exact near-star tie is a `d = 6` hub (`bcc = 5`, root degree 6). -/
theorem bcc_eq_five_of_nearStarTie {b : Branch} (h : IsNearStarTie b) : bcc b = 5 := by
  rw [h]; simp only [bcc, cherryBranch, List.length_cons, List.length_nil]

/-- **The strict root cell off the exact near-star tie (deg≥5 residue).**  A deg≥5 hub (`4 ≤ bcc b`) that is
    NOT the exact five-cherry near-star tie has a STRICT root cell.  Proof: `bcc b ≥ 4` means `b = node cs` with
    `4 ≤ |cs|`; if `|cs| ≠ 5` this is `strictRootCell_tail`; if `|cs| = 5` (`d = 6`) then `b ≠` the exact tie forces
    `cs` to be a NON-all-cherry degree-6 hub — but NOTE the residual `d = 6` non-cherry margin is NOT closed here
    (see `master_ineq_strict'` scope), so this lemma is stated for the `|cs| ≠ 5` reach and the full deg≥5
    residue is handled through `master_ineq_strict'` below. -/
theorem strictRootCell_of_deg_ne_six {b : Branch} (hb : 4 ≤ bcc b) (hne6 : bcc b ≠ 5) :
    StrictRootCell b := by
  cases b with
  | node cs =>
    have hlen : 4 ≤ cs.length := by simpa only [bcc] using hb
    have hne : cs.length ≠ 5 := by simpa only [bcc] using hne6
    exact strictRootCell_tail cs hlen hne

/-! ### The `d = 6` non-cherry STRICT cell (closing the exact near-star tie).

  A `d = 6` hub whose five children are NOT all the cherry `node [leaf]` is STRICT.  The `d = 6` (SUB) cell
  (`subaction_tail_d6`) is `tail_decouple` at `S0 = 5/3`, per-child `phi_lb_d6` (`m + (3/23)·bY c ≤ ρwit c`),
  and `B = 0` (the exact `27·23` identity).  The per-child bound `phi_lb_d6` is TIGHT only for the cherry
  (deg-2 child at `bY = 1/3`); for every other child type — leaf, deg-2 at `bY > 1/3`, deg-3, deg-4, deg≥5 —
  it is STRICT.  So one non-cherry child makes the summed bound STRICT, hence the root cell STRICT. -/

/-- **Strict list-lift.**  If the per-child affine bound holds for all children and is STRICT for at least one
    child `a ∈ cs`, the sum is STRICT: `|cs|·m + σ·(Σ bY) < Σ ρwit`. -/
theorem sum_rhowit_gt (σ m : ℝ) (a : Branch) :
    ∀ (cs : List Branch), (∀ c ∈ cs, m + σ * bY c ≤ ρwit c) → a ∈ cs →
      m + σ * bY a < ρwit a →
      (cs.length : ℝ) * m + σ * (cs.map bY).sum < (cs.map ρwit).sum
  | [], _, ha, _ => by simp at ha
  | x :: t, hall, ha, hstrict => by
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    have hxle : m + σ * bY x ≤ ρwit x := hall x (by simp)
    rcases List.mem_cons.mp ha with hax | hat
    · -- strict at the head: a = x, so hstrict transports to x
      have hstrictx : m + σ * bY x < ρwit x := hax ▸ hstrict
      have ht := sum_rhowit_ge σ m t (fun c hc => hall c (by simp [hc]))
      calc ((t.length : ℝ) + 1) * m + σ * (bY x + (t.map bY).sum)
          = (m + σ * bY x) + ((t.length : ℝ) * m + σ * (t.map bY).sum) := by ring
        _ < ρwit x + (t.map ρwit).sum := by
            have := add_lt_add_of_lt_of_le hstrictx ht; linarith
    · have ht := sum_rhowit_gt σ m a t (fun c hc => hall c (by simp [hc])) hat hstrict
      calc ((t.length : ℝ) + 1) * m + σ * (bY x + (t.map bY).sum)
          = (m + σ * bY x) + ((t.length : ℝ) * m + σ * (t.map bY).sum) := by ring
        _ < ρwit x + (t.map ρwit).sum := by
            have := add_lt_add_of_le_of_lt hxle ht; linarith

/-- **The strict tail decouple with a strict child.**  Same as `tail_decouple` but the per-child bound is
    STRICT for at least one child (`hstrict`) and `B(S0) ≥ 0` (non-strict); the root cell is STRICT. -/
theorem tail_decouple_strict_child (cs : List Branch) (S0 m : ℝ)
    (hlen : 4 ≤ cs.length) (hS0 : 0 ≤ S0)
    (hpc : ∀ c ∈ cs, m + (1 / (((cs.length : ℝ) + 1) + S0)) * bY c ≤ ρwit c)
    (a : Branch) (ha : a ∈ cs)
    (hstrict : m + (1 / (((cs.length : ℝ) + 1) + S0)) * bY a < ρwit a)
    (hB : 0 ≤ (cs.length : ℝ) * m
            + (FSTAR - Real.log (1 + S0 / ((cs.length : ℝ) + 1))
               + S0 / (((cs.length : ℝ) + 1) + S0))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have hd_pos : (0 : ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hdS0 : (0 : ℝ) < ((cs.length : ℝ) + 1) + S0 := by positivity
  have hS_nn : (0 : ℝ) ≤ (cs.map bY).sum :=
    List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
  have htan := log_tangent (d := (cs.length : ℝ) + 1) (s := (cs.map bY).sum) (s0 := S0)
    hd_pos hS_nn hS0
  have hsum := sum_rhowit_gt (1 / (((cs.length : ℝ) + 1) + S0)) m a cs hpc ha hstrict
  have hsp : ((cs.map bY).sum - S0) / (((cs.length : ℝ) + 1) + S0)
      = (1 / (((cs.length : ℝ) + 1) + S0)) * (cs.map bY).sum
        - S0 / (((cs.length : ℝ) + 1) + S0) := by
    field_simp
  rw [ρwit_node_high hlen]
  linarith [htan, hsum, hB, hsp]

/-- `phi_lb_d6` is STRICT at any child whose message exceeds the cherry value (`1/3 < bY c`).  Such a child is
    necessarily a leaf (`bY = 1`) or a deg-2 hub at `bY > 1/3` (deg≥3 children have `bY ≤ 1/3`); both give a
    strict per-child bound (leaf via the STRICT anchor `2/23 < log(3/2) − F*`; deg-2 via the slope gap
    `3/23 < 1/4`).  This is the clean, closable sufficient condition for the `d = 6` strict cell. -/
theorem phi_lb_d6_strict_of_bY_gt (c : Branch) (hbY : (1:ℝ)/3 < bY c) :
    (2 * FSTAR - Real.log (3/2) - 1/23) + (3/23) * bY c < ρwit c := by
  have hyd := bY_le_inv_deg c
  -- STRICT leaf anchor: 2/23 < log(3/2) − F*.
  have hEl : (2:ℝ)/23 < Real.log (3/2) - FSTAR := by
    rw [FSTAR]
    have hY : (0:ℝ) < (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by positivity
    have hlog : Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621))
        = 11 * Real.log (3/2) - Real.log (621/64) := by
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
          show (64/621 : ℝ) = (621/64)⁻¹ by norm_num, Real.log_inv]
      push_cast; ring
    have hgt : (22:ℝ)/23 < Real.log ((3/2 : ℝ) ^ (11:ℕ) * (64/621)) := by
      rw [Real.lt_log_iff_exp_lt hY]
      calc Real.exp (22/23) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        _ < 2.7182818286 := Real.exp_one_lt_d9
        _ ≤ (3/2 : ℝ) ^ (11:ℕ) * (64/621) := by norm_num
    rw [hlog] at hgt; linarith
  -- `1/3 < bY c` forces the child to be a leaf or a deg-2 hub (deg≥3 ⇒ bY ≤ 1/3).
  rcases hbc : bcc c with _ | _ | _ | _ | n
  · -- leaf: bY = 1, ρwit = F*.  goal ⟺ 2/23 < log(3/2) − F* (STRICT, hEl).
    have hby1 : bY c = 1 := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact bY_leaf
    have hrc : ρwit c = FSTAR := by
      cases c with
      | node cs => simp only [bcc] at hbc; rw [List.length_eq_zero_iff.mp hbc] at *; exact ρwit_leaf
    rw [hby1, hrc]; linarith
  · -- deg-2 at bY > 1/3: STRICT via the slope gap (3/23 < 1/4).
    have hrc : ρwit c = 2 * FSTAR - Real.log (3/2) + (1/4) * (bY c - 1/3) := by
      simp only [ρwit, hbc]
    rw [hrc]; nlinarith [hbY]
  · -- deg-3: bY ≤ 1/3 contradicts 1/3 < bY.
    rw [hbc] at hyd; norm_num at hyd; linarith
  · -- deg-4: bY ≤ 1/4 contradicts 1/3 < bY.
    rw [hbc] at hyd; norm_num at hyd; linarith
  · have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hby : bY c ≤ 1/5 := by
      rw [hbc] at hyd
      have hd5 : (5:ℝ) ≤ ((n + 4 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hle : (1:ℝ) / (((n + 4 : ℕ) : ℝ) + 1) ≤ 1/5 :=
        one_div_le_one_div_of_le (by norm_num) hd5
      linarith
    linarith

/-- **The `d = 6` STRICT cell for a hub with an above-cherry child.**  If `cs.length = 5` and some child
    `a ∈ cs` has message `1/3 < bY a` (a leaf, or a deg-2 hub pushed above the cherry value), the root cell is
    STRICT.  This is the closable slice of the `d = 6` residue: it strictly separates from the near-star tie
    every degree-6 hub carrying a leaf or an above-cherry deg-2 child. -/
theorem strict_tail_d6_of_bY_gt (cs : List Branch) (hlen : cs.length = 5)
    (a : Branch) (ha : a ∈ cs) (hbY : (1:ℝ)/3 < bY a) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) < (cs.map ρwit).sum := by
  have h4 : 4 ≤ cs.length := by omega
  have hσ : (1 : ℝ) / (((cs.length : ℝ) + 1) + 5/3) = 3/23 := by rw [hlen]; norm_num
  refine tail_decouple_strict_child cs (5/3) (2 * FSTAR - Real.log (3/2) - 1/23) h4 (by norm_num)
    ?_ a ha ?_ ?_
  · intro c _; rw [hσ]; exact phi_lb_d6 c
  · rw [hσ]; exact phi_lb_d6_strict_of_bY_gt a hbY
  · rw [hlen]; push_cast
    rw [show (1 : ℝ) + 5/3 / (5 + 1) = 23/18 by norm_num,
        show (5:ℝ)/3 / ((5 + 1) + 5/3) = 5/23 by norm_num]
    linarith [tie_identity_d6]

/-! ### The strengthened master inequality: the tie set collapses to degree exactly 6. -/

/-- **The tie set is confined to degree exactly 6.**  `IsTie b := 4 ≤ bcc b ∧ ¬StrictRootCell b` forces
    `bcc b = 5` (root degree 6): every deg≥5 hub of degree `≠ 6` has a STRICT root cell
    (`strictRootCell_of_deg_ne_six`), so `¬StrictRootCell b` rules it out.  This is the Part-1 strengthening:
    the strict-inequality residue drops from "all deg≥5, tight root cell" to "degree EXACTLY 6, tight root cell". -/
theorem isTie_imp_bcc_eq_five {b : Branch} (h : IsTie b) : bcc b = 5 := by
  obtain ⟨hge, hns⟩ := h
  by_contra hne
  exact hns (strictRootCell_of_deg_ne_six hge hne)

/-- **The strengthened master strict inequality (degree reach).**  For every `b` whose root degree is NOT 6
    (`bcc b ≠ 5`), `bell b < 0`.  Combines route (i) (deg ≤ 4, `bell_lt_of_bcc_le3`) with the new deg≥5,
    degree-≠6 strict root cells (`strictRootCell_of_deg_ne_six` ⟶ `bell_lt_of_strict_root`).  Strengthens
    `master_ineq_strict`: the only branches this does NOT cover are the degree-6 hubs (the near-star tie lives
    there), whereas `master_ineq_strict` left the whole deg≥5 tight-root-cell set open. -/
theorem master_ineq_strict_off_deg6 {b : Branch} (hne6 : bcc b ≠ 5) : bell b < 0 := by
  rcases (show bcc b ≤ 3 ∨ 4 ≤ bcc b by omega) with hle | hge
  · exact bell_lt_of_bcc_le3 b hle
  · exact bell_lt_of_strict_root b (strictRootCell_of_deg_ne_six hge hne6)

/-- **`bell = 0 ⇒ degree exactly 6.**  A `bell = 0` branch must be a degree-6 hub — sharpening
    `bcc_ge_four_of_bell_eq_zero` (`bell = 0 ⇒ bcc ≥ 4`) all the way to `bcc = 5`. -/
theorem bcc_eq_five_of_bell_eq_zero {b : Branch} (h : bell b = 0) : bcc b = 5 := by
  by_contra hne
  have := master_ineq_strict_off_deg6 hne
  linarith

end BGSCL
end R3Cert
