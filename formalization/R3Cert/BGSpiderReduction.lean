/-
  BG spider reduction, part B1: the high-degree case (2026-09-24).

  Claim under study: for every tree T on n vertices there is a two-level spider (a centre carrying
  leaves, cherries and arms, where an arm is a vertex all of whose other neighbours are cherries) on n
  vertices with `pi >= pi(T)`.

  This file proves, with no `sorry` and only the standard axioms:

  * `phiRoot_eq` — the Lagrangian identity at a root with child list `cs` (`k = |cs|`):
      `log pi(cs) - (n-1) F* = sum_i bell b_i + log(1 + (sum_i y_i)/k)`.
  * `phiRoot_le_tangent` — for every `t > 0`, with price `mu = 1/(k t)`:
      `log pi(cs) - (n-1) F* <= log t + 1/t - 1 + sum_i V_mu(b_i)`.
  * `armEnv_interp` — the arm-envelope statement `ArmEnv mu delta`
      (`V_mu(b) <= 3mu/23` for every branch, and `<= 3mu/23 - delta` off the atoms) is affine in `mu`,
      so the two endpoints `mu = 0` and `mu = mu0` give it on all of `[0, mu0]`.
  * `phiRoot_le_of_armEnv` — HIGH-DEGREE ROOT BOUND: if `ArmEnv` holds on `[0, 23/624]` and the root has
      `k >= 24` children, one of which is not an atom, then `log pi - (n-1) F* <= log(26/23) - delta`.
  * `phiRoot_spider_ge` — UNCONDITIONAL spider lower bound: the spider with `a` arms of 5 cherries and `q`
      arms of 4 cherries has `log pi - (n-1) F* >= log(26/23) + q * bell(arm_4)`, and
      `bell(arm_4) >= -1/960` (`bell_arm4_ge`).
  * `spider_dominates_highDegree` — MAIN CONDITIONAL THEOREM: under `ArmEnv` on `[0, 23/624]` with
      `delta = 1/75`, every root list with `k >= 24` children, one of them a non-atom, and total size
      `n - 1 >= 90` is STRICTLY beaten by a spider (arms of 5 and 4 cherries) of the same size.
  * `armEnv_of_cells` — the arm envelope REDUCED to three explicit per-vertex cell families
      (`AtomCell0`, `SurchargeCell`, `AtomCellMu`), using the proven subaction `isSubaction_ρwit`,
      `bg_ceiling` and `bell_add_ρwit_le`.  The three cell families are NOT proved here (they are the
      crisp remaining obligations; numerically validated in `proof/verification/bg_spider_reduction.py`).
  * `spider_dominates_highDegree_of_cells` — the main theorem with `ArmEnv` replaced by the three cells.
  * `atom_bV_le` — every atom satisfies the arm envelope on `[0, 23/624]` (rational log enclosures);
      hence the atom cells hold outright for `K >= 23` children and the surcharge cell for degree `>= 8`
      (`atomCell0_of_core`, `atomCellMu_of_core`, `surchargeCell_of_core`).
  * `spider_dominates_highDegree_of_cores` — the main theorem conditional only on the three FINITE-DEGREE
      cores `AtomCell0Core (1/75)` (`<= 22` atom children), `AtomCellMuCore (23/624) (1/75)` (`3..22` atom
      children) and `SurchargeCore (23/624)` (`3..6` arbitrary children, entering only via `(bcc, y)`).

  The three cores are PROVED in `BGSpiderCells.lean` (`spider_dominates_highDegree_uncond`), so the
  high-degree case is unconditional.

  What this does NOT cover: trees whose maximum degree is `<= 23` (the root-degree `k <= 23` case) for
  `n > 100`.  See `proof/docs/BG_SPIDER_REDUCTION_2026-09-24.md`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionDispatch
import R3Cert.BGSCLSubactionStrict
import R3Cert.BGSCLSubactionTailDecouple

namespace R3Cert
namespace BGSCL

open Real

/-! ### Atoms, spiders and the root objective. -/

/-- `arm_j`: a vertex whose `j` children are all cherries (`armB 0` is the leaf). -/
def armB (j : ℕ) : Branch := Branch.node (List.replicate j cherry)

/-- The atoms: leaf (`armB 0`), cherry, and the arms `armB j`, `j ≥ 1`. -/
def IsAtom (b : Branch) : Prop := b = cherry ∨ ∃ j, b = armB j

/-- The tree objective at a root with child list `cs` (`k = |cs|`):
    `pi = (∏ T_c) · (1 + (Σ y_c)/k)`. -/
noncomputable def piRoot (cs : List Branch) : ℝ :=
  (cs.map (fun c => (cav c).2)).prod * (1 + (cs.map bY).sum / (cs.length : ℝ))

/-- The Lagrangian objective `log pi − (n−1)·F*`, `n − 1 = bsizeList cs`. -/
noncomputable def phiRoot (cs : List Branch) : ℝ :=
  Real.log (piRoot cs) - (bsizeList cs : ℝ) * FSTAR

/-- The spider with `a` arms of five cherries and `q` arms of four cherries. -/
def spiderB (a q : ℕ) : List Branch := List.replicate a (armB 5) ++ List.replicate q (armB 4)

theorem sumY_nonneg (cs : List Branch) : 0 ≤ (cs.map bY).sum := by
  apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c

theorem prodT_pos (cs : List Branch) : 0 < (cs.map (fun c => (cav c).2)).prod := by
  apply List.prod_pos; intro x hx; rw [List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx; exact btotal_pos c

theorem piRoot_pos (cs : List Branch) : 0 < piRoot cs := by
  unfold piRoot
  have h1 := prodT_pos cs
  have h2 : 0 ≤ (cs.map bY).sum / (cs.length : ℝ) := div_nonneg (sumY_nonneg cs) (Nat.cast_nonneg _)
  exact mul_pos h1 (by linarith)

/-- **The Lagrangian identity at a root.**
    `log pi(cs) − (n−1)F* = Σ bell + log(1 + (Σ y)/k)`. -/
theorem phiRoot_eq (cs : List Branch) :
    phiRoot cs = (cs.map bell).sum + Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) := by
  have hP := prodT_pos cs
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / (cs.length : ℝ) := by
    have : 0 ≤ (cs.map bY).sum / (cs.length : ℝ) := div_nonneg (sumY_nonneg cs) (Nat.cast_nonneg _)
    linarith
  have hlog : Real.log (piRoot cs)
      = (cs.map (fun c => Real.log (cav c).2)).sum
        + Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) := by
    unfold piRoot
    rw [Real.log_mul hP.ne' hfac.ne', log_list_prod _ ?_, List.map_map]
    · rfl
    · intro x hx; rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact btotal_pos c
  unfold phiRoot
  rw [hlog, sum_map_bell, bsizeList_eq_sum, cast_sum_map_bsize]
  ring

/-- `log u ≤ log t + u/t − 1` for `u, t > 0` (the tangent of `log` at `t`). -/
theorem log_le_tangent_at {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    Real.log u ≤ Real.log t + u / t - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu ht)
  rw [Real.log_div hu.ne' ht.ne'] at h
  linarith

/-- `Σ bV μ = Σ bell + μ Σ y`. -/
theorem sum_map_bV (μ : ℝ) (cs : List Branch) :
    (cs.map (bV μ)).sum = (cs.map bell).sum + μ * (cs.map bY).sum := by
  induction cs with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      unfold bV; ring

/-- **The tangent bound at a root.**  For `t > 0` and price `μ = 1/(k t)` (`k = |cs| ≥ 1`):
    `log pi − (n−1)F* ≤ log t + 1/t − 1 + Σ_i V_μ(b_i)`. -/
theorem phiRoot_le_tangent (cs : List Branch) (hcs : cs ≠ []) {t : ℝ} (ht : 0 < t) :
    phiRoot cs ≤ Real.log t + 1 / t - 1
      + (cs.map (bV (1 / ((cs.length : ℝ) * t)))).sum := by
  have hk : (0:ℝ) < (cs.length : ℝ) := by
    have : 0 < cs.length := List.length_pos_of_ne_nil hcs
    exact_mod_cast this
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / (cs.length : ℝ) := by
    have : 0 ≤ (cs.map bY).sum / (cs.length : ℝ) := div_nonneg (sumY_nonneg cs) hk.le
    linarith
  have htan := log_le_tangent_at hfac ht
  rw [phiRoot_eq, sum_map_bV]
  have hsplit : (1 + (cs.map bY).sum / (cs.length : ℝ)) / t
      = 1 / t + 1 / ((cs.length : ℝ) * t) * (cs.map bY).sum := by
    field_simp
  rw [hsplit] at htan
  linarith

/-! ### The arm envelope and its affine interpolation in `μ`. -/

/-- **The arm-envelope statement at price `μ`, with non-atom gap `δ`.**  Every branch has
    `V_μ(b) ≤ V_μ(arm_5) = 3μ/23`, and every non-atom branch is below by at least `δ`.
    At `μ = 0` the first half is `bg_ceiling`. -/
def ArmEnv (μ δ : ℝ) : Prop :=
  (∀ b, bV μ b ≤ μ * (3 / 23)) ∧ (∀ b, ¬ IsAtom b → bV μ b ≤ μ * (3 / 23) - δ)

/-- **Interpolation.**  `ArmEnv` at `μ = 0` and at `μ = μ0 > 0` gives it on `[0, μ0]`
    (`V_μ(b) − 3μ/23 = bell b + μ (y_b − 3/23)` is affine in `μ`). -/
theorem armEnv_interp {μ0 δ : ℝ} (hμ0 : 0 < μ0) (h0 : ArmEnv 0 δ) (h1 : ArmEnv μ0 δ)
    {μ : ℝ} (hμ : 0 ≤ μ) (hμle : μ ≤ μ0) : ArmEnv μ δ := by
  set θ := μ / μ0 with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hμ hμ0.le
  have hθ1 : θ ≤ 1 := (div_le_one hμ0).mpr hμle
  have hμeq : μ = θ * μ0 := by rw [hθ]; field_simp
  have key : ∀ b, bV μ b - μ * (3 / 23)
      = (1 - θ) * (bV 0 b - 0 * (3 / 23)) + θ * (bV μ0 b - μ0 * (3 / 23)) := by
    intro b; unfold bV; rw [hμeq]; ring
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · have e0 := h0.1 b; have e1 := h1.1 b
    have := key b
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr e0), mul_nonneg hθ0 (sub_nonneg.mpr e1)]
  · have e0 := h0.2 b hb; have e1 := h1.2 b hb
    have := key b
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr e0), mul_nonneg hθ0 (sub_nonneg.mpr e1)]

/-- A list sum where every term is `≤ g` and one member is `≤ g − δ` is `≤ |l|·g − δ`. -/
theorem sum_le_of_one_gap {f : Branch → ℝ} {g δ : ℝ} :
    ∀ (l : List Branch), (∀ c ∈ l, f c ≤ g) → (∃ c ∈ l, f c ≤ g - δ) →
      (l.map f).sum ≤ (l.length : ℝ) * g - δ
  | [], _, ⟨c, hc, _⟩ => by simp at hc
  | a :: t, hall, ⟨c, hc, hcδ⟩ => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have hsum_le : ∀ (l : List Branch), (∀ c ∈ l, f c ≤ g) → (l.map f).sum ≤ (l.length : ℝ) * g := by
        intro l hl
        induction l with
        | nil => simp
        | cons x r ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
            have hx := hl x (List.mem_cons.mpr (Or.inl rfl))
            have hr := ih (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
            linarith
      rcases List.mem_cons.mp hc with rfl | hct
      · have ht := hsum_le t (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))
        linarith
      · have ha := hall a (List.mem_cons.mpr (Or.inl rfl))
        have ht := sum_le_of_one_gap t (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy))) ⟨c, hct, hcδ⟩
        linarith

/-- **High-degree root bound.**  If `ArmEnv μ δ` holds for every `μ ∈ [0, 23/624]`, a root with `k ≥ 24`
    children, at least one of which is not an atom, has `log pi − (n−1)F* ≤ log(26/23) − δ`.
    (Tangent at `t = 26/23`, price `μ = 23/(26k) ≤ 23/624`.) -/
theorem phiRoot_le_of_armEnv {δ : ℝ} (hEnv : ∀ μ, 0 ≤ μ → μ ≤ 23 / 624 → ArmEnv μ δ)
    (cs : List Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c) :
    phiRoot cs ≤ Real.log (26 / 23) - δ := by
  have hcs : cs ≠ [] := by
    intro h; rw [h] at hk; simp at hk
  have hkR : (24:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (cs.length : ℝ) := by linarith
  set μ := 1 / ((cs.length : ℝ) * (26 / 23)) with hμ
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have hμle : μ ≤ 23 / 624 := by
    rw [hμ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE := hEnv μ hμ0 hμle
  have htan := phiRoot_le_tangent cs hcs (t := 26 / 23) (by norm_num)
  have hsum := sum_le_of_one_gap (f := bV μ) (g := μ * (3 / 23)) (δ := δ) cs
    (fun c _ => hE.1 c) (by obtain ⟨c, hc, hnc⟩ := hna; exact ⟨c, hc, hE.2 c hnc⟩)
  have hkμ : (cs.length : ℝ) * (μ * (3 / 23)) = 3 / 26 := by
    rw [hμ]; field_simp
  have h1t : (1:ℝ) / (26 / 23) = 23 / 26 := by norm_num
  rw [h1t] at htan
  nlinarith [htan, hsum, hkμ]

/-! ### Arms: closed forms and the unconditional spider lower bound. -/

theorem bsize_cherry : bsize cherry = 2 := by
  simp [cherry, bsize, bsizeList]

theorem bsizeList_replicate (n : ℕ) (b : Branch) :
    bsizeList (List.replicate n b) = n * bsize b := by
  rw [bsizeList_eq_sum, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem bsize_armB (j : ℕ) : bsize (armB j) = 2 * j + 1 := by
  simp only [armB, bsize, bsizeList_replicate, bsize_cherry]; ring

theorem bsizeList_append (l m : List Branch) : bsizeList (l ++ m) = bsizeList l + bsizeList m := by
  rw [bsizeList_eq_sum, bsizeList_eq_sum, bsizeList_eq_sum, List.map_append, List.sum_append]

theorem bsizeList_spiderB (a q : ℕ) : bsizeList (spiderB a q) = 11 * a + 9 * q := by
  rw [spiderB, bsizeList_append, bsizeList_replicate, bsizeList_replicate, bsize_armB, bsize_armB]
  ring

theorem bY_armB (j : ℕ) : bY (armB j) = 3 / (4 * (j : ℝ) + 3) := by
  rw [armB, bY_node, List.map_replicate, List.sum_replicate, bY_cherry, List.length_replicate,
    nsmul_eq_mul]
  have : (0:ℝ) < 4 * (j : ℝ) + 3 := by positivity
  field_simp
  ring

theorem bell_armB (j : ℕ) :
    bell (armB j) = (j : ℝ) * (Real.log (3 / 2) - 2 * FSTAR)
      + (Real.log ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3)) - FSTAR) := by
  rw [armB, bell_node, List.map_replicate, List.sum_replicate, List.map_replicate, List.sum_replicate,
    bell_cherry, bY_cherry, List.length_replicate, nsmul_eq_mul, nsmul_eq_mul]
  have harg : 1 + (j : ℝ) * (1 / 3) / ((j : ℝ) + 1) = (4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3) := by
    have : (0:ℝ) < (j : ℝ) + 1 := by positivity
    field_simp
    ring
  rw [harg]

/-- `11 F* = log(621/64)`. -/
theorem eleven_fstar : 11 * FSTAR = Real.log (621 / 64) := by
  rw [FSTAR]; ring

/-- `bell(arm_5) = 0` (the tie: `T(arm_5) = 621/64`). -/
theorem bell_arm5 : bell (armB 5) = 0 := by
  rw [bell_armB]
  have h : (5:ℝ) * Real.log (3 / 2) + Real.log ((4 * (5:ℝ) + 3) / (3 * 5 + 3)) = Real.log (621 / 64) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; norm_num
  push_cast at h ⊢
  have := eleven_fstar
  linarith

theorem bY_arm5 : bY (armB 5) = 3 / 23 := by rw [bY_armB]; norm_num
theorem bY_arm4 : bY (armB 4) = 3 / 19 := by rw [bY_armB]; norm_num

/-- `bell(arm_4) = log(513/80) − 9 F*`. -/
theorem bell_arm4_eq : bell (armB 4) = Real.log (513 / 80) - 9 * FSTAR := by
  rw [bell_armB]
  have h : (4:ℝ) * Real.log (3 / 2) + Real.log ((4 * (4:ℝ) + 3) / (3 * 4 + 3)) = Real.log (513 / 80) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; norm_num
  push_cast at h ⊢
  linarith

/-- **The arm-4 deficit is tiny:** `bell(arm_4) ≥ −1/960` (true value `≈ −0.0010264`).
    `−11·bell(arm_4) = log X`, `X = (621/64)^9 (80/513)^11 ≈ 1.01135`, and `log X ≤ X − 1 ≤ 11/960`. -/
theorem bell_arm4_ge : (-1 / 960 : ℝ) ≤ bell (armB 4) := by
  rw [bell_arm4_eq]
  have hX : (0:ℝ) < (621 / 64) ^ 9 * (80 / 513) ^ 11 := by positivity
  have hlog : Real.log ((621 / 64 : ℝ) ^ 9 * (80 / 513) ^ 11)
      = 9 * Real.log (621 / 64) - 11 * Real.log (513 / 80) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      show (80:ℝ) / 513 = (513 / 80)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  have hle := Real.log_le_sub_one_of_pos hX
  rw [hlog] at hle
  have hnum : (621 / 64 : ℝ) ^ 9 * (80 / 513) ^ 11 - 1 ≤ 11 / 960 := by norm_num
  have := eleven_fstar
  have hF : 9 * FSTAR = 9 / 11 * Real.log (621 / 64) := by rw [← this]; ring
  rw [hF]
  linarith

/-- **Unconditional spider lower bound.**  For `a + q ≥ 1`,
    `log pi(spider) − (n−1)F* ≥ log(26/23) + q·bell(arm_4)` (the mean message `≥ 3/23`). -/
theorem phiRoot_spider_ge (a q : ℕ) (haq : 1 ≤ a + q) :
    Real.log (26 / 23) + (q : ℝ) * bell (armB 4) ≤ phiRoot (spiderB a q) := by
  rw [phiRoot_eq]
  have hbell : ((spiderB a q).map bell).sum = (q : ℝ) * bell (armB 4) := by
    rw [spiderB, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      List.map_replicate, List.sum_replicate, bell_arm5, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hY : ((spiderB a q).map bY).sum = (a : ℝ) * (3 / 23) + (q : ℝ) * (3 / 19) := by
    rw [spiderB, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      List.map_replicate, List.sum_replicate, bY_arm5, bY_arm4, nsmul_eq_mul, nsmul_eq_mul]
  have hlen : ((spiderB a q).length : ℝ) = (a : ℝ) + (q : ℝ) := by
    rw [spiderB, List.length_append, List.length_replicate, List.length_replicate]; push_cast; ring
  rw [hbell, hY, hlen]
  have hk : (1:ℝ) ≤ (a : ℝ) + (q : ℝ) := by exact_mod_cast haq
  have hmean : (26 / 23 : ℝ) ≤ 1 + ((a : ℝ) * (3 / 23) + (q : ℝ) * (3 / 19)) / ((a : ℝ) + (q : ℝ)) := by
    rw [← sub_nonneg]
    have hq : (0:ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have : 1 + ((a : ℝ) * (3 / 23) + (q : ℝ) * (3 / 19)) / ((a : ℝ) + (q : ℝ)) - 26 / 23
        = (q : ℝ) * (3 / 19 - 3 / 23) / ((a : ℝ) + (q : ℝ)) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ (by linarith); nlinarith
  have := Real.log_le_log (by norm_num) hmean
  linarith

/-! ### The main conditional theorem (high degree). -/

/-- **Spider domination in the high-degree case, conditional on the arm envelope.**  If `ArmEnv μ (1/75)`
    holds for every `μ ∈ [0, 23/624]`, then every root list with `k ≥ 24` children, at least one of which
    is not an atom, and total size `n − 1 ≥ 90`, is STRICTLY beaten by the spider with
    `q = (5(n−1)) mod 11` arms of four cherries and `a = ((n−1) − 9q)/11` arms of five cherries. -/
theorem spider_dominates_highDegree
    (hEnv : ∀ μ, 0 ≤ μ → μ ≤ 23 / 624 → ArmEnv μ (1 / 75))
    (cs : List Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (hN : 90 ≤ bsizeList cs) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  set N := bsizeList cs with hNdef
  refine ⟨(N - 9 * ((5 * N) % 11)) / 11, (5 * N) % 11, by omega, ?_, ?_⟩
  · rw [bsizeList_spiderB]; omega
  · have hsz : bsizeList (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) = N := by
      rw [bsizeList_spiderB]; omega
    have haq : 1 ≤ (N - 9 * ((5 * N) % 11)) / 11 + (5 * N) % 11 := by omega
    have hq10 : (((5 * N) % 11 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : (5 * N) % 11 ≤ 10)
    have hlo := phiRoot_spider_ge _ _ haq
    have hup := phiRoot_le_of_armEnv hEnv cs hk hna
    have h4 := bell_arm4_ge
    have h4' : (-1 / 96 : ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) * bell (armB 4) := by
      have hqnn : (0:ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hlt : phiRoot cs < phiRoot (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) := by
      linarith
    unfold phiRoot at hlt
    rw [hsz, ← hNdef] at hlt
    exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

/-! ### Reduction of the arm envelope to three per-vertex cell families.

  The witness `ρwit` (degree/message keyed; `isSubaction_ρwit`, `bell_add_ρwit_le`) already gives
  `bell b ≤ −ρwit b`.  Three explicit per-vertex families upgrade this to the arm envelope:

  * `AtomCell0 δ`: a non-atom vertex all of whose children are atoms has `bell + ρwit ≤ −δ`.
  * `SurchargeCell μ`: at a vertex of degree `≥ 4`, the subaction inequality survives the surcharge
    `μ (y − 3/23)` (it only bites when `y > 3/23`, i.e. `d + Σy < 23/3`).
  * `AtomCellMu μ δ`: a non-atom vertex of degree `≥ 4` with only atom children has `V_μ ≤ 3μ/23 − δ`.

  All three are NOT proved here; they are validated numerically (min gap `0.014520` for `AtomCell0`,
  attained at five cherries + one arm of four; `SurchargeCell (23/624)` holds on the class relaxation
  with tightest margins `0` (arm_5 tie) and `1.4e-5` (arm_4); `AtomCellMu (23/624)` min gap `0.015151`). -/

/-- Non-atom vertex with only atom children: `bell + ρwit ≤ −δ`. -/
def AtomCell0 (δ : ℝ) : Prop :=
  ∀ cs : List Branch, (∀ c ∈ cs, IsAtom c) → ¬ IsAtom (Branch.node cs) →
    bell (Branch.node cs) + ρwit (Branch.node cs) ≤ -δ

/-- The surcharged subaction inequality at vertices of degree `≥ 4`. -/
def SurchargeCell (μ : ℝ) : Prop :=
  ∀ cs : List Branch, 3 ≤ cs.length →
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + μ * (bY (Branch.node cs) - 3 / 23) ≤ (cs.map ρwit).sum

/-- Non-atom vertex of degree `≥ 4` with only atom children: `V_μ ≤ 3μ/23 − δ`. -/
def AtomCellMu (μ δ : ℝ) : Prop :=
  ∀ cs : List Branch, 3 ≤ cs.length → (∀ c ∈ cs, IsAtom c) → ¬ IsAtom (Branch.node cs) →
    bV μ (Branch.node cs) ≤ μ * (3 / 23) - δ

theorem sum_map_add_bell_ρ (l : List Branch) :
    (l.map (fun c => bell c + ρwit c)).sum = (l.map bell).sum + (l.map ρwit).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- One-level subaction bound: `bell(node cs) + ρwit(node cs) ≤ Σ_c (bell c + ρwit c)`. -/
theorem bell_add_ρwit_node_le (cs : List Branch) :
    bell (Branch.node cs) + ρwit (Branch.node cs) ≤ (cs.map (fun c => bell c + ρwit c)).sum := by
  rw [sum_map_add_bell_ρ, bell_node]
  have := isSubaction_ρwit cs
  linarith

/-- **The non-atom gap of the ceiling, from `AtomCell0`.**  Every non-atom branch has
    `bell b + ρwit b ≤ −δ` (hence `bell b ≤ −δ`). -/
theorem bell_add_ρwit_le_of_nonatom {δ : ℝ} (hA : AtomCell0 δ) :
    ∀ b, ¬ IsAtom b → bell b + ρwit b ≤ -δ := by
  refine scl_of_child_step bsize bchildren (fun b => ¬ IsAtom b → bell b + ρwit b ≤ -δ)
    bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs =>
    intro hna
    by_cases h : ∃ c ∈ cs, ¬ IsAtom c
    · obtain ⟨c0, hc0, hnc0⟩ := h
      have hc0' := hIH c0 (by simpa only [bchildren] using hc0) hnc0
      have hsum := sum_le_of_one_gap (f := fun c => bell c + ρwit c) (g := 0) (δ := δ) cs
        (fun c _ => bell_add_ρwit_le c) ⟨c0, hc0, by simpa using hc0'⟩
      have := bell_add_ρwit_node_le cs
      simp only [mul_zero, zero_sub] at hsum
      linarith
    · push_neg at h
      exact hA cs h hna

/-- `ρwit` dominates the surcharge on vertices of degree `≤ 3` (`bcc ≤ 2`), for `μ ∈ [0, 23/624]`. -/
theorem surcharge_le_ρwit_low {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 23 / 624) (b : Branch)
    (hb : bcc b ≤ 2) : μ * (bY b - 3 / 23) ≤ ρwit b := by
  cases b with
  | node cs =>
    rcases cs with _ | ⟨c, _ | ⟨c2, _ | ⟨c3, t⟩⟩⟩
    · -- leaf: y = 1, ρ = F* ≥ 1 − 64/621
      have hF : (5:ℝ) / 156 ≤ FSTAR := by
        rw [FSTAR]
        have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 621 / 64 by norm_num)
        have : (1:ℝ) - (621 / 64)⁻¹ = 557 / 621 := by norm_num
        rw [this] at h
        linarith
      simp only [ρwit, bcc, List.length_nil, bY_leaf]
      nlinarith
    · -- degree 2: y ≥ 1/3, ρ = anchor + (y − 1/3)/4, anchor ≥ 3/400
      have hy := bY_deg2_ge_third c
      have hA := cherry_anchor_ge_tight
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      nlinarith
    · -- degree 3: 0 ≤ y ≤ 1/3, ρ = y/32
      have hy0 := bY_nonneg (Branch.node [c, c2])
      have hy1 : bY (Branch.node [c, c2]) ≤ 1 / 3 := by
        rw [bY_node]
        have h1 := bY_nonneg c; have h2 := bY_nonneg c2
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil]
        rw [div_le_div_iff₀ (by push_cast; linarith) (by norm_num)]
        push_cast; linarith
      simp only [ρwit, bcc, List.length_cons, List.length_nil]
      rcases le_or_gt μ (1 / 32) with hsm | hbg
      · nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hsm)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hbg.le)]
    · simp [bcc] at hb

/-- **The arm envelope at `μ = 0`**, from `AtomCell0` (first half is `bg_ceiling`). -/
theorem armEnv_zero_of_cells {δ : ℝ} (hA : AtomCell0 δ) : ArmEnv 0 δ := by
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · simp only [bV, zero_mul, add_zero]; exact bg_ceiling b
  · have h := bell_add_ρwit_le_of_nonatom hA b hb
    have := ρwit_nonneg b
    simp only [bV, zero_mul, add_zero, sub_eq_add_neg, zero_add]
    linarith

/-- **The arm envelope at a price `μ ∈ [0, 23/624]`**, from the three cell families at that price. -/
theorem armEnv_of_cells_at {μ δ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 23 / 624)
    (hA0 : AtomCell0 δ) (hS : SurchargeCell μ) (hAm : AtomCellMu μ δ) : ArmEnv μ δ := by
  have hJ := bell_add_ρwit_le_of_nonatom hA0
  -- the degree `≥ 4` expansion: V_μ(node cs) = Σ bell c + e + μ y
  have hexp : ∀ cs : List Branch, bV μ (Branch.node cs)
      = (cs.map bell).sum + (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
        + μ * bY (Branch.node cs) := by
    intro cs; rw [bV, bell_node]
  have hsplit : ∀ cs : List Branch, (cs.map bell).sum
      = (cs.map (fun c => bell c + ρwit c)).sum - (cs.map ρwit).sum := by
    intro cs; rw [sum_map_add_bell_ρ]; ring
  have hsum0 : ∀ cs : List Branch, (cs.map (fun c => bell c + ρwit c)).sum ≤ 0 := by
    intro cs; exact list_sum_nonpos (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bell_add_ρwit_le c)
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · cases b with
    | node cs =>
      rcases le_or_gt cs.length 2 with hlo | hhi
      · have h1 := bell_add_ρwit_le (Branch.node cs)
        have h2 := surcharge_le_ρwit_low hμ0 hμ1 (Branch.node cs) (by simpa [bcc] using hlo)
        rw [bV]; linarith
      · have hs := hS cs (by omega)
        rw [hexp, hsplit]
        have := hsum0 cs
        linarith
  · cases b with
    | node cs =>
      rcases le_or_gt cs.length 2 with hlo | hhi
      · have h1 := hJ (Branch.node cs) hb
        have h2 := surcharge_le_ρwit_low hμ0 hμ1 (Branch.node cs) (by simpa [bcc] using hlo)
        rw [bV]; linarith
      · by_cases h : ∃ c ∈ cs, ¬ IsAtom c
        · obtain ⟨c0, hc0, hnc0⟩ := h
          have hsum := sum_le_of_one_gap (f := fun c => bell c + ρwit c) (g := 0) (δ := δ) cs
            (fun c _ => bell_add_ρwit_le c) ⟨c0, hc0, by simpa using hJ c0 hnc0⟩
          simp only [mul_zero, zero_sub] at hsum
          have hs := hS cs (by omega)
          rw [hexp, hsplit]
          linarith
        · push_neg at h
          exact hAm cs (by omega) h hb

/-- **The arm envelope on all of `[0, 23/624]`**, from the three cell families at the single price
    `μ0 = 23/624` (plus `AtomCell0`), by `armEnv_interp`. -/
theorem armEnv_of_cells {δ : ℝ} (hA0 : AtomCell0 δ) (hS : SurchargeCell (23 / 624))
    (hAm : AtomCellMu (23 / 624) δ) :
    ∀ μ, 0 ≤ μ → μ ≤ 23 / 624 → ArmEnv μ δ := by
  intro μ hμ0 hμ1
  exact armEnv_interp (by norm_num) (armEnv_zero_of_cells hA0)
    (armEnv_of_cells_at (by norm_num) le_rfl hA0 hS hAm) hμ0 hμ1

/-- **Spider domination in the high-degree case, reduced to three explicit cell families.**
    Under `AtomCell0 (1/75)`, `SurchargeCell (23/624)` and `AtomCellMu (23/624) (1/75)`: every root list
    with `k ≥ 24` children, at least one a non-atom, and `n − 1 ≥ 90`, is strictly beaten by a spider of
    the same size (arms of five and four cherries). -/
theorem spider_dominates_highDegree_of_cells
    (hA0 : AtomCell0 (1 / 75)) (hS : SurchargeCell (23 / 624)) (hAm : AtomCellMu (23 / 624) (1 / 75))
    (cs : List Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (hN : 90 ≤ bsizeList cs) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) :=
  spider_dominates_highDegree (armEnv_of_cells hA0 hS hAm) cs hk hna hN

/-! ### Shrinking the cell families to finite-degree cores.

  The atoms themselves satisfy the arm envelope on `[0, 23/624]` (`atom_bV_le`, from rational log
  enclosures for `arm_1..arm_4`, the cherry anchor and `bg_ceiling` for `arm_j`, `j ≥ 5`).  Hence the atom
  cells hold outright for `K ≥ 23` children (tangent at `t = 26/23`: value `≤ log(26/23) − F* ≈ −0.084`),
  and the surcharge cell holds outright for degree `≥ 8` (the surcharge is `≤ 0` there and the rest is
  `isSubaction_ρwit`).  What remains are the finite-degree cores below. -/

theorem fstar_ge : (17 / 100 : ℝ) ≤ FSTAR := by
  have hA := cherry_anchor_ge_tight
  have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3 / 2 by norm_num)
  have : (1:ℝ) - (3 / 2)⁻¹ = 1 / 3 := by norm_num
  rw [this] at h
  linarith

theorem log_26_23_le : Real.log (26 / 23 : ℝ) ≤ 3 / 23 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 26 / 23 by norm_num)
  linarith

/-- `11·bell(arm_j) = log(T_j^11 / (621/64)^(2j+1))` for the rational `T_j = (3/2)^j (4j+3)/(3j+3)`. -/
theorem eleven_bell_armB (j : ℕ) :
    11 * bell (armB j)
      = Real.log (((3 / 2 : ℝ) ^ j * ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3))) ^ 11
          / (621 / 64 : ℝ) ^ (2 * j + 1)) := by
  have hT : (0:ℝ) < (3 / 2 : ℝ) ^ j * ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3)) := by positivity
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, bell_armB, ← eleven_fstar]
  push_cast
  ring

/-- `bell(arm_j) ≤ (R − 1)/11` for any rational `R ≥ T_j^11/(621/64)^(2j+1)` (`log x ≤ x − 1`). -/
theorem bell_armB_le (j : ℕ) {R : ℝ}
    (hR : ((3 / 2 : ℝ) ^ j * ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3))) ^ 11 / (621 / 64 : ℝ) ^ (2 * j + 1) ≤ R) :
    bell (armB j) ≤ (R - 1) / 11 := by
  have hpos : (0:ℝ) < ((3 / 2 : ℝ) ^ j * ((4 * (j : ℝ) + 3) / (3 * (j : ℝ) + 3))) ^ 11
      / (621 / 64 : ℝ) ^ (2 * j + 1) := by positivity
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := eleven_bell_armB j
  linarith

theorem bY_armB_le (j : ℕ) (hj : 5 ≤ j) : bY (armB j) ≤ 3 / 23 := by
  rw [bY_armB]
  have : (23:ℝ) ≤ 4 * (j : ℝ) + 3 := by
    have : (5:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Every atom satisfies the arm envelope on `[0, 23/624]`:** `V_μ(a) ≤ 3μ/23`. -/
theorem atom_bV_le {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 23 / 624) {a : Branch} (ha : IsAtom a) :
    bV μ a ≤ μ * (3 / 23) := by
  rcases ha with rfl | ⟨j, rfl⟩
  · rw [bV, bell_cherry, bY_cherry]
    have := cherry_anchor_ge_tight
    nlinarith
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j) with h | h | h | h | h | h
    · subst h
      have hl : armB 0 = Branch.node [] := rfl
      rw [hl, bV, bell_leaf, bY_leaf]
      have := fstar_ge
      nlinarith
    · subst h
      have hb := bell_armB_le 1 (R := 52 / 100) (by norm_num)
      rw [bV, bY_armB]; norm_num at hb ⊢; nlinarith
    · subst h
      have hb := bell_armB_le 2 (R := 4 / 5) (by norm_num)
      rw [bV, bY_armB]; norm_num at hb ⊢; nlinarith
    · subst h
      have hb := bell_armB_le 3 (R := 94 / 100) (by norm_num)
      rw [bV, bY_armB]; norm_num at hb ⊢; nlinarith
    · subst h
      have hb := bell_armB_le 4 (R := 98878 / 100000) (by norm_num)
      rw [bV, bY_armB]; norm_num at hb ⊢; nlinarith
    · have hb := bg_ceiling (armB j)
      have hy := bY_armB_le j h
      rw [bV]; nlinarith

theorem ρwit_node_of_four_le (cs : List Branch) (h : 4 ≤ cs.length) : ρwit (Branch.node cs) = 0 := by
  rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, t⟩⟩⟩⟩
  all_goals first | rfl | (simp at h) | (simp [ρwit, bcc, List.length_cons])

/-- Tangent bound at a vertex with `K = |cs|` children, `t = 26/23`, price `μ = 23/(26(K+1))`. -/
theorem bell_node_le_tangent_2623 (cs : List Branch) :
    bell (Branch.node cs) ≤ Real.log (26 / 23) - 3 / 26 - FSTAR
      + (cs.map (bV (23 / (26 * ((cs.length : ℝ) + 1))))).sum := by
  have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / ((cs.length : ℝ) + 1) := by
    have := div_nonneg (sumY_nonneg cs) hd.le; linarith
  have htan := log_le_tangent_at hfac (show (0:ℝ) < 26 / 23 by norm_num)
  have hsplit : (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) / (26 / 23)
      = 23 / 26 + 23 / (26 * ((cs.length : ℝ) + 1)) * (cs.map bY).sum := by
    field_simp
  rw [hsplit] at htan
  rw [bell_node, sum_map_bV]
  linarith

/-- For `K ≥ 23` atom children the tangent bound gives `bell(node) ≤ log(26/23) − F*`. -/
theorem bell_node_atoms_highK (cs : List Branch) (hK : 23 ≤ cs.length) (hat : ∀ c ∈ cs, IsAtom c) :
    bell (Branch.node cs) ≤ Real.log (26 / 23) - FSTAR := by
  have hKR : (23:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hK
  set μ := 23 / (26 * ((cs.length : ℝ) + 1)) with hμ
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have hμ1 : μ ≤ 23 / 624 := by
    rw [hμ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsum : (cs.map (bV μ)).sum ≤ (cs.length : ℝ) * (μ * (3 / 23)) := by
    have : ∀ l : List Branch, (∀ c ∈ l, IsAtom c) → (l.map (bV μ)).sum ≤ (l.length : ℝ) * (μ * (3 / 23)) := by
      intro l hl
      induction l with
      | nil => simp
      | cons x r ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
          have hx := atom_bV_le hμ0 hμ1 (hl x (List.mem_cons.mpr (Or.inl rfl)))
          have hr := ih (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
          linarith
    exact this cs hat
  have hKμ : (cs.length : ℝ) * (μ * (3 / 23)) ≤ 3 / 26 := by
    rw [hμ, show (cs.length : ℝ) * (23 / (26 * ((cs.length : ℝ) + 1)) * (3 / 23))
        = 3 / 26 * ((cs.length : ℝ) / ((cs.length : ℝ) + 1)) by field_simp]
    have : (cs.length : ℝ) / ((cs.length : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have := bell_node_le_tangent_2623 cs
  linarith

/-- The atom cell restricted to `K ≤ 22` children (the finite-degree core). -/
def AtomCell0Core (δ : ℝ) : Prop :=
  ∀ cs : List Branch, cs.length ≤ 22 → (∀ c ∈ cs, IsAtom c) → ¬ IsAtom (Branch.node cs) →
    bell (Branch.node cs) + ρwit (Branch.node cs) ≤ -δ

/-- The `μ`-atom cell restricted to `3 ≤ K ≤ 22` children. -/
def AtomCellMuCore (μ δ : ℝ) : Prop :=
  ∀ cs : List Branch, 3 ≤ cs.length → cs.length ≤ 22 → (∀ c ∈ cs, IsAtom c) →
    ¬ IsAtom (Branch.node cs) → bV μ (Branch.node cs) ≤ μ * (3 / 23) - δ

/-- The surcharge cell restricted to degrees `4..7` (`3 ≤ K ≤ 6` children). -/
def SurchargeCore (μ : ℝ) : Prop :=
  ∀ cs : List Branch, 3 ≤ cs.length → cs.length ≤ 6 →
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + μ * (bY (Branch.node cs) - 3 / 23) ≤ (cs.map ρwit).sum

theorem atomCell0_of_core (h : AtomCell0Core (1 / 75)) : AtomCell0 (1 / 75) := by
  intro cs hat hna
  rcases le_or_gt cs.length 22 with hK | hK
  · exact h cs hK hat hna
  · rw [ρwit_node_of_four_le cs (by omega)]
    have := bell_node_atoms_highK cs (by omega) hat
    have := fstar_ge
    have := log_26_23_le
    linarith

theorem atomCellMu_of_core (h : AtomCellMuCore (23 / 624) (1 / 75)) : AtomCellMu (23 / 624) (1 / 75) := by
  intro cs h3 hat hna
  rcases le_or_gt cs.length 22 with hK | hK
  · exact h cs h3 hK hat hna
  · have hb := bell_node_atoms_highK cs (by omega) hat
    have hy : bY (Branch.node cs) ≤ 1 / 24 := by
      rw [bY_node]
      have hKR : (23:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hK
      have := sumY_nonneg cs
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have := fstar_ge
    have := log_26_23_le
    rw [bV]; nlinarith

theorem surchargeCell_of_core {μ : ℝ} (hμ : 0 ≤ μ) (h : SurchargeCore μ) : SurchargeCell μ := by
  intro cs h3
  rcases le_or_gt cs.length 6 with hK | hK
  · exact h cs h3 hK
  · have hsub := isSubaction_ρwit cs
    rw [ρwit_node_of_four_le cs (by omega)] at hsub
    have hy : bY (Branch.node cs) ≤ 3 / 23 := by
      rw [bY_node]
      have hKR : (7:ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast hK
      have := sumY_nonneg cs
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    nlinarith

/-- **Spider domination in the high-degree case, reduced to three FINITE-DEGREE cores.**
    Under `AtomCell0Core (1/75)` (non-atom vertices with `≤ 22` atom children),
    `AtomCellMuCore (23/624) (1/75)` (degree `4..23`, atom children) and `SurchargeCore (23/624)`
    (degree `4..7`, arbitrary children through `(bcc, y)`): every root list with `k ≥ 24` children, at least
    one a non-atom, and `n − 1 ≥ 90`, is strictly beaten by a spider of the same size. -/
theorem spider_dominates_highDegree_of_cores
    (hA0 : AtomCell0Core (1 / 75)) (hS : SurchargeCore (23 / 624)) (hAm : AtomCellMuCore (23 / 624) (1 / 75))
    (cs : List Branch) (hk : 24 ≤ cs.length) (hna : ∃ c ∈ cs, ¬ IsAtom c)
    (hN : 90 ≤ bsizeList cs) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) :=
  spider_dominates_highDegree_of_cells (atomCell0_of_core hA0) (surchargeCell_of_core (by norm_num) hS)
    (atomCellMu_of_core hAm) cs hk hna hN

/-! ### The low-degree case: reduction to a taxed (degree-capped) envelope.

  For trees of maximum degree `≤ D` the arm envelope is too weak (the optimum spider has centre degree
  `≈ n/10`, so for moderate `n` the relevant root degrees are small and the size-free bound exceeds the
  spider value).  The natural replacement is a size TAX: degree-capped branches grow at a rate strictly
  below `F*`.  `TaxedEnv D λ μ W` says `bell b + λ|b| + μ y_b ≤ W` for every branch all of whose vertices
  have `≤ D − 1` children.  Given it, the root bound loses `λ (n − 1)` (`phiRoot_le_taxed`), which beats
  the spider for `n` large (`spider_dominates_lowDegree_of_taxed`).  `TaxedEnv` is NOT proved here. -/

mutual
  /-- Maximum child count over all vertices of a branch. -/
  def maxCh : Branch → ℕ
    | .node cs => max cs.length (maxChList cs)
  /-- Maximum child count over a child list. -/
  def maxChList : List Branch → ℕ
    | [] => 0
    | c :: t => max (maxCh c) (maxChList t)
end

/-- The taxed envelope for branches of maximum degree `≤ D` (as non-root vertices: `≤ D − 1` children). -/
def TaxedEnv (D : ℕ) (lam μ W : ℝ) : Prop :=
  ∀ b, maxCh b + 1 ≤ D → bell b + lam * (bsize b : ℝ) + μ * bY b ≤ W

/-- **Taxed root bound.**  Under `TaxedEnv D λ (1/(k t)) W` for the children of a root with `k` children:
    `log pi − (n−1)F* ≤ log t + 1/t − 1 + k W − λ (n − 1)`. -/
theorem phiRoot_le_taxed (cs : List Branch) (hcs : cs ≠ []) {t : ℝ} (ht : 0 < t) {D : ℕ} {lam W : ℝ}
    (hT : TaxedEnv D lam (1 / ((cs.length : ℝ) * t)) W) (hb : ∀ c ∈ cs, maxCh c + 1 ≤ D) :
    phiRoot cs ≤ Real.log t + 1 / t - 1 + (cs.length : ℝ) * W - lam * (bsizeList cs : ℝ) := by
  have htan := phiRoot_le_tangent cs hcs ht
  set μ := 1 / ((cs.length : ℝ) * t)
  have key : ∀ l : List Branch, (∀ c ∈ l, maxCh c + 1 ≤ D) →
      (l.map (bV μ)).sum ≤ (l.length : ℝ) * W - lam * (bsizeList l : ℝ) := by
    intro l hl
    induction l with
    | nil => simp [bsizeList]
    | cons a r ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, bsizeList, Nat.cast_add]
        have ha := hT a (hl a (List.mem_cons.mpr (Or.inl rfl)))
        have hr := ih (fun c hc => hl c (List.mem_cons.mpr (Or.inr hc)))
        have hv : bV μ a = bell a + μ * bY a := rfl
        linarith
  have := key cs hb
  linarith

/-- **Low-degree spider domination, conditional on the taxed envelope.**  If the children of a root with
    `k` children all have maximum degree `≤ D`, `TaxedEnv D λ (1/(k t)) W` holds, `n − 1 = N ≥ 90`, and the
    taxed bound is below the spider floor, `log t + 1/t − 1 + k W − λ N < log(26/23) − 1/96`, then an
    arm_5/arm_4 spider of the same size is strictly better. -/
theorem spider_dominates_lowDegree_of_taxed (cs : List Branch) (hcs : cs ≠ []) {t : ℝ} (ht : 0 < t)
    {D : ℕ} {lam W : ℝ} (hT : TaxedEnv D lam (1 / ((cs.length : ℝ) * t)) W)
    (hb : ∀ c ∈ cs, maxCh c + 1 ≤ D) (hN : 90 ≤ bsizeList cs)
    (hlt : Real.log t + 1 / t - 1 + (cs.length : ℝ) * W - lam * (bsizeList cs : ℝ)
      < Real.log (26 / 23) - 1 / 96) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  set N := bsizeList cs with hNdef
  refine ⟨(N - 9 * ((5 * N) % 11)) / 11, (5 * N) % 11, by omega, ?_, ?_⟩
  · rw [bsizeList_spiderB]; omega
  · have hsz : bsizeList (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) = N := by
      rw [bsizeList_spiderB]; omega
    have haq : 1 ≤ (N - 9 * ((5 * N) % 11)) / 11 + (5 * N) % 11 := by omega
    have hq10 : (((5 * N) % 11 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : (5 * N) % 11 ≤ 10)
    have hlo := phiRoot_spider_ge _ _ haq
    have hup := phiRoot_le_taxed cs hcs ht hT hb
    have h4 := bell_arm4_ge
    have h4' : (-1 / 96 : ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) * bell (armB 4) := by
      have hqnn : (0:ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hlt' : phiRoot cs < phiRoot (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) := by
      linarith
    unfold phiRoot at hlt'
    rw [hsz, ← hNdef] at hlt'
    exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

/-! ### The low-degree case via a per-vertex RATE cell (bounded degree ⇒ linear deficit).

  With `g(c) := bell c + α|c|` for an atom child and `g(c) := −ρwit c` otherwise, the per-vertex cell

    `RateCell α`:  for a non-atom vertex with `≤ 22` children,
                   `(log(1 + S/d) − F*) + ρwit(node) + α + Σ_c g(c) ≤ 0`

  telescopes (`bell_add_ρwit_le_rate`) to `bell b + ρwit b ≤ −α |b|` for every non-atom branch all of
  whose vertices have `≤ 22` children: a LINEAR deficit.  At a root of degree `k ≤ 23` this gives
  `log pi − (n−1)F* ≤ [log(1 + S/k) + Σ g] − α(n−1)` (`phiRoot_le_rate`), and a root cell bounding the
  bracket by `R` finishes (`spider_dominates_lowDegree_of_rate`).  `RateCell` and the root cell are NOT
  proved here; numerically `RateCell` holds for `α ≈ 3.0e-4` (binding at degree 6) and the root bracket is
  `≤ 0.2082 .. 0.2545` for `k = 5..23`, giving an explicit threshold `N1` (see the doc). -/

open Classical in
/-- The per-child weight of the rate cell. -/
noncomputable def rateG (α : ℝ) (c : Branch) : ℝ :=
  if IsAtom c then bell c + α * (bsize c : ℝ) else -ρwit c

/-- The per-vertex rate cell. -/
def RateCell (α : ℝ) : Prop :=
  ∀ cs : List Branch, cs.length ≤ 22 → ¬ IsAtom (Branch.node cs) →
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρwit (Branch.node cs) + α
      + (cs.map (rateG α)).sum ≤ 0

theorem maxCh_node (cs : List Branch) : maxCh (Branch.node cs) = max cs.length (maxChList cs) := by
  simp [maxCh]

theorem maxCh_le_of_mem {c : Branch} : ∀ {cs : List Branch}, c ∈ cs → maxCh c ≤ maxChList cs
  | [], h => by simp at h
  | a :: t, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp [maxChList]
      · have := maxCh_le_of_mem h'
        simp only [maxChList]; omega

/-- `bell c ≤ rateG α c − α|c|` for every child whose non-atom branches satisfy the linear deficit. -/
theorem bell_le_rateG {α : ℝ} {c : Branch}
    (h : ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ)) :
    bell c ≤ rateG α c - α * (bsize c : ℝ) := by
  unfold rateG
  split_ifs with ha
  · linarith
  · have := h ha; linarith

theorem sum_bell_le_rateG {α : ℝ} : ∀ (cs : List Branch),
    (∀ c ∈ cs, ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ)) →
    (cs.map bell).sum ≤ (cs.map (rateG α)).sum - α * (bsizeList cs : ℝ)
  | [], _ => by simp [bsizeList]
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons, bsizeList, Nat.cast_add]
      have ha := bell_le_rateG (h a (List.mem_cons.mpr (Or.inl rfl)))
      have ht := sum_bell_le_rateG t (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
      linarith

/-- **Linear deficit for bounded degree, from `RateCell`.** -/
theorem bell_add_ρwit_le_rate {α : ℝ} (hR : RateCell α) :
    ∀ b, maxCh b ≤ 22 → ¬ IsAtom b → bell b + ρwit b ≤ -α * (bsize b : ℝ) := by
  refine scl_of_child_step bsize bchildren
    (fun b => maxCh b ≤ 22 → ¬ IsAtom b → bell b + ρwit b ≤ -α * (bsize b : ℝ))
    bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs =>
    intro hcap hna
    rw [maxCh_node] at hcap
    have hlen : cs.length ≤ 22 := le_trans (le_max_left _ _) hcap
    have hch : ∀ c ∈ cs, ¬ IsAtom c → bell c + ρwit c ≤ -α * (bsize c : ℝ) := fun c hc =>
      hIH c (by simpa only [bchildren] using hc)
        (le_trans (maxCh_le_of_mem hc) (le_trans (le_max_right _ _) hcap))
    have hsum := sum_bell_le_rateG cs hch
    have hcell := hR cs hlen hna
    have hsz : (bsize (Branch.node cs) : ℝ) = 1 + (bsizeList cs : ℝ) := by
      simp only [bsize]; push_cast; ring
    rw [bell_node, hsz]
    linarith

/-- **Root bound under `RateCell`.**  For a root whose children have all vertices with `≤ 22` children:
    `log pi − (n−1)F* ≤ log(1 + S/k) + Σ rateG α − α (n − 1)`. -/
theorem phiRoot_le_rate {α : ℝ} (hR : RateCell α) (cs : List Branch) (hcap : ∀ c ∈ cs, maxCh c ≤ 22) :
    phiRoot cs ≤ Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG α)).sum
      - α * (bsizeList cs : ℝ) := by
  rw [phiRoot_eq]
  have := sum_bell_le_rateG cs (fun c hc hna => bell_add_ρwit_le_rate hR c (hcap c hc) hna)
  linarith

/-- **Low-degree spider domination, conditional on `RateCell α` and a root-cell bound `R`.** -/
theorem spider_dominates_lowDegree_of_rate {α R : ℝ} (hR : RateCell α) (cs : List Branch)
    (hcap : ∀ c ∈ cs, maxCh c ≤ 22)
    (hroot : Real.log (1 + (cs.map bY).sum / (cs.length : ℝ)) + (cs.map (rateG α)).sum ≤ R)
    (hN : 90 ≤ bsizeList cs) (hlt : R - α * (bsizeList cs : ℝ) < Real.log (26 / 23) - 1 / 96) :
    ∃ a q : ℕ, q ≤ 10 ∧ bsizeList (spiderB a q) = bsizeList cs ∧ piRoot cs < piRoot (spiderB a q) := by
  set N := bsizeList cs with hNdef
  refine ⟨(N - 9 * ((5 * N) % 11)) / 11, (5 * N) % 11, by omega, ?_, ?_⟩
  · rw [bsizeList_spiderB]; omega
  · have hsz : bsizeList (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) = N := by
      rw [bsizeList_spiderB]; omega
    have haq : 1 ≤ (N - 9 * ((5 * N) % 11)) / 11 + (5 * N) % 11 := by omega
    have hq10 : (((5 * N) % 11 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : (5 * N) % 11 ≤ 10)
    have hlo := phiRoot_spider_ge _ _ haq
    have hup := phiRoot_le_rate hR cs hcap
    have h4 := bell_arm4_ge
    have h4' : (-1 / 96 : ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) * bell (armB 4) := by
      have hqnn : (0:ℝ) ≤ (((5 * N) % 11 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hlt' : phiRoot cs < phiRoot (spiderB ((N - 9 * ((5 * N) % 11)) / 11) ((5 * N) % 11)) := by
      linarith
    unfold phiRoot at hlt'
    rw [hsz, ← hNdef] at hlt'
    exact (Real.log_lt_log_iff (piRoot_pos _) (piRoot_pos _)).mp (by linarith)

end BGSCL
end R3Cert
