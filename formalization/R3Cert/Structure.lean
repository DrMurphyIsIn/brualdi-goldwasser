/-
  R3 (Phi <= 1) -- the PROOF STRUCTURE.  This file assembles the Lean-proved pieces (ExactCruxes, DEC, and the
  Jensen reduction of Jensen.lean) into the GENUINE per-node induction step `node_le_omega`, and isolates -- as
  CORRECTLY STATED hypotheses, not vacuous placeholders -- the pieces that still need a larger formalization:
    (S) the finite interval SWEEP -- that the Jensen-reduced all-equal node `Qeq s j H m` is <= omega over the
        reachable range.  The tails (`s_tail_ge_65` for s>=65, `node_jtail_le'` for j>=96) and the near-star
        grid (`grid_nodes`, `node_ns_le`) ARE proved in Sweep.lean/JTail.lean; the remaining finite
        (s<=64, j<=95) continuum-`m` core is gap_interval_certification.py's interval certificate.
    (E) the ENVELOPE / reachability -- the E0/E1 band classification over the reachable-cavity predicate, and
        that each child amplitude is <= H(child cavity) for the concave menu hull H (the tree induction).

  No `axiom`s: unproved facts are explicit, CORRECTLY-TYPED hypotheses of `node_le_omega`, whose conclusion is
  the ACTUAL amplitude bound `nodeAmp <= omega` and which USES every hypothesis.  (This replaces the earlier
  `phi_le_one_step`, whose hypotheses were false-as-written / vacuous and whose conclusion was three constant
  facts about rhoB that used none of them.)

  Notation mirrors Jensen.lean / adversary_sweep.py: a DEC node has `s` arm-units and `j` deep children with
  cavities `mu_i` and amplitudes `ell_i`; `nodeAmp` is its arm-normalized amplitude `ell(node)`;
  `omega = log Phi(ARM)`; the target is `ell(node) <= 0` (Phi <= 1).
-/
import R3Cert.ExactCruxes
import R3Cert.DEC
import R3Cert.Jensen
import R3Cert.Hull
import R3Cert.JTail

namespace R3Cert

open Real
open scoped BigOperators

/-! ## The band classification (E0/E1) -- CORRECTLY stated over the reachable-cavity predicate.

The earlier `∀ mu : ℚ, ...` forms were FALSE: they quantified over ALL rationals (e.g. `mu = 2` violates E0,
`mu = 3/8` violates E1).  The intended -- and true -- statements are conditional on reachability: they
constrain only the cavities that actually arise as `3/t` on a rooted branch.  They are parametrised here by an
abstract reachability predicate `Reach : ℝ → Prop` (whose inductive definition is part of remaining item (E)). -/

/-- E0: every REACHABLE branch cavity lies in `{1} ∪ (0, 1/2)`.  -- CERT: lemma_proofs.prove_E0. -/
def E0_cavity_classification (Reach : ℝ → Prop) : Prop :=
  ∀ mu : ℝ, Reach mu → (mu = 1 ∨ (0 < mu ∧ mu < 1 / 2))

/-- E1: no REACHABLE cavity lies in the forbidden band `(1/3, 2/5]`.  -- CERT: lemma_proofs.prove_E1. -/
def E1_forbidden_band (Reach : ℝ → Prop) : Prop :=
  ∀ mu : ℝ, Reach mu → ¬ (1 / 3 < mu ∧ mu ≤ 2 / 5)

/-! ## E3 shoulder bound / E2 chain region -- Lean-proved (genuine). -/

/-- The E3 shoulder inequality reduces to `rho_B^2 >= 3/2`, which is `R3Cert.rhoB_sq_ge` (from `e3_crux`). -/
theorem e3_reduces_to_crux : (3 / 2 : ℝ) ≤ rhoB ^ 2 := rhoB_sq_ge

/-- E2 decay (`2 rho_B > 1 + sqrt 2`) is `R3Cert.e2_two_rhoB_gt`; every chain amplitude strictly decays. -/
theorem e2_decay : 1 + Real.sqrt 2 < 2 * rhoB := e2_two_rhoB_gt

/-- The E2 binding value `T = -4L + log(3/2) + log(17/14) + log(7/6)` is negative (`< 0`).
    -- CERT: e2_closure.certify (T_binding, T = -0.072573). -/
def E2_binding_negative : Prop :=
  (-4) * Real.log rhoB + Real.log (3/2) + Real.log (17/14) + Real.log (7/6) < 0

/-- **E2 binding bound, promoted from certificate to THEOREM.**  `T = -4 log(rhoB) + log(3/2) + log(17/14) +
    log(7/6) < 0`.  The three logs combine to `log(17/8)` (since `3/2 · 17/14 · 7/6 = 17/8`), and
    `4 log rhoB = (4/11) log(621/64)` (`rhoB^11 = 621/64`), so `T < 0` reduces to the EXACT RATIONAL inequality
    `(17/8)^11 < (621/64)^4` (`3989.77 < 8864.34`), discharged by `norm_num`.  This is the E2 chain-amplitude
    binding value (`chainB_max <= T`), now a machine-checked real-log theorem, not a numeric certificate. -/
theorem E2_binding_negative_holds : E2_binding_negative := by
  have hcomb : Real.log (3 / 2) + Real.log (17 / 14) + Real.log (7 / 6) = Real.log (17 / 8) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1; norm_num
  have hrhoB : (11 : ℝ) * Real.log rhoB = Real.log (621 / 64) := by
    rw [← rhoB_pow11, Real.log_pow]; push_cast; ring
  have hkey : (11 : ℝ) * Real.log (17 / 8) < (4 : ℝ) * Real.log (621 / 64) := by
    have h3 : Real.log ((17 / 8 : ℝ) ^ (11 : ℕ)) < Real.log ((621 / 64 : ℝ) ^ (4 : ℕ)) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h3; push_cast at h3; linarith [h3]
  unfold E2_binding_negative
  linarith [hcomb, hrhoB, hkey]

/-! ## DEC identity -- a THEOREM (DEC.lean). -/

/-- (G) The DEC identity: the raw cavity amplitude equals the `(g, omega)`-normalized DEC form, a pure real-log
    identity depending only on `omega = log(3/2)-2L` and `s = c+k`.  Discharged by `dec_identity`. -/
def DEC_identity : Prop :=
  ∀ c k j E L t den omega : ℝ, t ≠ 0 → den ≠ 0 → den = 4 * ((c + k) + j) + 3 →
    omega = Real.log (3 / 2) - 2 * L →
    c * Real.log (3 / 2) - (1 + 2 * c) * L + Real.log t
        - Real.log (3 * ((c + k) + j + 1)) + k * omega + E
      = gAmp L ((c + k) + j) - j * omega + E + Real.log (t / den)

theorem DEC_identity_holds : DEC_identity := fun c k j E L t den omega ht hden hd ho =>
  dec_identity c k j E L t den omega ht hden hd ho

/-! ## The Jensen reduction is PROVED (not a `Prop := True` placeholder). -/

/-- The Jensen reduction `nodeAmp <= Qeq` is `R3Cert.node_jensen_reduction` (Jensen.lean, machine-checked): for
    a concave menu hull `H` with children `ell_i <= H(mu_i)`, the multi-child DEC node is at most the
    all-children-equal node at the mean cavity `mubar = (Σ mu_i)/j`.  (Was `Jensen_reduction : Prop := True`.) -/
theorem jensen_reduction_holds {s j : ℕ} (hj : 0 < j) {H : ℝ → ℝ}
    (hH : ConcaveOn ℝ Set.univ H) (ell mu : Fin j → ℝ) (hell : ∀ i, ell i ≤ H (mu i)) :
    nodeAmp s j ell mu ≤ Qeq s j H ((∑ i, mu i) / j) :=
  node_jensen_reduction hj hH ell mu (fun i => Set.mem_univ _) hell

/-! ## The finite sweep bound -- CORRECTLY stated (the honest remaining leaf). -/

/-- (S) The finite sweep, over the reachable cavity range `m ∈ [0,1]`: the Jensen-reduced all-equal node
    `Qeq s j H m` is at most `omega`.  (Was `finite_sweep_bounded : Prop := ∀ mu, mu = mu`.)  The range
    `0 <= m <= 1` is essential -- `Qeq` is UNbounded for large `m` (the coupling blows up), so an unrestricted
    `∀ m` form would be false.  The `s`-tail (`s >= 65`) is PROVED (`Qeq_stail`); the `j`-uniform head bound
    (`node_head_le`) means `j` needs no separate tail; so the residual is exactly the finite `s <= 64` core
    (`gap_interval_certification.py`'s interval certificate). -/
def SweepBound (H : ℝ → ℝ) : Prop :=
  ∀ (s j : ℕ) (m : ℝ), 0 < j → 0 ≤ m → m ≤ 1 → Qeq s j H m ≤ omegaVal

/-! ## The finite sweep -- the `s`-tail (`s >= 65`) is PROVED; `SweepBound` reduces to the `s <= 64` core. -/

/-- **The all-equal coupling factor is `<= 3/2` on the reachable range** (`m <= 1`):
    `(4s+3j+3+3jm)/(4(s+j)+3) <= 3/2`, since `3jm <= 3j <= 2s+3j+3/2`. -/
theorem coupling_le (s j : ℕ) (m : ℝ) (hm : m ≤ 1) :
    (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3) ≤ 3 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) by positivity) (show (0 : ℝ) ≤ 1 - m by linarith),
    show (0 : ℝ) ≤ (s : ℝ) by positivity, show (0 : ℝ) ≤ (j : ℝ) by positivity]

/-- **The `s`-tail of the sweep (`s >= 65`), PROVED.**  For any menu value `H m <= 0` and cavity `m ∈ [0,1]`,
    `Qeq s j H m <= omega` when `s >= 65`.  Uses the `j`-uniform head bound `node_head_le`
    (`g(s+j)-jω <= sω+λ`), `log(coupling) <= log(3/2)` (`coupling_le`), `j·H m <= 0`, and `s_tail_ge_65`
    (`sω+λ+log(3/2) <= ω`).  This discharges the `s >= 65` half of `SweepBound`, leaving the finite `s <= 64`
    core. -/
theorem Qeq_stail {H : ℝ → ℝ} (s j : ℕ) (m : ℝ) (hs : 65 ≤ s) (hm0 : 0 ≤ m) (hm : m ≤ 1)
    (hH : H m ≤ 0) : Qeq s j H m ≤ omegaVal := by
  have hden : (0 : ℝ) < 4 * ((s : ℝ) + j) + 3 := by positivity
  have h3jm : (0 : ℝ) ≤ 3 * (j : ℝ) * m :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg j)) hm0
  have hnum : (0 : ℝ) < 4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m := by
    have h0 : (0 : ℝ) ≤ 4 * (s : ℝ) + 3 * (j : ℝ) := by positivity
    linarith [h3jm, h0]
  have hlogcoup : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3))
      ≤ Real.log (3 / 2) := Real.log_le_log (div_pos hnum hden) (coupling_le s j m hm)
  have hHj : (j : ℝ) * H m ≤ 0 := by
    nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity, hH]
  have hhead := node_head_le s j
  have htail := s_tail_ge_65 s hs
  unfold Qeq
  linarith [hhead, hHj, hlogcoup, htail]

/-- **`SweepBound` reduces to the finite `s <= 64` core.**  Given the finite-core bound and `H <= 0` on the
    reachable range `[0,1]`, the proved `s`-tail `Qeq_stail` extends it to all `s`, establishing `SweepBound H`.
    So the ONLY remaining sweep obligation is the finite `s <= 64` continuum-`m` core. -/
theorem sweepBound_of_core {H : ℝ → ℝ}
    (hH0 : ∀ m, 0 ≤ m → m ≤ 1 → H m ≤ 0)
    (hcore : ∀ s j m, s ≤ 64 → 0 < j → 0 ≤ m → m ≤ 1 → Qeq s j H m ≤ omegaVal) :
    SweepBound H := by
  intro s j m hj hm0 hm
  rcases Nat.lt_or_ge s 65 with h | h
  · exact hcore s j m (by omega) hj hm0 hm
  · exact Qeq_stail s j m h hm0 hm (hH0 m hm0 hm)

/-! ## The all-equal coupling is monotone in the mean cavity `m` -- the interval-cell reduction.

For the finite `s <= 64` core, the interval certificate splits `m ∈ [0,1]` into cells and bounds each cell.
Since the coupling `(A+3jm)/B` is INCREASING in `m` (numerator increases, denominator fixed), over a cell
`[·, m1]` we have `coupling(m) <= coupling(m1)`, so `log(coupling(m)) <= log(coupling(m1))`; combined with a
cell bound on the menu value `H(m)` this feeds the per-node interval reduction `node_interval_le` (Sweep.lean).
`Qeq` concavity in `m` (the alternative stationary-point route) needs Mathlib's `log ∘ affine` concavity API;
the monotone-cell route below is self-contained. -/

/-- **The all-equal coupling is monotone increasing in `m`.**  `(A+3jm)/B <= (A+3jm')/B` for `m <= m'`
    (numerator increasing in `m` since `3j >= 0`, denominator `B > 0` fixed). -/
theorem coupling_mono (s j : ℕ) {m m' : ℝ} (hmm : m ≤ m') :
    (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3)
      ≤ (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m') / (4 * ((s : ℝ) + j) + 3) := by
  gcongr

/-! ## The per-node induction step -- REAL and conditional (replaces the hollow `phi_le_one_step`). -/

/-- **The multi-child per-node bound (the ROOT-J1 step).**  GIVEN the concave menu hull `H`, the child-envelope
    bound `ell_i <= H(mu_i)`, and the finite sweep bound `SweepBound H`, every DEC node with `j >= 1` deep
    children has arm-normalized amplitude `nodeAmp s j ell mu <= omega` -- i.e. `Phi(node) <= Phi(ARM)`.

    Proof: the machine-checked Jensen reduction `nodeAmp <= Qeq` (`jensen_reduction_holds`), then `SweepBound`.
    Unlike the former `phi_le_one_step`, the conclusion is the ACTUAL amplitude bound and every hypothesis is
    used.  Scope (honest): this is the multi-deep-child step; the `j = 0` near-star / ARM family is the
    separately proved arithmetic theorem (near_star_arithmetic_proof.py), and establishing `SweepBound` in full
    and the child-envelope `ell_i <= H(mu_i)` (E0-E3 + tree induction) is the remaining formalization -- named,
    correctly typed, no open mathematical idea. -/
theorem node_le_omega {s j : ℕ} (hj : 0 < j) {H : ℝ → ℝ}
    (hH : ConcaveOn ℝ Set.univ H) (hSweep : SweepBound H)
    (ell mu : Fin j → ℝ) (hmu : ∀ i, 0 ≤ mu i ∧ mu i ≤ 1) (hell : ∀ i, ell i ≤ H (mu i)) :
    nodeAmp s j ell mu ≤ omegaVal := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hmean0 : 0 ≤ (∑ i, mu i) / j :=
    div_nonneg (Finset.sum_nonneg (fun i _ => (hmu i).1)) hjr.le
  have hmean1 : (∑ i, mu i) / j ≤ 1 := by
    rw [div_le_one hjr]
    calc (∑ i, mu i) ≤ ∑ _i : Fin j, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hmu i).2)
      _ = (j : ℝ) := by simp
  exact le_trans (jensen_reduction_holds hj hH ell mu hell) (hSweep s j _ hj hmean0 hmean1)

/-- **Every multi-child node has `Phi < 1` (strictly).**  `nodeAmp <= omega < 0` (`omegaVal_neg`), so the
    arm-normalized amplitude of any `j >= 1` DEC node is strictly negative. -/
theorem node_amp_neg {s j : ℕ} (hj : 0 < j) {H : ℝ → ℝ}
    (hH : ConcaveOn ℝ Set.univ H) (hSweep : SweepBound H)
    (ell mu : Fin j → ℝ) (hmu : ∀ i, 0 ≤ mu i ∧ mu i ≤ 1) (hell : ∀ i, ell i ≤ H (mu i)) :
    nodeAmp s j ell mu < 0 :=
  lt_of_le_of_lt (node_le_omega hj hH hSweep ell mu hmu hell) omegaVal_neg

/-! ## A concrete menu hull `H` -- the inf-of-affines tent capped by the zero line.

`Hull.lean` builds the concave hull of the amplitude menu as an inf of affine segments (`hullOf`, concave by
construction).  The amplitude menu peaks at `0` at the TIE cavity `mu = 3/23` (near-star level `s' = 5`, where
`Phi = 1`) and is strictly negative on both sides (near-star amplitudes `g(s') < 0` for `s' != 5`).  So the
concrete hull is a concave "tent" through the tie point `(3/23, 0)`, capped from above by the zero line `y = 0`
(all child amplitudes are `<= 0`).  Taking the zero line as the `hullOf` SEED makes `H <= 0` immediate, and the
tent segments pass through the tie so `H(3/23) = 0`.  The two slopes `bL, bR` (left/right of the tie) are the
hull's structural parameters -- the exact rational tangent data of `adversary_sweep.py`'s certified hull;
concavity, non-positivity, and the tie value hold for ANY slopes and are proved here.  What remains (the
envelope work) is that the real menu points lie below the hull for the CERTIFIED slopes (`hullOf_dominates`). -/

/-- The tie cavity `mu = 3/23` (near-star level `s' = 5`), where the menu amplitude peaks at `0`. -/
noncomputable def tieCavity : ℝ := 3 / 23

/-- **The concrete menu hull.**  Zero-line seed `(0,0)` capped by two tangent segments through the tie point
    `(3/23, 0)`: a left segment of slope `bL` and a right segment of slope `bR` (each line `y = b (mu - 3/23)`,
    coefficients `(-b·3/23, b)`).  Concave by `hullOf_concave`; `<= 0` by the zero seed; `= 0` at the tie. -/
noncomputable def menuHull (bL bR : ℝ) : ℝ → ℝ :=
  hullOf [(-bL * (3 / 23), bL), (-bR * (3 / 23), bR)] (0, 0)

/-- **The menu hull is concave** (the Jensen premise) -- for free, `hullOf` is an inf of affines. -/
theorem menuHull_concave (bL bR : ℝ) : ConcaveOn ℝ Set.univ (menuHull bL bR) :=
  hullOf_concave _ _

/-- **The menu hull is `<= 0`** everywhere -- the zero-line seed caps it (`hullOf <= affineFn (0,0) = 0`). -/
theorem menuHull_nonpos (bL bR : ℝ) (m : ℝ) : menuHull bL bR m ≤ 0 := by
  simpa [menuHull, affineFn] using
    hullOf_le_seed [(-bL * (3 / 23), bL), (-bR * (3 / 23), bR)] (0, 0) m

/-- **The menu hull touches `0` at the tie** `mu = 3/23`: both tangents and the zero seed pass through
    `(3/23, 0)`, so their min is `0`. -/
theorem menuHull_tie (bL bR : ℝ) : menuHull bL bR (3 / 23) = 0 := by
  have hL : affineFn (-bL * (3 / 23), bL) (3 / 23) = 0 := by simp only [affineFn]; ring
  have hR : affineFn (-bR * (3 / 23), bR) (3 / 23) = 0 := by simp only [affineFn]; ring
  have h0 : affineFn ((0 : ℝ), (0 : ℝ)) (3 / 23) = 0 := by simp only [affineFn]; ring
  simp only [menuHull, hullOf_cons, hullOf_nil, hL, hR, h0, min_self]

/-! ## The concrete hull, wired into the proven capstone. -/

/-- **The s-tail holds for the concrete hull.**  Since `menuHull bL bR m <= 0`, `Qeq_stail` gives
    `Qeq s j (menuHull bL bR) m <= omega` for every `s >= 65`, `m ∈ [0,1]`. -/
theorem menuHull_Qeq_stail (bL bR : ℝ) (s j : ℕ) (m : ℝ) (hs : 65 ≤ s) (hm0 : 0 ≤ m) (hm : m ≤ 1) :
    Qeq s j (menuHull bL bR) m ≤ omegaVal :=
  Qeq_stail s j m hs hm0 hm (menuHull_nonpos bL bR m)

/-- **`SweepBound` for the concrete hull reduces to its finite `s <= 64` core.**  `menuHull` is `<= 0` on
    `[0,1]`, so `sweepBound_of_core` applies: the whole sweep for the concrete hull is discharged by the finite
    `s <= 64` core bound. -/
theorem menuHull_sweepBound_of_core (bL bR : ℝ)
    (hcore : ∀ s j m, s ≤ 64 → 0 < j → 0 ≤ m → m ≤ 1 → Qeq s j (menuHull bL bR) m ≤ omegaVal) :
    SweepBound (menuHull bL bR) :=
  sweepBound_of_core (fun m _ _ => menuHull_nonpos bL bR m) hcore

/-- **The multi-child per-node bound for the concrete hull.**  Instantiates `node_le_omega` with `menuHull`:
    given `SweepBound (menuHull bL bR)` and children below the hull, the node amplitude is `<= omega`. -/
theorem menuHull_node_le_omega (bL bR : ℝ) {s j : ℕ} (hj : 0 < j)
    (hSweep : SweepBound (menuHull bL bR)) (ell mu : Fin j → ℝ)
    (hmu : ∀ i, 0 ≤ mu i ∧ mu i ≤ 1) (hell : ∀ i, ell i ≤ menuHull bL bR (mu i)) :
    nodeAmp s j ell mu ≤ omegaVal :=
  node_le_omega hj (menuHull_concave bL bR) hSweep ell mu hmu hell

/-! ## The finite-core cell enumeration -- the reusable per-cell reduction.

Each cell of the `s <= 64` core fixes `(s, j)` and an `m`-interval `[·, m_hi]`.  On the cell the hull value is
bounded by its active tangent line (`menuHull_le_left/right`) and the coupling by its right-endpoint value
(`coupling_mono`), so `Qeq s j (menuHull bL bR) m <= omega` reduces to a RATIONAL check via `node_interval_le`
(Sweep.lean) -- exactly the per-cell inequality `gap_interval_certification.py` verifies.  `menuHull_cell_le`
is that reduction, the tool the enumeration instantiates over the `(s,j)`-grid x `m`-cells (as `grid_nodes`
does for the near-star grid). -/

/-- The hull is below its LEFT tangent line `y = bL (m - 3/23)` (active for small cavities). -/
theorem menuHull_le_left (bL bR m : ℝ) : menuHull bL bR m ≤ -bL * (3 / 23) + bL * m := by
  simpa [menuHull, affineFn] using
    hullOf_le_of_mem [(-bL * (3 / 23), bL), (-bR * (3 / 23), bR)] (0, 0) (-bL * (3 / 23), bL) m (by simp)

/-- The hull is below its RIGHT tangent line `y = bR (m - 3/23)` (active for large cavities). -/
theorem menuHull_le_right (bL bR m : ℝ) : menuHull bL bR m ≤ -bR * (3 / 23) + bR * m := by
  simpa [menuHull, affineFn] using
    hullOf_le_of_mem [(-bL * (3 / 23), bL), (-bR * (3 / 23), bR)] (0, 0) (-bR * (3 / 23), bR) m (by simp)

/-- **The per-cell reduction (the enumeration tool).**  For a core cell `(s, j)` with `m ∈ [·, m_hi]`, given a
    rational upper bound `gub` for `gVal(s+j)`, a rational lower bound `L` for `omega`, a cell upper bound `hub`
    for the hull value `menuHull bL bR m`, and a rational upper bound `cub` for the coupling log at the cell's
    RIGHT endpoint `m_hi`, the node bound `Qeq s j (menuHull bL bR) m <= omega` follows from the single rational
    inequality `gub - j·L + j·hub + cub <= L`.  Coupling monotonicity (`coupling_mono`) lifts the right-endpoint
    log bound to all `m` in the cell; `node_interval_le` closes it.  This is the finite-core analogue of
    `node_ns_le`: every cell is `menuHull_cell_le … (by norm_num)` once the rational data is supplied. -/
theorem menuHull_cell_le (bL bR : ℝ) (s j : ℕ) (m m_hi hub cub gub L : ℝ)
    (hm0 : 0 ≤ m) (hm_hi : m ≤ m_hi)
    (hg : gVal (s + j) ≤ gub) (hL : L ≤ omegaVal) (hHm : menuHull bL bR m ≤ hub)
    (hcoup_hi : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m_hi) / (4 * ((s : ℝ) + j) + 3)) ≤ cub)
    (hrat : gub - (j : ℝ) * L + (j : ℝ) * hub + cub ≤ L) :
    Qeq s j (menuHull bL bR) m ≤ omegaVal := by
  have hden : (0 : ℝ) < 4 * ((s : ℝ) + j) + 3 := by positivity
  have h3jm : (0 : ℝ) ≤ 3 * (j : ℝ) * m := mul_nonneg (by positivity) hm0
  have hnum : (0 : ℝ) < 4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m := by
    have h0 : (0 : ℝ) ≤ 4 * (s : ℝ) + 3 * (j : ℝ) := by positivity
    linarith [h3jm, h0]
  have hcoup_le : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3)) ≤ cub :=
    le_trans (Real.log_le_log (div_pos hnum hden) (coupling_mono s j hm_hi)) hcoup_hi
  have h := node_interval_le s j (menuHull bL bR m)
    ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3)) gub cub L hub
    (by positivity) hg hL hHm hcoup_le hrat
  unfold Qeq
  exact h

/-- **A rational upper bound for `gVal(n)`, uniform in `n`** -- the certified `gub` supply for the cell
    enumeration.  From `gVal n <= n·omega + lambda` (`gVal_le_linear`), `omega <= -77/10000`
    (`omega_enclosure`), and `lambda = log(4/3) - L <= 288/1000 - 1/20 = 238/1000` (`log_four_third_enclosure` +
    `Lval_ge_inv20`), so `gVal n <= -77 n/10000 + 238/1000`.  This removes the per-`n` transcendental `g`-bound
    obstacle: every cell's `gub` is this closed rational form. -/
theorem gVal_le_lin_rat (n : ℕ) : gVal n ≤ (n : ℝ) * (-77 / 10000) + 238 / 1000 := by
  have h1 := gVal_le_linear n
  have h2 : (n : ℝ) * omegaVal ≤ (n : ℝ) * (-77 / 10000) :=
    mul_le_mul_of_nonneg_left omega_enclosure.2.le (by positivity)
  have h3 : lambdaVal ≤ 238 / 1000 := by
    have hl := log_four_third_enclosure.2
    have hLv := Lval_ge_inv20
    unfold lambdaVal
    linarith
  linarith [h1, h2, h3]

/-- **A TIGHT rational upper bound for `gVal(n)`, uniform in `n`** -- the fix for the mid/large range
    `24 <= n <= 64` where `gVal_le_Rval` cannot `norm_num` (exponent `11n > 253`) and the loose `gVal_le_lin_rat`
    (`lambda <= 238/1000`) is `~0.16` slack.  The linear FORM `gVal n <= n*omega + lambda` (`gVal_le_linear`) is
    only `~log(1+1/(4n+3))` slack (`~0.007` at `n=36`); the earlier looseness was entirely the RATIONAL rounding
    of `lambda`.  Here `lambda = log(4/3) - Lval <= 288/1000 - (405/1000 + 77/10000)/2 = 1633/20000` (using the
    tight `Lval = (log(3/2) - omega)/2 >= 4127/20000` from `log_three_half_enclosure` + `omega_enclosure`), so
    `gVal n <= -77 n/10000 + 1633/20000` -- loose by only `~0.0075` at `n=36` (real `g(36) = -0.2031`, bound
    `-0.1956`).  This is the `gub` supply that lets the tie-adjacent / binding cells close (with fine cavity
    subdivision), the piece the loose `gVal_le_lin_rat` could not reach past the exact `gVal_le_Rval` range. -/
theorem gVal_le_lin_tight (n : ℕ) : gVal n ≤ (n : ℝ) * (-77 / 10000) + 1633 / 20000 := by
  have h1 := gVal_le_linear n
  have h2 : (n : ℝ) * omegaVal ≤ (n : ℝ) * (-77 / 10000) :=
    mul_le_mul_of_nonneg_left omega_enclosure.2.le (by positivity)
  have hLlow : (4127 : ℝ) / 20000 ≤ Lval := by
    have hL : Lval = (Real.log (3 / 2) - omegaVal) / 2 := by unfold omegaVal; ring
    rw [hL]; linarith [log_three_half_enclosure.1, omega_enclosure.2]
  have h3 : lambdaVal ≤ 1633 / 20000 := by
    have h43 := log_four_third_enclosure.2
    unfold lambdaVal; linarith [hLlow, h43]
  linarith [h1, h2, h3]

/-- **`gVal` is ANTITONE past the tie: `gVal (n+1) <= gVal n` for `n >= 5`** -- the foundational uniform
    monotonicity fact for collapsing the `s`-axis of the sweep (the near-star amplitude peaks at the tie `n=5`
    and decreases thereafter).  The exact difference telescopes to a single log:
    `gVal (n+1) - gVal n = omega + log((4n^2+11n+7)/(4n^2+11n+6))` (the `log(3/2)`/`Lval`/`log(4n+3)`/`log(3(n+1))`
    terms combine), which is `<= omega + 1/(4n^2+11n+6) <= omega + 1/161 < 0` for `n >= 5` (via `log x <= x-1`
    and `omega <= -77/10000`).  Uniform in `n` -- no per-`n` enumeration.  (For `n <= 4`, before the tie, `gVal`
    is increasing, so this is sharp at the tie `n=5`.) -/
theorem gVal_antitone (n : ℕ) (hn : 5 ≤ n) : gVal (n + 1) ≤ gVal n := by
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- The difference, keeping the `gVal (n+1)` log-arguments in their post-`push_cast` form.
  have hdiff : gVal (n + 1) - gVal n = omegaVal
      + (Real.log (4 * ((n : ℝ) + 1) + 3) - Real.log (4 * (n : ℝ) + 3)
         - Real.log (3 * (((n : ℝ) + 1) + 1)) + Real.log (3 * ((n : ℝ) + 1))) := by
    unfold gVal omegaVal; push_cast; ring
  -- Telescope the four logs into `log(P) + log(Q)` (the `3`s cancel in `Q`), each step unambiguous.
  have hA : Real.log (4 * ((n : ℝ) + 1) + 3) - Real.log (4 * (n : ℝ) + 3)
      = Real.log ((4 * ((n : ℝ) + 1) + 3) / (4 * (n : ℝ) + 3)) :=
    (Real.log_div (by positivity) (by positivity)).symm
  have hB : Real.log (3 * ((n : ℝ) + 1)) - Real.log (3 * (((n : ℝ) + 1) + 1))
      = Real.log (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    rw [← Real.log_div (by positivity) (by positivity),
      show (3 : ℝ) * (((n : ℝ) + 1) + 1) = 3 * ((n : ℝ) + 2) by ring,
      mul_div_mul_left ((n : ℝ) + 1) ((n : ℝ) + 2) (by norm_num : (3 : ℝ) ≠ 0)]
  have hcomb : Real.log ((4 * ((n : ℝ) + 1) + 3) / (4 * (n : ℝ) + 3))
      + Real.log (((n : ℝ) + 1) / ((n : ℝ) + 2))
      = Real.log ((4 * ((n : ℝ) + 1) + 3) / (4 * (n : ℝ) + 3) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) :=
    (Real.log_mul (by positivity) (by positivity)).symm
  have hlog : Real.log (4 * ((n : ℝ) + 1) + 3) - Real.log (4 * (n : ℝ) + 3)
      - Real.log (3 * (((n : ℝ) + 1) + 1)) + Real.log (3 * ((n : ℝ) + 1))
      = Real.log ((4 * ((n : ℝ) + 1) + 3) / (4 * (n : ℝ) + 3) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) := by
    rw [← hcomb, ← hA, ← hB]; ring
  -- `P*Q - 1 = 1/(4n^2+11n+6) <= 1/161` for `n >= 5`.
  have hval : (4 * ((n : ℝ) + 1) + 3) / (4 * (n : ℝ) + 3) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) - 1 ≤ 1 / 161 := by
    rw [div_mul_div_comm, div_sub_one (by positivity : (0:ℝ) < (4 * (n : ℝ) + 3) * ((n : ℝ) + 2)).ne',
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 5 by linarith)
      (show (0 : ℝ) ≤ 4 * (n : ℝ) + 31 by positivity)]
  have hlogle : Real.log (4 * ((n : ℝ) + 1) + 3) - Real.log (4 * (n : ℝ) + 3)
      - Real.log (3 * (((n : ℝ) + 1) + 1)) + Real.log (3 * ((n : ℝ) + 1)) ≤ 1 / 161 := by
    rw [hlog]; exact le_trans (Real.log_le_sub_one_of_pos (by positivity)) hval
  linarith [omega_enclosure.2, hdiff, hlogle]

/-- **The `s`-axis collapses for `m >= 1/3`: `Qeq` is antitone in `s` (past the tie).**  For cavity `m >= 1/3`
    and `s + j >= 5`, one step `s -> s+1` can only lower `Qeq`: the head `gVal (s+j)` decreases (`gVal_antitone`)
    and the coupling `(4s+3j+3+3jm)/(4(s+j)+3)` decreases in `s` -- its cross-multiplied `s`-difference is exactly
    `4 j (1-3m) <= 0`.  The `-j*omega` and `j*H(m)` terms are `s`-independent.  So in the `m >= 1/3` regime the
    worst `s` is the smallest, and no `s`-enumeration is needed -- the uniform collapse that replaces the literal
    grid's `s`-loop there. -/
theorem Qeq_s_antitone (s j : ℕ) (H : ℝ → ℝ) (m : ℝ) (hm : 1 / 3 ≤ m) (hsj : 5 ≤ s + j) :
    Qeq (s + 1) j H m ≤ Qeq s j H m := by
  have hg : gVal (s + 1 + j) ≤ gVal (s + j) := by
    have h := gVal_antitone (s + j) hsj
    rwa [show s + j + 1 = s + 1 + j from by omega] at h
  have hjm : (0 : ℝ) ≤ (j : ℝ) * (3 * m - 1) := mul_nonneg (by positivity) (by linarith)
  have hcast : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
  -- state the coupling bound in the `↑(s+1)` form so it matches the unfolded goal exactly
  have hC : (4 * ((s + 1 : ℕ) : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * (((s + 1 : ℕ) : ℝ) + j) + 3)
      ≤ (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3) := by
    rw [hcast, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hjm]
  have hlogC := Real.log_le_log
    (show (0 : ℝ) < (4 * ((s + 1 : ℕ) : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * (((s + 1 : ℕ) : ℝ) + j) + 3)
      by rw [hcast]; positivity) hC
  unfold Qeq
  linarith [hg, hlogC]

/-- **Full `s`-collapse for `m >= 1/3`:** `Qeq s j H m <= Qeq s0 j H m` for all `s >= s0` (with `s0 + j >= 5`).
    Iterating `Qeq_s_antitone` -- so the entire `s`-tail of the sweep, in the `m >= 1/3` regime, reduces to the
    single base `s0` (the smallest `s` with `s0 + j >= 5`).  Replaces the literal grid's `s`-enumeration there
    with one uniform theorem. -/
theorem Qeq_s_collapse (s0 s j : ℕ) (H : ℝ → ℝ) (m : ℝ) (hm : 1 / 3 ≤ m) (h0 : 5 ≤ s0 + j) (hs : s0 ≤ s) :
    Qeq s j H m ≤ Qeq s0 j H m := by
  induction s, hs using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (Qeq_s_antitone n j H m hm (by omega)) ih

/-! ## The concave-max-in-m for the near-tie region -- without subdivision.

Near the tie (`m < 1/3`) the `s`-collapse fails (coupling increases in `s`), so a whole cavity CELL must be
bounded at once.  The key: on a single hull SEGMENT `menuHullFull m <= affineFn ab m` is AFFINE in `m`
(`hullOf_le_of_mem`), the coupling `(4s+3j+3+3jm)/(4(s+j)+3)` is AFFINE in `m`, and `log(coupling) <= coupling-1`
(`Real.log_le_sub_one_of_pos`).  So the whole upper bound on `Qeq s j menuHullFull m` is AFFINE in `m`, hence its
maximum over `[ml, mr]` is at an endpoint (`affineFn_le_max_endpoints`) -- no `ConcaveOn` machinery, no
stationary point, no subdivision.  A single check at each endpoint closes an entire near-tie cell. -/

/-- **The affine (concave-max) cell bound.**  On a hull segment `ab` (so `H m <= affineFn ab m` -- for
    `menuHullFull` this is `hullOf_le_of_mem`), the upper bound on `Qeq` is affine in `m`, so
    `Qeq s j H m <= omega` for ALL `m in [ml, mr]` follows from the single rational check at each endpoint:
    `gub - j*L + j*(ab.1 + ab.2*e) + coupling(e) - 1 <= L` for `e in {ml, mr}`.  Generic in `H` (the caller
    supplies the affine domination); closes a whole near-tie cell in one shot (e.g. the wide `[3/23, 8/23]`
    the subdivided grid could not). -/
theorem Qeq_affine_cell_le {H : ℝ → ℝ} (s j : ℕ) (ab : ℝ × ℝ) (ml mr gub L : ℝ)
    (hml : 0 ≤ ml) (hg : gVal (s + j) ≤ gub) (hL : L ≤ omegaVal)
    (hdom : ∀ m, H m ≤ affineFn ab m)
    (hend_l : gub - (j : ℝ) * L + (j : ℝ) * (ab.1 + ab.2 * ml)
        + (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * ml) / (4 * ((s : ℝ) + j) + 3) - 1 ≤ L)
    (hend_r : gub - (j : ℝ) * L + (j : ℝ) * (ab.1 + ab.2 * mr)
        + (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * mr) / (4 * ((s : ℝ) + j) + 3) - 1 ≤ L) :
    ∀ m, ml ≤ m → m ≤ mr → Qeq s j H m ≤ omegaVal := by
  intro m hm1 hm2
  have hD : (0 : ℝ) < 4 * ((s : ℝ) + j) + 3 := by positivity
  have hml' : (0 : ℝ) ≤ m := le_trans hml hm1
  -- the affine upper bound `RHS(x)` equals `affineFn` of an explicit `(intercept, slope)`
  have hid : ∀ x : ℝ, gub - (j : ℝ) * L + (j : ℝ) * (ab.1 + ab.2 * x)
      + (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * x) / (4 * ((s : ℝ) + j) + 3) - 1
      = affineFn (gub - (j : ℝ) * L - 1 + (j : ℝ) * ab.1 + (4 * (s : ℝ) + 3 * j + 3) / (4 * ((s : ℝ) + j) + 3),
          (j : ℝ) * ab.2 + 3 * (j : ℝ) / (4 * ((s : ℝ) + j) + 3)) x := by
    intro x; simp only [affineFn]; field_simp [hD.ne']; ring
  have hmax := affineFn_le_max_endpoints
    (gub - (j : ℝ) * L - 1 + (j : ℝ) * ab.1 + (4 * (s : ℝ) + 3 * j + 3) / (4 * ((s : ℝ) + j) + 3),
      (j : ℝ) * ab.2 + 3 * (j : ℝ) / (4 * ((s : ℝ) + j) + 3)) ml mr m hm1 hm2
  rw [← hid ml, ← hid mr, ← hid m] at hmax
  have hRHS : gub - (j : ℝ) * L + (j : ℝ) * (ab.1 + ab.2 * m)
      + (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3) - 1 ≤ L :=
    le_trans hmax (max_le hend_l hend_r)
  have hlog : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3))
      ≤ (4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hjh : (j : ℝ) * H m ≤ (j : ℝ) * (ab.1 + ab.2 * m) := by
    have h := hdom m; simp only [affineFn] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hjw : -(j : ℝ) * omegaVal ≤ -(j : ℝ) * L := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) by positivity) (sub_nonneg.mpr hL)]
  unfold Qeq
  linarith [hg, hjh, hjw, hlog, hRHS, hL]

/-- **A worked finite-core cell, end to end.**  With tent slopes `(5, -1)`, the node `s = 0, j = 2` at cavity
    `m = 0` satisfies `Qeq <= omega`, discharged by `menuHull_cell_le` on concrete rational data: `gVal 2 <= 0`,
    hull value `menuHull 5 (-1) 0 <= -1/2` (via `menuHull_le_left`), coupling-log `log(9/11) <= -2/11` (via
    `Real.log_le_sub_one_of_pos`), `omega >= -78/10000`, and the rational check by `norm_num`.  This is the
    finite-core analogue of `Sweep.node_4_2_2`: every grid cell is such a one-liner on its certified data. -/
example : Qeq 0 2 (menuHull 5 (-1)) 0 ≤ omegaVal :=
  menuHull_cell_le 5 (-1) 0 2 0 0 (-1 / 2) (-2 / 11) 0 (-78 / 10000)
    (le_refl 0) (le_refl 0) (gVal_nonpos 2) omega_enclosure.1.le
    (le_trans (menuHull_le_left 5 (-1) 0) (by norm_num))
    (le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num))
    (by norm_num)

/-! ## A RATIONAL conservative hull for the near-star menu, with a DOMINATION proof.

The certified hull (`adversary_sweep.py`, 40 segments) has IRRATIONAL coefficients (transcendental `g`-values),
so the Lean hull uses a rational conservative OVER-approximation.  For the near-tie / right-of-tie region it is
the upper concave hull of the near-star points at their PROVEN rational amplitude bounds
`g(sp) <= {-1/20, -1/50, -1/100, -1/500, -1/2000, 0}` for `sp = 0..5` (from `gVal0_le..gVal4_le` + `gVal_nonpos`).
Its exact-Fraction tangent segments (hull vertices `sp = 5,4,3,0`) lie below every near-star menu point, so
`hullOf_dominates` applies.  Left of the tie (`cavity <= 3/23`) every amplitude is `<= 0` and each segment line
is `>= 0`, so the zero-line seed dominates -- covering all `sp >= 5` uniformly. -/

/-- The rational conservative near-star hull: 3 exact-Fraction tangent segments + zero-line seed. -/
noncomputable def menuHullRat : ℝ → ℝ :=
  hullOf [(19 / 8000, -437 / 24000), (41 / 8000, -57 / 1600), (1 / 100, -3 / 50)] (0, 0)

/-- Concave (the Jensen premise) -- free from `hullOf_concave`. -/
theorem menuHullRat_concave : ConcaveOn ℝ Set.univ menuHullRat := hullOf_concave _ _

/-- `<= 0` everywhere -- the zero-line seed caps it. -/
theorem menuHullRat_nonpos (m : ℝ) : menuHullRat m ≤ 0 := by
  simpa [menuHullRat, affineFn] using
    hullOf_le_seed [(19 / 8000, -437 / 24000), (41 / 8000, -57 / 1600), (1 / 100, -3 / 50)] (0, 0) m

/-- **Left-of-tie domination.**  Any amplitude `g <= 0` at cavity `x <= 3/23` lies below the rational hull:
    each segment `(a,b)` has `b < 0` and `a + b·(3/23) >= 0`, so `affineFn(a,b) x >= 0 >= g` for `x <= 3/23`;
    the zero seed gives `g <= 0`.  (Each per-segment `linarith` uses only `g <= 0` and `x <= 3/23`.) -/
theorem menuHullRat_dominates_left (x g : ℝ) (hg : g ≤ 0) (hx : x ≤ 3 / 23) : g ≤ menuHullRat x := by
  unfold menuHullRat
  refine hullOf_dominates _ _ g x ?_ ?_
  · simp only [affineFn]; linarith
  · intro ab hab
    fin_cases hab <;> simp only [affineFn] <;> linarith

/-- **The rational hull dominates the entire near-star menu.**  For every near-star level `sp`, the menu point
    `(3/(4sp+3), gVal sp)` lies below `menuHullRat`.  `sp >= 5` (cavity `<= 3/23`) via the left lemma +
    `gVal_nonpos`; `sp = 0..4` via the proved rational bounds `gVal{sp}_le` below each segment (`norm_num`). -/
theorem menuHullRat_dominates_nearstar (sp : ℕ) :
    gVal sp ≤ menuHullRat (3 / (4 * (sp : ℝ) + 3)) := by
  rcases Nat.lt_or_ge sp 5 with h | h
  · interval_cases sp
    · rw [show (3 / (4 * ((0 : ℕ) : ℝ) + 3)) = 1 by norm_num]
      unfold menuHullRat
      refine hullOf_dominates _ _ _ _ ?_ ?_
      · simp only [affineFn]; linarith [gVal_nonpos 0]
      · intro ab hab; fin_cases hab <;> simp only [affineFn] <;> linarith [gVal0_le]
    · rw [show (3 / (4 * ((1 : ℕ) : ℝ) + 3)) = 3 / 7 by norm_num]
      unfold menuHullRat
      refine hullOf_dominates _ _ _ _ ?_ ?_
      · simp only [affineFn]; linarith [gVal_nonpos 1]
      · intro ab hab; fin_cases hab <;> simp only [affineFn] <;> linarith [gVal1_le]
    · rw [show (3 / (4 * ((2 : ℕ) : ℝ) + 3)) = 3 / 11 by norm_num]
      unfold menuHullRat
      refine hullOf_dominates _ _ _ _ ?_ ?_
      · simp only [affineFn]; linarith [gVal_nonpos 2]
      · intro ab hab; fin_cases hab <;> simp only [affineFn] <;> linarith [gVal2_le]
    · rw [show (3 / (4 * ((3 : ℕ) : ℝ) + 3)) = 1 / 5 by norm_num]
      unfold menuHullRat
      refine hullOf_dominates _ _ _ _ ?_ ?_
      · simp only [affineFn]; linarith [gVal_nonpos 3]
      · intro ab hab; fin_cases hab <;> simp only [affineFn] <;> linarith [gVal3_le]
    · rw [show (3 / (4 * ((4 : ℕ) : ℝ) + 3)) = 3 / 19 by norm_num]
      unfold menuHullRat
      refine hullOf_dominates _ _ _ _ ?_ ?_
      · simp only [affineFn]; linarith [gVal_nonpos 4]
      · intro ab hab; fin_cases hab <;> simp only [affineFn] <;> linarith [gVal4_le]
  · refine menuHullRat_dominates_left _ _ (gVal_nonpos sp) ?_
    have h5 : (5 : ℝ) ≤ (sp : ℝ) := by exact_mod_cast h
    gcongr <;> linarith

/-! ## Deep-left tightening: a UNIFORM rational upper bound for `gVal`, and the accumulation obstruction.

Every near-star amplitude is `gVal n = log(Rval n)/11` with `Rval n` an EXACT rational (`Sweep.Rval`).  Since
`log x <= x - 1`, we get `gVal n <= (Rval n - 1)/11` -- a rational upper bound for EVERY `n`, strictly negative
for `sp >= 6`.  This removes the per-`n` transcendental obstacle on the deep left.

WHY A TIGHTER GLOBAL HULL IS OBSTRUCTED.  The bound `ghat(sp) = (Rval sp - 1)/11` is `> -1/11` (since
`Rval sp > 0`) and SATURATES at `-1/11` as `sp -> infinity`, while the real amplitude `g(sp) -> -infinity`
(cavity `-> 0`).  So the near-star menu is unbounded below near cavity `0`, but a rational concave `hullOf`
(inf of affines) cannot follow it: any negative left segment, extended toward cavity `0`, drops BELOW the
still-higher tail points (concavity), breaking `hullOf_dominates`.  Hence the deep-left region cannot be
tightened by a global rational concave hull -- an accumulation boundary at cavity `0`, the analogue of the
tie.  The correct deep-left device is the DIRECT per-child amplitude bound `gVal_le_Rval` (used inside the
Jensen sum `sum ell_i <= sum H(mu_i)`), not a global `H`.  `menuHullRat` therefore keeps the (correct,
dominating) zero seed on the left; `gVal_le_Rval` supplies the strictly-negative per-child bound the deep-left
cells actually use. -/

/-- **Uniform rational upper bound.**  `gVal n <= (Rval n - 1)/11` for every `n` (`Rval n` exact rational). -/
theorem gVal_le_Rval (n : ℕ) : gVal n ≤ (Rval n - 1) / 11 := by
  have h := Rval_eq n
  have hpos : (0 : ℝ) < Rval n := by unfold Rval; positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith [h, hlog]

/-- Deep-left amplitudes are provably strictly negative -- e.g. `gVal 6 <= -1/1000`
    (`(Rval 6 - 1)/11 ~ -0.0015`), by `gVal_le_Rval` + `norm_num` on the exact rational `Rval 6`. -/
example : gVal 6 ≤ -1 / 1000 := by
  have h := gVal_le_Rval 6
  have hr : (Rval 6 - 1) / 11 ≤ -1 / 1000 := by unfold Rval; norm_num
  linarith

/-- `gVal 8 <= -1/200` (`(Rval 8 - 1)/11 ~ -0.0083`). -/
example : gVal 8 ≤ -1 / 200 := by
  have h := gVal_le_Rval 8
  have hr : (Rval 8 - 1) / 11 ≤ -1 / 200 := by unfold Rval; norm_num
  linarith

/-! ## Wiring `gVal_le_Rval` into the deep-left cells: the RAW node bound (direct per-child sum, no hull).

Per the accumulation obstruction, the deep left bounds the RAW sum `Σ ell_i` directly by the per-child bound
`ell_i <= hub` (`hub` from `gVal_le_Rval`), rather than routing through a global concave `H`/Jensen.
`nodeAmp_deepleft_le` is the resulting node bound -- the same rational check as `node_interval_le`, but on
`nodeAmp` with `Σ ell_i <= j·hub` instead of the Jensen-collapsed `j·H(mubar)`. -/

/-- **The deep-left node bound (direct per-child).**  If every child amplitude is `<= hub` (its `gVal_le_Rval`
    bound), `gVal(s+j) <= gub`, `L <= omega`, the coupling-log `<= cub`, and `gub - j·L + j·hub + cub <= L`,
    then `nodeAmp s j ell mu <= omega`.  No Jensen / global hull -- `Σ ell_i <= j·hub` directly. -/
theorem nodeAmp_deepleft_le (s j : ℕ) (ell mu : Fin j → ℝ) (hub cub gub L : ℝ)
    (hell : ∀ i, ell i ≤ hub) (hg : gVal (s + j) ≤ gub) (hL : L ≤ omegaVal)
    (hlogc : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * ∑ i, mu i) / (4 * ((s : ℝ) + j) + 3)) ≤ cub)
    (hrat : gub - (j : ℝ) * L + (j : ℝ) * hub + cub ≤ L) :
    nodeAmp s j ell mu ≤ omegaVal := by
  have hjr : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hsum : (∑ i, ell i) ≤ (j : ℝ) * hub := by
    calc (∑ i, ell i) ≤ ∑ _i : Fin j, hub := Finset.sum_le_sum (fun i _ => hell i)
      _ = (j : ℝ) * hub := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hjw : -(j : ℝ) * omegaVal ≤ -(j : ℝ) * L := by nlinarith [hL, hjr]
  unfold nodeAmp
  linarith [hg, hsum, hlogc, hrat, hjw, hL]

/-- **A worked DEEP-LEFT node.**  Two near-star children at level `sp = 6` (cavity `3/27`, amplitude
    `<= -1/1000` by `gVal_le_Rval`) give `nodeAmp 0 2 <= omega` via `nodeAmp_deepleft_le` on concrete rationals
    -- the deep-left analogue of the mid-cavity worked cell, using the DIRECT per-child bound (not a global
    hull), the coupling-log `log(29/33) <= -4/33`, and the rational check by `norm_num`. -/
example : nodeAmp 0 2 (fun _ : Fin 2 => gVal 6) (fun _ : Fin 2 => (3 : ℝ) / 27) ≤ omegaVal := by
  have hg6 : gVal 6 ≤ -1 / 1000 := by
    have h := gVal_le_Rval 6
    have hr : (Rval 6 - 1) / 11 ≤ -1 / 1000 := by unfold Rval; norm_num
    linarith
  refine nodeAmp_deepleft_le 0 2 _ _ (-1 / 1000) (-4 / 33) 0 (-78 / 10000)
    (fun _ => hg6) (gVal_nonpos 2) omega_enclosure.1.le ?_ (by norm_num)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

/-! ## Chain / shoulder coverage -- the remaining two direct-per-child regions.

The near-star hull (mid) + deep-left cover cavities `<= 3/23` and the near-star points; the two remaining bands
are the E2 CHAIN region (cavity in `(2/5, 1/2)`, amplitude `<= -7/100`, the certified `chainB` bound) and the
E3 SHOULDER region (cavity in `(1/4, 1/3)`, amplitude `<= -9/100`, from the shoulder bound `log(1/(3mu)) - L`).
Both are DIRECT-per-child regions, so both are covered by the SAME generic tool `nodeAmp_deepleft_le` with the
region's amplitude bound as `hub`; the bounds themselves are the E2/E3 certificates (supplied as hypotheses,
exactly as `Sweep.node_chain_0_2`). -/

/-- **Chain-region node.**  Children in the E2 chain region (cavity `9/20 in (2/5,1/2)`, amplitude `<= -7/100`)
    give `nodeAmp 0 2 <= omega` via `nodeAmp_deepleft_le`; coupling `log(117/110) <= 7/110`. -/
example (ell : Fin 2 → ℝ) (hell : ∀ i, ell i ≤ -7 / 100) :
    nodeAmp 0 2 ell (fun _ : Fin 2 => (9 : ℝ) / 20) ≤ omegaVal := by
  refine nodeAmp_deepleft_le 0 2 ell _ (-7 / 100) (7 / 110) 0 (-78 / 10000)
    hell (gVal_nonpos 2) omega_enclosure.1.le ?_ (by norm_num)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

/-- **Shoulder-region node.**  Children in the E3 shoulder region (cavity `3/10 in (1/4,1/3)`, amplitude
    `<= -9/100`, from `log(1/(3mu)) - L`) give `nodeAmp 0 2 <= omega` via `nodeAmp_deepleft_le`; coupling
    `log(54/55) <= -1/55`. -/
example (ell : Fin 2 → ℝ) (hell : ∀ i, ell i ≤ -9 / 100) :
    nodeAmp 0 2 ell (fun _ : Fin 2 => (3 : ℝ) / 10) ≤ omegaVal := by
  refine nodeAmp_deepleft_le 0 2 ell _ (-9 / 100) (-1 / 55) 0 (-78 / 10000)
    hell (gVal_nonpos 2) omega_enclosure.1.le ?_ (by norm_num)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

/-! ## The grid instantiation: the hull-agnostic cell lemma, on the DOMINATING hull.

`menuHull_cell_le` was tied to the 2-tent `menuHull`; the grid needs it on the DOMINATING hull `menuHullRat`.
`Qeq_cell_le` is the same reduction, hull-agnostic (any `H` with `H m <= hub`), so it applies to `menuHullRat`
(and is the `H := menuHull` case of `menuHull_cell_le`).  A worked `menuHullRat` mid-cavity cell follows.

SCALE / STRUCTURE of the full grid (honest).  The finite `s <= 64` core is TWO-REGIME (mid-cavity Jensen-hull
cells via `Qeq_cell_le`+`menuHullRat`; deep-left/chain/shoulder via `nodeAmp_deepleft_le`), so it is not one
`SweepBound(menuHullRat)` -- that is FALSE where `menuHullRat` is loose (deep-left).  A full generation is
`~thousands` of `(s,j,seg)` cells with per-cell rational data, and has two data caveats: the `gVal(s+j)` bound
uses `gVal_le_Rval` only for `s+j <= 23` (`norm_num` exponent threshold 256) and `gVal_le_lin_rat` only for
`s+j >= 31` (it is positive/loose in between), and the tie-adjacent cells are thin-margin.  So the full grid is
the remaining MECHANICAL bulk; the tools (both cell lemmas, domination, the g-bounds) are all in place. -/

/-- **The hull-agnostic finite-core cell reduction.**  For ANY `H` with `H m <= hub`, the same rational check
    as `node_interval_le` (via `coupling_mono`) gives `Qeq s j H m <= omega`.  `menuHull_cell_le` is the
    `H := menuHull bL bR` instance; this version applies to the dominating hull `menuHullRat`. -/
theorem Qeq_cell_le {H : ℝ → ℝ} (s j : ℕ) (m m_hi hub cub gub L : ℝ)
    (hm0 : 0 ≤ m) (hm_hi : m ≤ m_hi)
    (hg : gVal (s + j) ≤ gub) (hL : L ≤ omegaVal) (hHm : H m ≤ hub)
    (hcoup_hi : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m_hi) / (4 * ((s : ℝ) + j) + 3)) ≤ cub)
    (hrat : gub - (j : ℝ) * L + (j : ℝ) * hub + cub ≤ L) :
    Qeq s j H m ≤ omegaVal := by
  have hden : (0 : ℝ) < 4 * ((s : ℝ) + j) + 3 := by positivity
  have h3jm : (0 : ℝ) ≤ 3 * (j : ℝ) * m := mul_nonneg (by positivity) hm0
  have hnum : (0 : ℝ) < 4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m := by
    have h0 : (0 : ℝ) ≤ 4 * (s : ℝ) + 3 * (j : ℝ) := by positivity
    linarith [h3jm, h0]
  have hcoup_le : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3)) ≤ cub :=
    le_trans (Real.log_le_log (div_pos hnum hden) (coupling_mono s j hm_hi)) hcoup_hi
  have h := node_interval_le s j (H m)
    ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * m) / (4 * ((s : ℝ) + j) + 3)) gub cub L hub
    (by positivity) hg hL hHm hcoup_le hrat
  unfold Qeq
  exact h

/-- **A worked mid-cavity grid cell on the DOMINATING hull `menuHullRat`.**  Node `(s=0, j=2)` at mean cavity
    `m = 3/19` (near-tie): `Qeq 0 2 menuHullRat (3/19) <= omega` via `Qeq_cell_le`, with `gVal 2 <= -1/100`
    (`gVal2_le`), `menuHullRat(3/19) <= -1/2000` (its `sp=4` tangent), coupling `log(189/209) <= -20/209`,
    `omega >= -78/10000`, rational check by `norm_num`. -/
example : Qeq 0 2 menuHullRat (3 / 19) ≤ omegaVal := by
  have hH : menuHullRat (3 / 19) ≤ -1 / 2000 := by
    have h := hullOf_le_of_mem [(19 / 8000, -437 / 24000), (41 / 8000, -57 / 1600), (1 / 100, -3 / 50)]
      (0, 0) (19 / 8000, -437 / 24000) (3 / 19) (by simp)
    have hval : affineFn (19 / 8000, -437 / 24000) (3 / 19) = (-1 / 2000 : ℝ) := by
      simp only [affineFn]; norm_num
    rw [hval] at h; exact h
  refine Qeq_cell_le 0 2 (3 / 19) (3 / 19) (-1 / 2000) (-20 / 209) (-1 / 100) (-78 / 10000)
    (by norm_num) (le_refl _) gVal2_le omega_enclosure.1.le hH ?_ (by norm_num)
  exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

/-! ## The INTERVAL cell lemma -- tiling the continuum of mean-cavities.

`Qeq_cell_le` bounds `Qeq` at a SINGLE mean-cavity `m`; a sound sweep must cover the whole reachable
`m`-continuum.  `Qeq_interval_le` upgrades it to `∀ m ∈ [ml, mr]` (using `coupling_mono`: the coupling is
increasing in `m`, so its cell-max is at the right endpoint `mr`), given a UNIFORM hull bound on the cell
(`H m ≤ hub` for all `m ∈ [ml, mr]`).  For `menuHullRat`, `menuHullRat_le_cell` supplies that uniform bound
from a chosen tangent segment via `Hull.hullOf_le_max_endpoints`.  Together they make each grid cell a single
rational check over a whole cavity interval -- the honest tiling tool the full grid needs. -/

/-- **Uniform hull bound on a cavity cell.**  For any tangent segment `ab` of `menuHullRat` and `m ∈ [ml, mr]`,
    `menuHullRat m ≤ max (affineFn ab ml) (affineFn ab mr)` -- a rational constant.  (Choose `ab` as the active
    tangent so the bound is tight.) -/
theorem menuHullRat_le_cell (ab : ℝ × ℝ)
    (hab : ab ∈ [((19 : ℝ) / 8000, -437 / 24000), (41 / 8000, -57 / 1600), (1 / 100, -3 / 50)])
    (ml mr m : ℝ) (h1 : ml ≤ m) (h2 : m ≤ mr) :
    menuHullRat m ≤ max (affineFn ab ml) (affineFn ab mr) :=
  hullOf_le_max_endpoints _ _ ab ml mr m hab h1 h2

/-- **The interval cell reduction.**  Given a uniform cell hull bound `hub` (`∀ m ∈ [ml, mr], H m ≤ hub`), a
    rational `gub ≥ gVal(s+j)`, `L ≤ ω`, and the coupling-log bound `cub` at the RIGHT endpoint `mr`, the single
    rational inequality `gub - j·L + j·hub + cub ≤ L` gives `Qeq s j H m ≤ ω` for EVERY `m ∈ [ml, mr]`.  Proof:
    each point reduces to `Qeq_cell_le` with `m_hi := mr`.  This is the per-cell lemma the grid instantiates. -/
theorem Qeq_interval_le {H : ℝ → ℝ} (s j : ℕ) (ml mr hub cub gub L : ℝ)
    (hml : 0 ≤ ml) (hg : gVal (s + j) ≤ gub) (hL : L ≤ omegaVal)
    (hHm : ∀ m, ml ≤ m → m ≤ mr → H m ≤ hub)
    (hcoup_hi : Real.log ((4 * (s : ℝ) + 3 * j + 3 + 3 * (j : ℝ) * mr) / (4 * ((s : ℝ) + j) + 3)) ≤ cub)
    (hrat : gub - (j : ℝ) * L + (j : ℝ) * hub + cub ≤ L) :
    ∀ m, ml ≤ m → m ≤ mr → Qeq s j H m ≤ omegaVal := by
  intro m hm_lo hm_hi
  exact Qeq_cell_le s j m mr hub cub gub L (le_trans hml hm_lo) hm_hi hg hL
    (hHm m hm_lo hm_hi) hcoup_hi hrat

/-- **A worked INTERVAL grid cell on the dominating hull.**  The binding column `j = 36` at `s = 0`, over the
    cavity cell `m ∈ [13/23, 18/23]`, satisfies `Qeq 0 36 menuHullRat m ≤ ω` -- one `Qeq_interval_le` call
    covering a continuum of mean-cavities, with the uniform hull bound `menuHullRat m ≤ -11/460` from the ACTIVE
    (`sp=3`) tangent `(1/100, -3/50)` via `menuHullRat_le_cell` (all three named tangents are decreasing, so the
    cell max is at the left endpoint `13/23`).  Data (`gub = -49/1250`, `cub = 372/1127`) is exactly what
    `grid_gen.py` computes and self-verifies in `Fraction` arithmetic; `Grid.lean` holds a CI-verified block of
    such cells for the binding column and its neighbours. -/
example : ∀ m, (13 : ℝ) / 23 ≤ m → m ≤ 18 / 23 →
    Qeq 0 36 menuHullRat m ≤ omegaVal := by
  refine Qeq_interval_le 0 36 (13 / 23) (18 / 23) (-11 / 460) (372 / 1127) (-49 / 1250)
    (-78 / 10000) (by norm_num) (le_trans (gVal_le_lin_rat (0 + 36)) (by norm_num)) omega_enclosure.1.le
    ?_ ?_ (by norm_num)
  · intro m h1 h2
    refine le_trans (menuHullRat_le_cell (1 / 100, -3 / 50) (by simp) (13 / 23) (18 / 23) m h1 h2) ?_
    simp only [affineFn, max_le_iff]; constructor <;> norm_num
  · exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

end R3Cert
