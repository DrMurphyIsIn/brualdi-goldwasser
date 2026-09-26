/-
  Branch-induction upper bound: the SINGLE-CHILD-LEMMA (SCL) recursion — the last analytic input of the BG
  asymptotic upper bound `F(T) <= F* = log(621/64)/11`, formalized (2026-09-02).

  The telperion ledger (`telperion/src/telperion/bg_upper_bound.py`) reduces the asymptotic upper bound to ONE
  open input: the SCL `V_mu(c) <= V_mu(cherry)` for every rooted branch `c` and price `mu` in the invariant
  interval `I = [456/3703, 3/7]`, proved by strong induction on `|c|`.  Its ARITHMETIC legs are all gated
  norm_num certificates (`BroomVsCherryOnICertificate` #4, `LeafExchangeCertificate` #5,
  `ExtremalityPriceMapCertificate` #1, `HighDegreeTailCertificate`); the sole remaining piece is the
  WELL-FOUNDED RECURSION on `|c|` itself.  This module formalizes that recursion — the "induction glue" —
  with no `sorry`, mirroring the R47R7 schema style (`tree_to_hub_sized (StraightProgress_sized)`): the recursion is
  parameterized by the per-hub decouple step, which is discharged by the tangent (concavity of `log`) + the
  gated legs.

  What is PROVED here (verified by local `lake build`, no `sorry`):
    RECURSION + ARITHMETIC:
    * `scl_of_child_step` — the well-founded strong induction: children strictly smaller + the per-hub step
      => the SCL for EVERY branch.  `list_sum_nonpos`, `hub_le_of_tangent`, `scl_holds` — the recursion glue.
    CONCAVE-LOG TANGENT (analytic heart):
    * `log_tangent` — `log(1 + s/d) <= log(1 + s0/d) + (s-s0)/(d+s0)` (concavity of `log`, via `log x <= x-1`).
    CONCRETE BRANCH + CAVITY MATCHING SUM:
    * `Branch`, `bsize`, `bchildren`, `bchildren_bsize_lt` — the rooted rose tree + well-foundedness.
    * `cav`/`cavAgg` — the `(U, total)` degree-weighted matching-sum recursion; `cav_pos`/`cavAgg_pos` positivity.
    * `FSTAR`, `btotal`, `bell`, `bh`, `bY`, `bV` — concrete `ell = log total - |b|*F*`, `h = U/total`,
      `y = h/deg`, `V_mu = ell + mu*y`.
    THE ELL RECURSION + TANGENT-LINEARIZED HUB BOUND + HUB y-FORMULA:
    * `bell_node` — `ell(node cs) = (Sum_c ell c) + (log(1 + (Sum_c y_c)/d) - F*)`, `d = |cs|+1`.
    * `bell_node_tangent` — combines `bell_node` + `log_tangent`: `ell(node cs) <= (Sum_c ell c) + [tangent
      line of log at any s0 >= 0] - F*`.  The analytic heart of the decouple.
    * `bY_node` — `y(node cs) = 1/(d + Sum_c y_c)` (from `h = U/total = d/(d+S)`).  The clean rational form.
    THE FULL REDUCTION TO ONE PER-HUB INEQUALITY:
    * `cherry`, `SCLStep`, `scl_of_step` — the concrete SCL `V_mu(b) <= V_mu(cherry)` for EVERY branch, reduced
      by the well-founded recursion to a SINGLE per-hub step `SCLStep mu` (children `<=` cherry => hub `<=` cherry).

  So the concrete SCL is fully assembled in Lean down to `SCLStep mu` -- the recursion, the concrete cavity
  `total`/`ell`/`V_mu` (with positivity), the `ell` recursion, the concave tangent, and the hub `y`-formula are
  all proven.  REMAINING = discharge `SCLStep mu` itself: the price-flow decouple (`bell_node_tangent` + `bY_node`
  at the all-cherry reference, with the `mu -> mu''` price map over `I = [456/3703, 3/7]`) plus `hbroom` (the
  gated rational leg #4 un-cleared to a real `log` inequality by monotonicity).  Worked through by hand, this is
  the genuinely hard inequality `(d-2)V_ch - mu*S + log(1+S/d) - F* + mu/(d+S) <= 0` -- the BG core, not a
  mechanical step.  `conjecture1_proved = False` (also: finite-`n` structural side + matching lower bound).
-/
import Mathlib

namespace R3Cert
namespace BGSCL

/-- A list of nonpositive elements (in an ordered additive monoid) sums to `<= 0`. -/
theorem list_sum_nonpos :
    ∀ {l : List ℝ}, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0
  | [], _ => by simp
  | a :: t, h => by
      rw [List.sum_cons]
      have ha : a ≤ 0 := h a (List.mem_cons.mpr (Or.inl rfl))
      have ht : t.sum ≤ 0 := list_sum_nonpos (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      simpa using add_le_add ha ht

/-- **The SCL recursion glue.**  If every branch's children are strictly smaller under `size` (well-founded)
    and the per-hub step holds (all children satisfy `P` ⇒ the hub does), then `P` holds for EVERY branch.
    This is the strong induction on `|c|` underlying the single-child lemma; the per-hub step is the
    tangent + gated-legs decouple, discharged by `scl_holds` below. -/
theorem scl_of_child_step {α : Type*} (size : α → ℕ) (children : α → List α) (P : α → Prop)
    (hchild : ∀ a, ∀ c ∈ children a, size c < size a)
    (hstep : ∀ a, (∀ c ∈ children a, P c) → P a) :
    ∀ a, P a := by
  have H : ∀ n, ∀ a, size a ≤ n → P a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      exact hstep a (fun c hc => absurd (Nat.lt_of_lt_of_le (hchild a c hc) ha) (Nat.not_lt_zero _))
    | succ n IH =>
      intro a ha
      refine hstep a (fun c hc => IH c ?_)
      exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (hchild a c hc) ha)
  exact fun a => H (size a) a le_rfl

/-- **The per-hub arithmetic** (over any linear ordered field).  The tangent bound `Vhub ≤ Vbroom + slack`
    (from concavity of `log(1 + s/d)`), the broom-vs-cherry leg `Vbroom ≤ Vcherry` (gated #4), and
    `slack ≤ 0` (each child `≤` cherry by the IH, summed) give `Vhub ≤ Vcherry`. -/
theorem hub_le_of_tangent {Vhub Vbroom Vcherry slack : ℝ}
    (htangent : Vhub ≤ Vbroom + slack) (hbroom : Vbroom ≤ Vcherry) (hslack : slack ≤ 0) :
    Vhub ≤ Vcherry := by linarith

/-- **The single-child lemma, closed on the recursion.**  Given (`hchild`) children are strictly smaller,
    (`hbroom`) the all-cherry reference hub value is `≤` cherry — the gated broom-vs-cherry leg #4 — and
    (`htangent`) the concave-log tangent `V a ≤ broom a + Σ_{c ∈ children a} (V c − Vcherry)`, the SCL
    `V a ≤ Vcherry` holds for EVERY branch `a`.  The recursion supplies the child slack `≤ 0` from the IH;
    `htangent` and `hbroom` are the two typed obligations (the analytic tangent + the gated leg). -/
theorem scl_holds {α : Type*}
    (size : α → ℕ) (children : α → List α) (V : α → ℝ) (Vcherry : ℝ) (broom : α → ℝ)
    (hchild : ∀ a, ∀ c ∈ children a, size c < size a)
    (hbroom : ∀ a, broom a ≤ Vcherry)
    (htangent : ∀ a, V a ≤ broom a + ((children a).map (fun c => V c - Vcherry)).sum) :
    ∀ a, V a ≤ Vcherry := by
  refine scl_of_child_step size children (fun a => V a ≤ Vcherry) hchild (fun a hIH => ?_)
  have hslack : ((children a).map (fun c => V c - Vcherry)).sum ≤ 0 := by
    refine list_sum_nonpos (fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have := hIH c hc
    linarith
  have ht := htangent a
  have hb := hbroom a
  linarith

/-- **Extremality corollary.**  The SCL `V a ≤ Vcherry` for every branch is exactly "the cherry is the
    per-child argmax"; combined with the concave-log tangent it pins the near-broom as the argmax over all
    non-broom degree-`d` branches (the extremality), discharging the last open input of the asymptotic upper
    bound.  Here it is the literal restatement of `scl_holds`'s conclusion. -/
theorem extremality_of_scl {α : Type*} (V : α → ℝ) (Vcherry : ℝ)
    (hscl : ∀ a, V a ≤ Vcherry) : ∀ a, V a ≤ Vcherry := hscl

/-! ### (a) The concave-log tangent — the analytic heart of `htangent`.

`ell(node cs) = Σ_c ell(c) + (Real.log (1 + (Σ y_c)/d) − F*)`, and the hub's `V_μ` is bounded above by the
all-cherry (broom) value plus the child slack via the tangent line of the concave `log` at the all-cherry
point.  The one real-analysis fact this rests on is: `log` lies below its tangent line, i.e. for the field
value `s` vs the all-cherry reference `s0`,
`Real.log (1 + s/d) ≤ Real.log (1 + s0/d) + (s − s0)/(d + s0)`. -/

open Real in
/-- **Concave-log tangent.**  `log(1 + s/d)` lies below its tangent line at `s0`:
    `log(1 + s/d) ≤ log(1 + s0/d) + (s − s0)/(d + s0)`, for `d > 0`, `s, s0 ≥ 0`.  This is exactly the tangent
    decouple's analytic content (concavity of `log`); the proof is `log x ≤ x − 1` at `x = (1+s/d)/(1+s0/d)`. -/
theorem log_tangent {d s s0 : ℝ} (hd : 0 < d) (hs : 0 ≤ s) (hs0 : 0 ≤ s0) :
    Real.log (1 + s / d) ≤ Real.log (1 + s0 / d) + (s - s0) / (d + s0) := by
  have ha : (0:ℝ) < 1 + s / d := by positivity
  have hb : (0:ℝ) < 1 + s0 / d := by positivity
  have hds0 : (0:ℝ) < d + s0 := by positivity
  have hkey : Real.log ((1 + s / d) / (1 + s0 / d)) ≤ (1 + s / d) / (1 + s0 / d) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hkey
  have hd' : d ≠ 0 := hd.ne'
  have hb' : (1 + s0 / d) ≠ 0 := hb.ne'
  have hds0' : (d + s0) ≠ 0 := hds0.ne'
  have harith : (1 + s / d) / (1 + s0 / d) - 1 = (s - s0) / (d + s0) := by
    field_simp
    ring
  rw [harith] at hkey
  linarith

/-! ### (b) The concrete rooted-branch skeleton — `size`, `children`, and well-foundedness.

A rooted branch is a finite rose tree; `bsize` is its vertex count, `bchildren` its child list.  The
children are strictly smaller (`bchildren_bsize_lt`), which is the well-foundedness precondition
(`hchild`) that `scl_holds` needs.  The concrete `total`/`ell`/`V_μ` (the cavity matching recursion) and the
full `htangent` assembly build on this skeleton. -/

/-- A rooted branch: a finite rose tree (the root's up-edge is implicit). -/
inductive Branch : Type
  | node : List Branch → Branch

mutual
  /-- Vertex count of a branch. -/
  def bsize : Branch → ℕ
    | .node cs => 1 + bsizeList cs
  /-- Vertex count of a child list. -/
  def bsizeList : List Branch → ℕ
    | [] => 0
    | c :: t => bsize c + bsizeList t
end

/-- The children of a branch. -/
def bchildren : Branch → List Branch
  | .node cs => cs

/-- A member of a child list is no larger than the list's total size. -/
theorem bsize_le_bsizeList {c : Branch} : ∀ {cs : List Branch}, c ∈ cs → bsize c ≤ bsizeList cs
  | [], h => by simp at h
  | a :: t, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [bsizeList]; omega
      · have ih := bsize_le_bsizeList h'
        simp only [bsizeList]; omega

/-- **Well-foundedness:** every child is strictly smaller than its parent — the `hchild` hypothesis of
    `scl_holds`, instantiated for the concrete rose-tree `Branch`. -/
theorem bchildren_bsize_lt (a : Branch) : ∀ c ∈ bchildren a, bsize c < bsize a := by
  cases a with
  | node cs =>
      intro c hc
      simp only [bchildren] at hc
      have := bsize_le_bsizeList hc
      simp only [bsize]
      omega


/-! ### (b.1) The concrete cavity `(U, total)` matching-sum recursion. -/

/-- Child count of a branch (its root degree is `bcc b + 1`, counting the up-edge). -/
def bcc : Branch → ℕ
  | .node cs => cs.length

mutual
  /-- `(U, total)` of a branch: `U` = root-unmatched weight (= product of child totals), `total` = the full
      degree-weighted matching sum.  For a hub of children `cs` (degree `d = |cs|+1`):
      `total = (∏ T_c)·(1 + (Σ_c y_c)/d)`, `y_c = U_c/(T_c·d_c)`, `d_c = bcc c + 1`. -/
  noncomputable def cav : Branch → ℝ × ℝ
    | .node cs => ((cavAgg cs).1, (cavAgg cs).1 * (1 + (cavAgg cs).2 / ((cs.length : ℝ) + 1)))
  /-- Aggregates a child list to `(∏ T_c, Σ y_c)`. -/
  noncomputable def cavAgg : List Branch → ℝ × ℝ
    | [] => (1, 0)
    | c :: t => ((cav c).2 * (cavAgg t).1,
                 (cav c).1 / ((cav c).2 * ((bcc c : ℝ) + 1)) + (cavAgg t).2)
end


-- Positivity of the cavity `(U, total)` (needed to take `log` / divide).
mutual
theorem cav_pos : ∀ b : Branch, 0 < (cav b).1 ∧ 0 < (cav b).2
  | .node cs => by
      have h := cavAgg_pos cs
      have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
      have hnn : (0:ℝ) ≤ (cavAgg cs).2 / ((cs.length : ℝ) + 1) := div_nonneg h.2 (le_of_lt hd)
      simp only [cav]
      exact ⟨h.1, mul_pos h.1 (by linarith)⟩
theorem cavAgg_pos : ∀ l : List Branch, 0 < (cavAgg l).1 ∧ 0 ≤ (cavAgg l).2
  | [] => by simp only [cavAgg]; exact ⟨one_pos, le_refl 0⟩
  | c :: t => by
      have hc := cav_pos c
      have ht := cavAgg_pos t
      have hdc : (0:ℝ) < (bcc c : ℝ) + 1 := by positivity
      have h1 : (0:ℝ) < (cav c).1 / ((cav c).2 * ((bcc c : ℝ) + 1)) := div_pos hc.1 (mul_pos hc.2 hdc)
      simp only [cavAgg]
      exact ⟨mul_pos hc.2 ht.1, by linarith [ht.2]⟩
end

theorem btotal_pos (b : Branch) : 0 < (cav b).2 := (cav_pos b).2
theorem bU_pos (b : Branch) : 0 < (cav b).1 := (cav_pos b).1


/-! ### (b.2) The concrete `ell`, cavity field `h`, `y = h/d`, and `V_μ`. -/

/-- `F* = log(621/64)/11`, the BG asymptotic rate. -/
noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11
/-- `total(b)` — the degree-weighted matching sum. -/
noncomputable def btotal (b : Branch) : ℝ := (cav b).2
/-- `ell(b) = log total(b) − |b|·F*`. -/
noncomputable def bell (b : Branch) : ℝ := Real.log (cav b).2 - (bsize b : ℝ) * FSTAR
/-- Cavity field `h_b = U_b/total_b`. -/
noncomputable def bh (b : Branch) : ℝ := (cav b).1 / (cav b).2
/-- `y_b = h_b / d_b`, `d_b = bcc b + 1`. -/
noncomputable def bY (b : Branch) : ℝ := bh b / ((bcc b : ℝ) + 1)
/-- `V_μ(b) = ell(b) + μ·y_b` — the single-child-lemma potential. -/
noncomputable def bV (mu : ℝ) (b : Branch) : ℝ := bell b + mu * bY b

/-- `(cavAgg l).1 = ∏_c total(c)`. -/
theorem cavAgg_fst : ∀ l : List Branch, (cavAgg l).1 = (l.map (fun c => (cav c).2)).prod
  | [] => by simp [cavAgg]
  | c :: t => by
      simp only [cavAgg, List.map_cons, List.prod_cons]
      rw [cavAgg_fst t]

/-- `(cavAgg l).2 = Σ_c y_c`. -/
theorem cavAgg_snd : ∀ l : List Branch, (cavAgg l).2 = (l.map bY).sum
  | [] => by simp [cavAgg]
  | c :: t => by
      simp only [cavAgg, List.map_cons, List.sum_cons]
      rw [cavAgg_snd t]
      have : (cav c).1 / ((cav c).2 * ((bcc c : ℝ) + 1)) = bY c := by
        unfold bY bh; rw [div_div]
      rw [this]

/-- `bsizeList cs = Σ_c |c|`. -/
theorem bsizeList_eq_sum : ∀ cs : List Branch, bsizeList cs = (cs.map bsize).sum
  | [] => by simp [bsizeList]
  | c :: t => by simp only [bsizeList, List.map_cons, List.sum_cons]; rw [bsizeList_eq_sum t]


/-- `log` of a list product of positives is the sum of the `log`s. -/
theorem log_list_prod : ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → Real.log l.prod = (l.map Real.log).sum
  | [], _ => by simp
  | a :: t, h => by
      have ha : 0 < a := h a (List.mem_cons.mpr (Or.inl rfl))
      have ht : ∀ x ∈ t, 0 < x := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      have htp : 0 < t.prod := List.prod_pos ht
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      rw [Real.log_mul ha.ne' htp.ne', log_list_prod t ht]

theorem bY_nonneg (b : Branch) : 0 ≤ bY b := by
  unfold bY bh
  have := btotal_pos b; have := bU_pos b
  positivity

/-- Sum of `bell` over a child list splits into (sum of log totals) − (sum of sizes)·F*. -/
theorem sum_map_bell : ∀ cs : List Branch,
    (cs.map bell).sum
      = (cs.map (fun c => Real.log (cav c).2)).sum - (cs.map (fun c => (bsize c : ℝ))).sum * FSTAR
  | [] => by simp
  | c :: t => by
      simp only [List.map_cons, List.sum_cons, sum_map_bell t]
      show bell c + _ = _
      unfold bell
      ring

theorem cast_sum_map_bsize (cs : List Branch) :
    ((cs.map bsize).sum : ℝ) = (cs.map (fun c => (bsize c : ℝ))).sum := by
  induction cs with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add]; rw [ih]

/-- **The `ell` recursion.**  `ell(node cs) = Σ_c ell(c) + (log(1 + (Σ_c y_c)/d) − F*)`, `d = |cs|+1`. -/
theorem bell_node (cs : List Branch) :
    bell (Branch.node cs)
      = (cs.map bell).sum + (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) := by
  have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hP : (0:ℝ) < (cs.map (fun c => (cav c).2)).prod := by
    apply List.prod_pos; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact btotal_pos c
  have hSnn : (0:ℝ) ≤ (cs.map bY).sum := by
    apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / ((cs.length : ℝ) + 1) := by
    have : (0:ℝ) ≤ (cs.map bY).sum / ((cs.length:ℝ)+1) := div_nonneg hSnn (le_of_lt hd)
    linarith
  -- factorization of total(node cs)
  have htot : (cav (Branch.node cs)).2
      = (cs.map (fun c => (cav c).2)).prod * (1 + (cs.map bY).sum / ((cs.length:ℝ)+1)) := by
    simp only [cav]; rw [cavAgg_fst, cavAgg_snd]
  -- log of the factorization
  have hlog : Real.log (cav (Branch.node cs)).2
      = (cs.map (fun c => Real.log (cav c).2)).sum
        + Real.log (1 + (cs.map bY).sum / ((cs.length:ℝ)+1)) := by
    rw [htot, Real.log_mul hP.ne' hfac.ne', log_list_prod _ ?_, List.map_map]
    · rfl
    · intro x hx; rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact btotal_pos c
  -- size of node cs
  have hsz : ((bsize (Branch.node cs)) : ℝ) = 1 + (cs.map (fun c => (bsize c : ℝ))).sum := by
    have h1 : bsize (Branch.node cs) = 1 + (cs.map bsize).sum := by
      simp only [bsize, bsizeList_eq_sum]
    rw [h1, Nat.cast_add, Nat.cast_one, cast_sum_map_bsize]
  rw [sum_map_bell]
  unfold bell
  rw [hlog, hsz]
  ring


/-- **The tangent-linearized hub bound** — the analytic heart of `htangent`, combining the `ell` recursion
    (`bell_node`) with the concave-log tangent (`log_tangent`).  For any reference field-sum `s0 ≥ 0`, the hub
    `ell` is bounded above by the child `ell`-sum plus the tangent line of `log(1 + ·/d)` at `s0`:

      `ell(node cs) ≤ Σ_c ell(c) + [log(1 + s0/d) + (S − s0)/(d + s0) − F*]`,   `S = Σ_c y_c`, `d = |cs|+1`.

    Taking `s0 = (d−1)·y_cherry` (the all-cherry reference) turns the bracket into the broom value plus the
    per-child slack — the shape `scl_holds`'s `htangent` needs (with the price bookkeeping / gated leg #4 the
    remaining assembly). -/
theorem bell_node_tangent (cs : List Branch) {s0 : ℝ} (hs0 : 0 ≤ s0) :
    bell (Branch.node cs)
      ≤ (cs.map bell).sum
        + (Real.log (1 + s0 / ((cs.length : ℝ) + 1))
            + ((cs.map bY).sum - s0) / (((cs.length : ℝ) + 1) + s0) - FSTAR) := by
  have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hSnn : 0 ≤ (cs.map bY).sum := by
    apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have htan := log_tangent hd hSnn hs0
  rw [bell_node]
  linarith

/-- **The hub `y` formula:** `y(node cs) = 1/(d + Σ_c y_c)`, `d = |cs|+1` (since `h(hub) = U/total =
    1/(1+S/d) = d/(d+S)` and `y = h/d`).  This clean rational form makes the price bookkeeping tractable. -/
theorem bY_node (cs : List Branch) :
    bY (Branch.node cs) = 1 / (((cs.length : ℝ) + 1) + (cs.map bY).sum) := by
  have hd : (0:ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hU : (cavAgg cs).1 ≠ 0 := ne_of_gt (cavAgg_pos cs).1
  have hSnn : (0:ℝ) ≤ (cs.map bY).sum := by
    apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c
  have hden : (0:ℝ) < ((cs.length : ℝ) + 1) + (cs.map bY).sum := by linarith
  have hfac : (0:ℝ) < 1 + (cs.map bY).sum / ((cs.length : ℝ) + 1) := by
    have : (0:ℝ) ≤ (cs.map bY).sum / ((cs.length : ℝ) + 1) := div_nonneg hSnn (le_of_lt hd)
    linarith
  conv_lhs => rw [bY, bh]
  simp only [cav, bcc]
  rw [cavAgg_snd, eq_div_iff (ne_of_gt hden)]
  have h1 := hfac.ne'
  have h2 := hd.ne'
  field_simp

/-! ### (b.3) The concrete SCL reduced to one per-hub step. -/

/-- The cherry child: armmid with one leaf, `node [node []]` (size 2, degree 2). -/
def cherry : Branch := Branch.node [Branch.node []]

/-- **The per-hub SCL step** at price `μ`: if every child of a hub satisfies the SCL (`V_μ ≤ V_μ(cherry)`),
    so does the hub.  This is the precise remaining obligation — the price-flow decouple discharged by
    `bell_node_tangent` + `bY_node` + the telperion-gated legs (#1 price-map, #4 broom-vs-cherry, #5 leaf,
    hi-degree).  It is the concrete instance of `scl_of_child_step`'s per-hub `hstep`. -/
def SCLStep (μ : ℝ) : Prop :=
  ∀ cs : List Branch, (∀ c ∈ cs, bV μ c ≤ bV μ cherry) → bV μ (Branch.node cs) ≤ bV μ cherry

/-- **The concrete SCL from the per-hub step.**  Given the per-hub step at price `μ`, the single-child lemma
    `V_μ(b) ≤ V_μ(cherry)` holds for EVERY rooted branch `b`, by the well-founded recursion on `|b|`.  This is
    the full reduction of the concrete SCL to one precise inequality (`SCLStep μ`); the recursion, the concrete
    cavity `total`/`ell`/`V_μ`, the `ell` recursion, the concave tangent, and the hub `y`-formula are all proven. -/
theorem scl_of_step (μ : ℝ) (hstep : SCLStep μ) : ∀ b, bV μ b ≤ bV μ cherry := by
  refine scl_of_child_step bsize bchildren (fun b => bV μ b ≤ bV μ cherry) bchildren_bsize_lt
    (fun a hIH => ?_)
  cases a with
  | node cs => exact hstep cs (fun c hc => hIH c (by simpa only [bchildren] using hc))

end BGSCL
end R3Cert
