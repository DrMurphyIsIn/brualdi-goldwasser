/-
  Toward formalizing R3's finite interval sweep (Phi<=1 for multi-child DEC nodes).

  After the Jensen reduction (adversary_sweep.py), Phi<=1 for a node with j>=2 non-arm children reduces to
  `Q(s,j,m) <= omega` over a finite (s,j) core (s<=64, j<=500) plus two explicit TAIL inequalities (D1 for
  s>=65, D2 for j>500), where omega = log(3/2)-2L, L = log(621/64)/11, lambda = log(4/3)-L.

  STATUS (honest).  The TAILS clear to EXACT rational/integer inequalities (the same "clear the 11th root"
  trick as the cruxes), and are machine-checked here:
    * `s_tail` (D1): 65*omega + lambda + log(3/2) <= omega, reduced to the integer fact 3^317*2^81 <= 23^129.
  The finite CORE, by contrast, does NOT reduce to exact rationals: the adversary may place children on the
  E2 chain-region bound, whose value accumulates at the transcendental fixed point sqrt(2)-1 (the integrality
  obstruction -- no smooth/rational certificate exists).  So the core genuinely requires interval arithmetic
  over `Real.log`, which is not formalized here (a substantial computational-formalization, Flyspeck-style).
  This file records the tail that IS exactly formalizable and delimits precisely what remains.
-/
import Mathlib

namespace R3Cert

open Real

/-- `L = log rho_B = (1/11) log(621/64)`. -/
noncomputable def Lval : ℝ := Real.log (621 / 64) / 11
/-- `omega = log Phi(ARM) = log(3/2) - 2L`. -/
noncomputable def omegaVal : ℝ := Real.log (3 / 2) - 2 * Lval
/-- `lambda = log(4/3) - L`. -/
noncomputable def lambdaVal : ℝ := Real.log (4 / 3) - Lval

/-- The near-star amplitude `g(n) = n log(3/2) - (1+2n)L + log(4n+3) - log(3(n+1))`. -/
noncomputable def gVal (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (3 / 2) - (1 + 2 * (n : ℝ)) * Lval + Real.log (4 * (n : ℝ) + 3)
    - Real.log (3 * ((n : ℝ) + 1))

/-- **The reusable engine for the exact-arithmetic part of the sweep:** `11 * g(n)` is the `log` of an exact
    rational (clearing the 11th root, `11 L = log(621/64)`).  Every near-star-child node bound `Q <= omega`
    thus reduces to an exact RATIONAL inequality (no interval arithmetic): exponentiate by 11, and each `g`
    and `omega` becomes `log(rational)`, so `Q <= omega` iff a product of rationals `<= 1`, closed by
    `norm_num`.  This covers the bulk of the finite core; interval arithmetic (`omega_enclosure`) is only
    needed for the minority of configs with a chain-region child. -/
theorem gVal_eq (n : ℕ) :
    11 * gVal n = Real.log ((3 / 2) ^ (11 * n) * (4 * (n : ℝ) + 3) ^ 11
      / ((621 / 64) ^ (1 + 2 * n) * (3 * ((n : ℝ) + 1)) ^ 11)) := by
  have hR : Real.log ((3 / 2 : ℝ) ^ (11 * n) * (4 * (n : ℝ) + 3) ^ 11
      / ((621 / 64) ^ (1 + 2 * n) * (3 * ((n : ℝ) + 1)) ^ 11))
      = (11 * n : ℕ) * Real.log (3 / 2) + 11 * Real.log (4 * (n : ℝ) + 3)
        - ((1 + 2 * n : ℕ) * Real.log (621 / 64) + 11 * Real.log (3 * ((n : ℝ) + 1))) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    ring
  rw [hR]; unfold gVal Lval; push_cast; ring

/-- `11 * omega = log((3/2)^11 / (621/64)^2)` -- the same clearing, for the sweep's target. -/
theorem omega_eq : 11 * omegaVal = Real.log ((3 / 2) ^ 11 / (621 / 64) ^ 2) := by
  have hR : Real.log ((3 / 2 : ℝ) ^ 11 / (621 / 64) ^ 2)
      = 11 * Real.log (3 / 2) - 2 * Real.log (621 / 64) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  rw [hR]; unfold omegaVal Lval; ring

/-! ## The monotone-tail engine: the linear-rate bound on the near-star amplitude.

The finite sweep enumerates only a small binding grid (`s ∈ [2,7]`, `j ∈ [2,4]`); the node bound over the
whole `(s,j)` tail beyond it is controlled NOT by monotonicity of the node bound `F` itself (`F` is not monotone
in `s` or `j`) but by an EXACT linear surrogate: `g(n) <= n*omega + lambda`, with the exact reason
`(4n+3)/(4n+4) <= 1` (so `g` never grows faster than the tail rate `omega < 0`).  From it the node HEAD
`g(s+j) - j*omega` is bounded by `s*omega + lambda`, which is INDEPENDENT of `j` (so larger `j` cannot escape
the bound) and strictly DECREASING in `s` (since `omega < 0`, so larger `s` decays).  These two facts are the
rigorous content of "the tail is dominated by monotone decay". -/

/-- **The linear-rate bound (the tail engine):** `g(n) <= n*omega + lambda` for every `n`.  All the `L`-terms
    cancel exactly (no 11th-root clearing needed); the residual is `log((4n+3)/(4n+4)) <= 0`. -/
theorem gVal_le_linear (n : ℕ) : gVal n ≤ (n : ℝ) * omegaVal + lambdaVal := by
  have step : gVal n - ((n : ℝ) * omegaVal + lambdaVal)
      = Real.log (4 * (n : ℝ) + 3) - Real.log (3 * ((n : ℝ) + 1)) - Real.log (4 / 3) := by
    unfold gVal omegaVal lambdaVal Lval; ring
  have e1 : Real.log (3 * ((n : ℝ) + 1)) + Real.log (4 / 3) = Real.log (4 * (n : ℝ) + 4) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
  have hcomb : Real.log (4 * (n : ℝ) + 3) - Real.log (3 * ((n : ℝ) + 1)) - Real.log (4 / 3)
      = Real.log ((4 * (n : ℝ) + 3) / (4 * (n : ℝ) + 4)) := by
    rw [Real.log_div (show (4 * (n : ℝ) + 3) ≠ 0 by positivity)
      (show (4 * (n : ℝ) + 4) ≠ 0 by positivity)]; linarith [e1]
  have hle : Real.log ((4 * (n : ℝ) + 3) / (4 * (n : ℝ) + 4)) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity)]; linarith
  linarith [step, hcomb, hle]

/-- **The node head is bounded independently of `j`, and decreasingly in `s`.**  `g(s+j) - j*omega <= s*omega +
    lambda`.  This single bound covers BOTH tails of the sweep: the RHS does not depend on `j` (the `j`-tail),
    and (with `omegaVal_neg`) it strictly decreases in `s` (the `s`-tail). -/
theorem node_head_le (s j : ℕ) :
    gVal (s + j) - (j : ℝ) * omegaVal ≤ (s : ℝ) * omegaVal + lambdaVal := by
  have h := gVal_le_linear (s + j)
  have hcast : ((s + j : ℕ) : ℝ) = (s : ℝ) + (j : ℝ) := by push_cast; ring
  have hdist : ((s : ℝ) + (j : ℝ)) * omegaVal = (s : ℝ) * omegaVal + (j : ℝ) * omegaVal := by ring
  rw [hcast] at h
  linarith [h, hdist]

/-! ## Automating the recipe: a general reduction lemma for the near-star-child node bounds.

Define the exact rationals `Rval n` (`= exp(11 g(n))`), `Romval` (`= exp(11 omega)`), and the coupling
`cpl s j sp`.  Then `node_ns_le` proves, ONCE and for ALL `(s, j, sp)`, that the Jensen-reduced node bound
`Q(s,j,sp) <= omega` reduces to the exact rational inequality `Rval(s+j) * Rval(sp)^j * cpl^11 <= Romval^(j+1)`
-- so every grid node is a one-liner `node_ns_le s j sp (by norm_num)`, no interval arithmetic. -/

/-- `Rval n = exp(11 g(n))`, the exact rational clearing the 11th root of the near-star amplitude. -/
noncomputable def Rval (n : ℕ) : ℝ :=
  (3 / 2) ^ (11 * n) * (4 * (n : ℝ) + 3) ^ 11 / ((621 / 64) ^ (1 + 2 * n) * (3 * ((n : ℝ) + 1)) ^ 11)

/-- `Romval = exp(11 omega)`. -/
noncomputable def Romval : ℝ := (3 / 2) ^ 11 / (621 / 64) ^ 2

/-- The all-equal coupling for a node with `s` arm-units and `j` children at cavity `3/(4sp+3)`. -/
noncomputable def cpl (s j sp : ℕ) : ℝ :=
  ((4 * (s : ℝ) + 3 * j + 3) * (4 * sp + 3) + 9 * j) / ((4 * ((s : ℝ) + j) + 3) * (4 * sp + 3))

theorem Rval_eq (n : ℕ) : 11 * gVal n = Real.log (Rval n) := gVal_eq n
theorem Rom_eq : 11 * omegaVal = Real.log Romval := omega_eq

/-- **The recipe, automated:** for every `(s, j, sp)`, the near-star-child node bound
    `Q = g(s+j) - j*omega + j*g(sp) + log(cpl)` satisfies `Q <= omega` provided the EXACT rational inequality
    `Rval(s+j) * Rval(sp)^j * cpl^11 <= Romval^(j+1)` holds.  Proof: multiply by 11, apply the engine
    `Rval_eq`/`Rom_eq`, combine logs, and `Real.log_le_log` reduces to the hypothesis.  Each grid node is then
    `node_ns_le s j sp (by norm_num)`. -/
theorem node_ns_le (s j sp : ℕ)
    (hrat : Rval (s + j) * (Rval sp) ^ j * (cpl s j sp) ^ 11 ≤ Romval ^ (j + 1)) :
    gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * gVal sp + Real.log (cpl s j sp) ≤ omegaVal := by
  have hRsj : 0 < Rval (s + j) := by unfold Rval; positivity
  have hRsp : 0 < Rval sp := by unfold Rval; positivity
  have hRom : 0 < Romval := by unfold Romval; positivity
  have hcpl : 0 < cpl s j sp := by unfold cpl; positivity
  have h11 : 11 * (gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * gVal sp + Real.log (cpl s j sp))
      ≤ 11 * omegaVal := by
    have expand : 11 * (gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * gVal sp + Real.log (cpl s j sp))
        = 11 * gVal (s + j) + (j : ℝ) * (11 * gVal sp) + 11 * Real.log (cpl s j sp)
          - (j : ℝ) * (11 * omegaVal) := by ring
    rw [expand, Rval_eq (s + j), Rval_eq sp, Rom_eq]
    have hLeft : Real.log (Rval (s + j)) + (j : ℝ) * Real.log (Rval sp) + 11 * Real.log (cpl s j sp)
        = Real.log (Rval (s + j) * (Rval sp) ^ j * (cpl s j sp) ^ 11) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast; ring
    have hRight : (j : ℝ) * Real.log Romval + Real.log Romval = Real.log (Romval ^ (j + 1)) := by
      rw [Real.log_pow]; push_cast; ring
    have hlog := Real.log_le_log
      (show (0 : ℝ) < Rval (s + j) * (Rval sp) ^ j * (cpl s j sp) ^ 11 by positivity) hrat
    rw [← hLeft, ← hRight] at hlog
    linarith [hlog]
  linarith

/-- **The first finite-core node bound, now a one-liner** via `node_ns_le` (`node (4,2,2)`; coupling
    `cpl 4 2 2 = 293/297`).  The `norm_num` closes the exact 56-digit rational inequality. -/
theorem node_4_2_2 :
    gVal 6 - (2 : ℝ) * omegaVal + (2 : ℝ) * gVal 2 + Real.log (cpl 4 2 2) ≤ omegaVal :=
  node_ns_le 4 2 2 (by unfold Rval Romval cpl; norm_num)

/-- A batch of grid nodes, each a one-liner -- demonstrating the recipe is automated across `(s, j, sp)`. -/
theorem node_0_2_1 :
    gVal 2 - (2 : ℝ) * omegaVal + (2 : ℝ) * gVal 1 + Real.log (cpl 0 2 1) ≤ omegaVal :=
  node_ns_le 0 2 1 (by unfold Rval Romval cpl; norm_num)

theorem node_0_3_2 :
    gVal 3 - (3 : ℝ) * omegaVal + (3 : ℝ) * gVal 2 + Real.log (cpl 0 3 2) ≤ omegaVal :=
  node_ns_le 0 3 2 (by unfold Rval Romval cpl; norm_num)

theorem node_2_4_3 :
    gVal 6 - (4 : ℝ) * omegaVal + (4 : ℝ) * gVal 3 + Real.log (cpl 2 4 3) ≤ omegaVal :=
  node_ns_le 2 4 3 (by unfold Rval Romval cpl; norm_num)

/-- **Enumerating the grid following the concave-hull structure.**  By concavity of the node bound in the mean
    child cavity, the worst near-star child for each `(s,j)` sits at a hull vertex (a specific near-star level
    `sp`), and the binding region is the small box `s ∈ [2,7], j ∈ [2,4], sp ∈ {3,4}` (worst margin `+0.018`).
    Every such node is discharged uniformly by `node_ns_le _ _ _ (by norm_num)` -- the whole near-star-child
    binding region of the finite sweep, machine-checked in one `fin_cases`.  (Nodes with larger `s,j` are
    dominated by monotone decay; the tail `s_tail` (D1) and the chain-child minority (`omega_enclosure` + log
    Taylor) complete the sweep.) -/
theorem grid_nodes (s j sp : ℕ)
    (h : (s, j, sp) ∈ [(5, 2, 4), (6, 2, 4), (7, 2, 4), (4, 2, 4), (3, 2, 3), (5, 3, 4), (6, 3, 4),
      (7, 3, 4), (4, 3, 4), (3, 3, 4), (2, 2, 3), (5, 4, 4), (6, 4, 4), (7, 4, 4), (4, 4, 4),
      (3, 4, 4)]) :
    gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * gVal sp + Real.log (cpl s j sp) ≤ omegaVal := by
  fin_cases h <;> exact node_ns_le _ _ _ (by unfold Rval Romval cpl; norm_num)

/-! ## The chain-child (interval) node bounds.

For a child on the E2 chain-region bound (cavity in `(2/5,1/2)`, amplitude a TRANSCENDENTAL value near the
`sqrt(2)-1` fixed point), the amplitude does not clear to an exact rational -- it must be ENCLOSED.  The interval
analog of `node_ns_le`: bound each transcendental piece of `Q` above by a rational (`g(n) <= 0` clears exactly
via `Rval n <= 1`; `omega >= L` from `omega_enclosure`; `log(coupling) <= coupling - 1` via
`Real.log_le_sub_one_of_pos`; the chain child amplitude `<= hub`), then a rational check closes `Q <= omega`. -/

/-- **The interval node reduction:** given rational bounds on `g(s+j)` (above), `omega` (below), the child
    amplitude, and `log(coupling)`, the node bound `Q <= omega` follows from a rational inequality. -/
theorem node_interval_le (s j : ℕ) (Hm coupling gub cub L hub : ℝ) (hj : 0 ≤ (j : ℝ))
    (hg : gVal (s + j) ≤ gub) (homL : L ≤ omegaVal) (hHm : Hm ≤ hub)
    (hlogc : Real.log coupling ≤ cub)
    (hrat : gub - (j : ℝ) * L + (j : ℝ) * hub + cub ≤ L) :
    gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * Hm + Real.log coupling ≤ omegaVal := by
  have h1 : (j : ℝ) * Hm ≤ (j : ℝ) * hub := by nlinarith [hHm, hj]
  have h2 : -(j : ℝ) * omegaVal ≤ -(j : ℝ) * L := by nlinarith [homL, hj]
  linarith [hg, hlogc, h1, h2, hrat, homL]

/-- **s-tail crux (exact integer).**  The reduced form of D1 after clearing the 11th root and factoring
    `621 = 3^3 * 23`, `64 = 2^6`, `4 = 2^2`. -/
theorem s_tail_crux : (3 : ℕ) ^ 317 * 2 ^ 81 ≤ 23 ^ 129 := by decide

/-- **The s-tail bound (D1) in log form, machine-checked:** `317 log 3 + 81 log 2 <= 129 log 23`.  This is the
    exact analytic content of the tail `65*omega + lambda + log(3/2) <= omega` after unfolding
    `omega = log(3/2)-2L`, `lambda = log(4/3)-L`, `L = log(621/64)/11`, clearing the 11th root, and collecting
    `log 2, log 3, log 23` (using `621 = 3^3*23`, `64 = 2^6`, `4 = 2^2`).  It follows from the integer crux by
    monotonicity of `Real.log`. -/
theorem s_tail_log : 317 * Real.log 3 + 81 * Real.log 2 ≤ 129 * Real.log 23 := by
  have h : (3 : ℝ) ^ 317 * 2 ^ 81 ≤ 23 ^ 129 := by exact_mod_cast s_tail_crux
  have e : 317 * Real.log 3 + 81 * Real.log 2 = Real.log ((3 : ℝ) ^ 317 * 2 ^ 81) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have e2 : (129 : ℝ) * Real.log 23 = Real.log ((23 : ℝ) ^ 129) := by
    rw [Real.log_pow]; push_cast; ring
  rw [e, e2]
  exact Real.log_le_log (by positivity) h

/-! ## Interval-arithmetic infrastructure for the finite core (found in Mathlib).

Every transcendental in the sweep is `log` of a RATIONAL.  Mathlib's `Real.abs_log_sub_add_sum_range_le`
(log Taylor series with an explicit remainder) together with the proven enclosures `Real.log_two_near_10`,
`Real.log_three_near_10` yield rigorous RATIONAL enclosures of any `log(rational)`.  So the finite core of the
sweep -- which I earlier called blocked on "interval arithmetic over log not in Mathlib" -- is in fact
UNBLOCKED: it is laborious (bound each log term per node) but needs no new infrastructure.  Below are the
reusable enclosures for the sweep's base constants, machine-checked, as a working demonstration. -/

/-- Rigorous rational enclosure of `log(3/2)` (a sweep constant), from `log 3 - log 2`. -/
theorem log_three_half_enclosure : (405 : ℝ) / 1000 < Real.log (3 / 2) ∧ Real.log (3 / 2) < 406 / 1000 := by
  have h2 := Real.log_two_near_10
  have h3 := Real.log_three_near_10
  rw [abs_sub_le_iff] at h2 h3
  rw [Real.log_div (by norm_num) (by norm_num)]
  exact ⟨by nlinarith [h2.1, h2.2, h3.1, h3.2], by nlinarith [h2.1, h2.2, h3.1, h3.2]⟩

/-- Rigorous rational enclosure of `log(4/3)` (a sweep constant), from `2 log 2 - log 3`. -/
theorem log_four_third_enclosure : (287 : ℝ) / 1000 < Real.log (4 / 3) ∧ Real.log (4 / 3) < 288 / 1000 := by
  have h2 := Real.log_two_near_10
  have h3 := Real.log_three_near_10
  rw [abs_sub_le_iff] at h2 h3
  have e : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e]
  exact ⟨by nlinarith [h2.1, h2.2, h3.1, h3.2], by nlinarith [h2.1, h2.2, h3.1, h3.2]⟩

/-- **Rigorous rational enclosure of `omega`** -- the sweep's comparison target -- machine-checked.
    `omega = (3/11) log 3 - (5/11) log 2 - (2/11) log(1 - 1/24)` (since `621/64 = 3^4 (1-1/24) / 2^3`), and
    `log(1-1/24)` is enclosed by its degree-4 Taylor sum via `Real.abs_log_sub_add_sum_range_le`.  This is the
    sweep's key constant boxed into rationals: every node bound `Q(s,j,m) <= omega` is checked by enclosing
    `Q` above and `omega` below. -/
theorem omega_enclosure : (-78 : ℝ) / 10000 < omegaVal ∧ omegaVal < -77 / 10000 := by
  have h2 := Real.log_two_near_10
  have h3 := Real.log_three_near_10
  rw [abs_sub_le_iff] at h2 h3
  -- omega as a rational combination of log 2, log 3, log(1-1/24)
  have hom : omegaVal = 3 / 11 * Real.log 3 - 5 / 11 * Real.log 2 - 2 / 11 * Real.log (1 - 1 / 24) := by
    have h621 : Real.log (621 / 64) = 4 * Real.log 3 - 3 * Real.log 2 + Real.log (1 - 1 / 24) := by
      have e : (621 / 64 : ℝ) = 3 ^ 4 * (1 - 1 / 24) / 2 ^ 3 := by norm_num
      rw [e, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]
      push_cast; ring
    simp only [omegaVal, Lval]
    rw [Real.log_div (by norm_num) (by norm_num), h621]; ring
  -- log(1-1/24) enclosed by its degree-4 Taylor sum
  have htay := Real.abs_log_sub_add_sum_range_le (x := (1 / 24 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 / 24 : ℝ) ^ (i + 1) / (i + 1)) = 56481 / 1327104 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have herr : |(1 / 24 : ℝ)| ^ (4 + 1) / (1 - |1 / 24|) = 1 / 7630848 := by
    rw [show |(1 / 24 : ℝ)| = 1 / 24 by rw [abs_of_pos]; norm_num]; norm_num
  rw [hsum, herr, abs_le] at htay
  rw [hom]
  exact ⟨by nlinarith [h2.1, h2.2, h3.1, h3.2, htay.1, htay.2],
    by nlinarith [h2.1, h2.2, h3.1, h3.2, htay.1, htay.2]⟩

/-! ## The complete `s`-tail (D1), quantified over all `s >= 65`.

The `s`-tail closes because the node head is `<= s*omega + lambda` (`node_head_le`) and, adding the exact bounds
`log-coupling <= log(3/2)` and child amplitudes `<= 0`, the whole node is `<= s*omega + lambda + log(3/2)`.  A
single base inequality at `s = 65` -- `65*omega + lambda + log(3/2) <= omega`, the exact integer crux
`s_tail_log` boxed into the real constants -- then extends to EVERY `s >= 65` because `s*omega` is decreasing
(`omega < 0`).  So one exact check plus one monotonicity discharges the entire `s >= 65` tail. -/

/-- `omega < 0` (from the rigorous enclosure `omega < -77/10000`). -/
theorem omegaVal_neg : omegaVal < 0 := lt_trans omega_enclosure.2 (by norm_num)

/-- **The `s`-tail base case at `s = 65`:** `65*omega + lambda + log(3/2) <= omega`.  This is the exact integer
    crux `s_tail_log` (`317 log 3 + 81 log 2 <= 129 log 23`) re-expressed in the sweep's real constants: multiply
    by 11, expand `log(3/2), log(4/3), log(621/64)` over `{log 2, log 3, log 23}`, and it is exactly the crux. -/
theorem s_tail_base : (65 : ℝ) * omegaVal + lambdaVal + Real.log (3 / 2) ≤ omegaVal := by
  have l32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have l43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have l621 : Real.log (621 / 64) = 3 * Real.log 3 + Real.log 23 - 6 * Real.log 2 := by
    rw [show (621 / 64 : ℝ) = 3 ^ 3 * 23 / 2 ^ 6 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have key : 11 * ((65 : ℝ) * omegaVal + lambdaVal + Real.log (3 / 2) - omegaVal)
      = 317 * Real.log 3 + 81 * Real.log 2 - 129 * Real.log 23 := by
    unfold omegaVal lambdaVal Lval; rw [l32, l43, l621]; ring
  linarith [key, s_tail_log]

/-- **The complete `s`-tail (D1), for EVERY `s >= 65`:** `s*omega + lambda + log(3/2) <= omega`.  From the base
    case at `s = 65` plus `s*omega <= 65*omega` (monotone decay, `omega < 0`). -/
theorem s_tail_ge_65 (s : ℕ) (hs : 65 ≤ s) :
    (s : ℝ) * omegaVal + lambdaVal + Real.log (3 / 2) ≤ omegaVal := by
  have hsr : (65 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hmono : (s : ℝ) * omegaVal ≤ (65 : ℝ) * omegaVal := by nlinarith [omegaVal_neg, hsr]
  linarith [s_tail_base, hmono]

/-- **A chain-child node bound (interval), machine-checked:** for a node with `s=0` arm-units and `j=2`
    children at a chain-region cavity (coupling `81/77`), ANY child amplitude `<= -7/100` -- which covers every
    chain-region child (amplitude `<= -0.0726`) -- gives `Q <= omega`.  The transcendental pieces are enclosed:
    `g(2) <= 0` (exact, `Rval 2 <= 1`), `omega >= -78/10000` (`omega_enclosure`), `log(81/77) <= 6/100`
    (`log x <= x-1`); the rational check `0 - 2L + 2(-7/100) + 6/100 <= L` closes it. -/
theorem node_chain_0_2 (Hm : ℝ) (hHm : Hm ≤ -7 / 100) :
    gVal 2 - (2 : ℝ) * omegaVal + (2 : ℝ) * Hm + Real.log (81 / 77) ≤ omegaVal := by
  have hg2 : gVal 2 ≤ 0 := by
    have h := gVal_eq 2
    set R : ℝ := (3 / 2) ^ (11 * 2) * (4 * (2 : ℕ) + 3) ^ 11
      / ((621 / 64) ^ (1 + 2 * 2) * (3 * ((2 : ℕ) + 1)) ^ 11) with hRdef
    have hR : R ≤ 1 := by rw [hRdef]; norm_num
    have hpos : (0 : ℝ) < R := by rw [hRdef]; positivity
    have hlog : Real.log R ≤ 0 := Real.log_nonpos (le_of_lt hpos) hR
    linarith [h, hlog]
  have homL : (-78 : ℝ) / 10000 ≤ omegaVal := omega_enclosure.1.le
  have hc : Real.log (81 / 77) ≤ 6 / 100 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 81 / 77 by norm_num); linarith
  exact node_interval_le 0 2 Hm (81 / 77) 0 (6 / 100) (-78 / 10000) (-7 / 100)
    (by norm_num) hg2 homL hHm hc (by norm_num)

end R3Cert
