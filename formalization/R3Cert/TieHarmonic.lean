/-
  The tie-harmonic amplitude `f(c) <= 0` at integer `c` -- the ARITHMETIC statement the near-tie asymptotics
  pin (`near_tie_asymptotics.py`).

  The tie-harmonic family `G(c) = (c, [ARM])` (root: `c` cherries + one cherry-arm child), root cavity field
  `m(c) = 3/(4c+7)`, has the exact log-amplitude
      f(c) = -(2c+3) log rho_B + (c+1) log(3/2) + log(4c+7) - log(3(c+2)),
  and it is the value-function ENVELOPE at every near-tie harmonic (verified numerically).  The whole crux, at
  the tie, reduces to `f(c) <= 0` for INTEGER `c`, with equality at `c = 4` (`m = 3/23`) -- while the CONTINUOUS
  relaxation has its max at `c* = 3.8217` with `Phi(c*) = 1.000042 > 1`, so this is an ARITHMETIC (integrality)
  fact, not a smooth one.

  KEY IDENTITY: `f(c) = gVal (c+1)` (the near-star amplitude at `n = c+1`).  Indeed `gVal n = n log(3/2) -
  (1+2n) L + log(4n+3) - log(3(n+1))` (Sweep.lean) at `n = c+1` is exactly `f(c)`.  Hence `f(c) <= 0` is the
  already-proven `gVal_nonpos (c+1)` (JTail.lean: `Rval n <= 1` for `n < 11` by `norm_num`, the linear tail for
  `n >= 11`), and the tie `f(4) = 0` is `gVal 5 = 0` (i.e. `Rval 5 = 1`, the exact integer tie identity).

  NOTE (honest scope): this closes the TIE-HARMONIC / near-star family -- the marginal near-tie envelope -- NOT
  the full `Phi <= 1`, which additionally needs the general-children tree-induction over the (non-finite,
  accumulating) potential (`Reach.phi_le_one_of_potential` conditional on `exists P, ValidPotential P`), the
  open crux.
-/
import Mathlib
import R3Cert.JTail

namespace R3Cert

open Real

/-- The tie-harmonic amplitude `f(c) = log Phi(G(c))`, `G(c) = (c, [ARM])`, root cavity `m(c) = 3/(4c+7)`. -/
noncomputable def fHarm (c : ℕ) : ℝ :=
  -(2 * (c : ℝ) + 3) * Lval + ((c : ℝ) + 1) * Real.log (3 / 2)
    + Real.log (4 * (c : ℝ) + 7) - Real.log (3 * ((c : ℝ) + 2))

/-- **`f(c) = gVal (c+1)`** -- the tie-harmonic amplitude is the near-star amplitude at `n = c+1`. -/
theorem fHarm_eq_gVal (c : ℕ) : fHarm c = gVal (c + 1) := by
  unfold fHarm gVal
  push_cast
  rw [show (4 : ℝ) * ((c : ℝ) + 1) + 3 = 4 * (c : ℝ) + 7 from by ring,
    show (3 : ℝ) * (((c : ℝ) + 1) + 1) = 3 * ((c : ℝ) + 2) from by ring]
  ring

/-- **`f(c) <= 0` at every integer `c`** -- the arithmetic tie-harmonic bound, from the proven `gVal_nonpos`. -/
theorem fHarm_nonpos (c : ℕ) : fHarm c ≤ 0 := by
  rw [fHarm_eq_gVal]; exact gVal_nonpos (c + 1)

/-- **`gVal 5 = 0`** -- the tie: `Rval 5 = 1` exactly (the integer tie identity), so `11 * gVal 5 = log 1 = 0`. -/
theorem gVal_five_zero : gVal 5 = 0 := by
  have hR : Rval 5 = 1 := by unfold Rval; norm_num
  have h := Rval_eq 5
  rw [hR, Real.log_one] at h
  linarith

/-- **`f(4) = 0`** -- the tie `m = 3/23` (`c = 4`), where the harmonic amplitude vanishes exactly. -/
theorem fHarm_tie : fHarm 4 = 0 := by
  rw [fHarm_eq_gVal]; exact gVal_five_zero

/-- **The tie-harmonic bound, packaged: `f(c) <= 0` for all `c`, with equality at the tie `c = 4`.** -/
theorem tie_harmonic_le_zero (c : ℕ) : fHarm c ≤ 0 ∧ fHarm 4 = 0 :=
  ⟨fHarm_nonpos c, fHarm_tie⟩

end R3Cert
