/-
  DEC -- the decomposition identity, formalized as a PURE REAL-LOG IDENTITY (no graph theory needed).

  The node amplitude has two expressions:
    * the RAW cavity form (from the amplitude recursion `_amp`), and
    * the (g, omega)-normalized DEC form used throughout the induction.
  DEC asserts they are equal.  Crucially this is an ALGEBRAIC identity in reals + `Real.log`: after using
  `Real.log (a/b) = Real.log a - Real.log b` and substituting `omega = log(3/2) - 2L`, everything cancels by
  `ring` (the `log t`, `log (3*(s+j+1))`, `log (4*(s+j)+3)` terms match as atoms and the rest is linear in
  `log(3/2)` and `L`).  It depends only on `omega = log(3/2) - 2L` and `s = c + k` -- NOT on the definition of
  `t`, on `M = Σ child cavities`, or on any matching/permanent theory.

  Scope: this proves DEC, the identity RELATING the two amplitude expressions.  The separate fact that the
  cavity recursion computes `per L(T) / ∏ deg` (the matching/permanent bridge) is not formalized here; DEC is
  the piece the Phi<=1 induction actually invokes, and it is now a theorem.

  Verified numerically to 2e-15 over 200k random reals (gap_reduction_frontier.verify_decomposition and the
  companion Python check).
-/
import Mathlib

namespace R3Cert

open Real

/-- The near-star amplitude `g(n) = n·log(3/2) − (1+2n)L + log(4n+3) − log(3(n+1))` (as a real function). -/
noncomputable def gAmp (L n : ℝ) : ℝ :=
  n * Real.log (3 / 2) - (1 + 2 * n) * L + Real.log (4 * n + 3) - Real.log (3 * (n + 1))

/-- **DEC** (decomposition identity), abstract form.

For a node with `c` cherries, `k` arm-children (each contributing amplitude `omega` and cavity `1/3`), and
`j` deep children with total amplitude `E` and total cavity mass folded into `t` (the node's `t`-value) and
`den = 4(s+j)+3` with `s = c+k`, the RAW amplitude equals the DEC form:

  raw  = c·log(3/2) − (1+2c)L + log t − log(3(s+j+1)) + k·omega + E
  DEC  = gAmp(s+j) − j·omega + E + log (t / den).

Holds for all reals with `t ≠ 0`, `den ≠ 0`, `den = 4(s+j)+3`, and `omega = log(3/2) − 2L`. -/
theorem dec_identity
    (c k j E L t den omega : ℝ)
    (ht : t ≠ 0) (hden : den ≠ 0)
    (hdendef : den = 4 * ((c + k) + j) + 3)
    (homega : omega = Real.log (3 / 2) - 2 * L) :
    c * Real.log (3 / 2) - (1 + 2 * c) * L + Real.log t
        - Real.log (3 * ((c + k) + j + 1)) + k * omega + E
      =
    gAmp L ((c + k) + j) - j * omega + E + Real.log (t / den) := by
  unfold gAmp
  rw [Real.log_div ht hden, hdendef, homega]
  ring

/-- ARM is the equality case: an arm-child has amplitude `omega` and cavity `1/3`.  A near-star node (`j = 0`,
no deep children, `E = 0`) reduces DEC to `raw = gAmp(s) + log (t / (4s+3))`, the near-star amplitude form. -/
theorem dec_near_star
    (c k L t den omega : ℝ)
    (ht : t ≠ 0) (hden : den ≠ 0)
    (hdendef : den = 4 * (c + k) + 3)
    (homega : omega = Real.log (3 / 2) - 2 * L) :
    c * Real.log (3 / 2) - (1 + 2 * c) * L + Real.log t
        - Real.log (3 * ((c + k) + 1)) + k * omega
      =
    gAmp L (c + k) + Real.log (t / den) := by
  have h := dec_identity c k 0 0 L t den omega ht hden (by rw [hdendef]; ring) homega
  simpa using h

end R3Cert
