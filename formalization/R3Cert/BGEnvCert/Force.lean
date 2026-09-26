/-
  R3Cert.BGEnvCert.Force -- evaluation-forcing variant of the cap loop (2026-09-26).

  The Lean kernel does not share the evaluation of repeated argument subterms, so `capLoop`, whose
  state `t` is reused by `levelOK` and by the next `lvS`, re-evaluates the whole chain of earlier
  levels.  `forceN n f` matches on the natural number `n`, which makes the kernel reduce `n` to a
  literal once and hand that literal to `f`; semantically `forceN n f = f n` (`forceN_eq`).
  `capLoopF` threads the forced state; `capLoopF_eq` shows it equals `capLoop`, and `capCheckF_eq`
  lifts this to `capCheck`.  No `sorry`; standard axioms only.
-/
import Mathlib
import R3Cert.BGEnvCert.Check
import R3Cert.BGEnvCert.Assemble

namespace R3Cert
namespace EnvCert

/-- Force the evaluation of `n` before passing it on. -/
def forceN (n : ℕ) (f : ℕ → Bool) : Bool :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem forceN_eq (n : ℕ) (f : ℕ → Bool) : forceN n f = f n := by
  cases n <;> rfl

/-- Force all three components of a state. -/
def force3 (t : ℕ × ℕ × ℕ) (f : ℕ × ℕ × ℕ → Bool) : Bool :=
  forceN t.1 fun a => forceN t.2.1 fun b => forceN t.2.2 fun r => f (a, b, r)

theorem force3_eq (t : ℕ × ℕ × ℕ) (f : ℕ × ℕ × ℕ → Bool) : force3 t f = f t := by
  simp only [force3, forceN_eq]

/-- `capLoop` with the state forced at every level. -/
def capLoopF (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) : ℕ → ℕ → ℕ × ℕ × ℕ → Bool
  | 0, _, _ => true
  | j + 1, c, t => levelOK tt ld ph d c t && force3 (lvS d t) (fun t' => capLoopF tt ld ph d j (c + 1) t')

theorem capLoopF_eq (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) :
    ∀ j c t, capLoopF tt ld ph d j c t = capLoop tt ld ph d j c t
  | 0, _, _ => rfl
  | j + 1, c, t => by
    simp only [capLoopF, capLoop, force3_eq, capLoopF_eq tt ld ph d j (c + 1)]

/-- `capCheck` with the forced loop and a forced initial state. -/
def capCheckF (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) : Bool :=
  decide (3 ≤ d.R) && decide (1 ≤ d.C) && decide (d.kmax ≤ d.C + 1) && decide (d.C + 1 ≤ 120) &&
    dataOK (HG * d.R) d.Wa (2 * OFF) && dataOK (HG * d.R) d.Wn (2 * OFF) && leafOK d &&
    d.roots.all trootOK && d.roots.all (fun e => decide (e.2.1 ≤ d.kmax)) &&
    force3 (lv0 d) (fun t => capLoopF tt ld ph d (max d.C d.kmax) 1 t)

theorem capCheckF_eq (tt : TanTab) (ld : LdTab) (ph : PhiTab) (d : CapData) :
    capCheckF tt ld ph d = capCheck tt ld ph d := by
  simp only [capCheckF, capCheck, force3_eq, capLoopF_eq]

end EnvCert
end R3Cert

namespace R3Cert
namespace EnvCert

theorem tanOK_split (tt : TanTab) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : tanOK tt a b = true) (h2 : tanOK tt b c = true) : tanOK tt a c = true := by
  unfold tanOK at *
  have : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    have h := List.range'_append (s := a) (m := b - a) (n := c - b) (step := 1)
    rw [show a + 1 * (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
    exact h.symm
  rw [this, List.all_append, h1, h2]; rfl

theorem spidersOK_split (ph : PhiTab) (sp : List (List ℕ)) (sm : List ℤ) (a b c : ℕ)
    (hab : a ≤ b + 1) (hbc : b ≤ c)
    (h1 : spidersOK ph sp sm a b = true) (h2 : spidersOK ph sp sm (b + 1) c = true) :
    spidersOK ph sp sm a c = true := by
  unfold spidersOK at *
  have : List.range' a (c + 1 - a) = List.range' a (b + 1 - a) ++ List.range' (b + 1) (c + 1 - (b + 1)) := by
    have h := List.range'_append (s := a) (m := b + 1 - a) (n := c + 1 - (b + 1)) (step := 1)
    rw [show a + 1 * (b + 1 - a) = b + 1 by omega,
      show b + 1 - a + (c + 1 - (b + 1)) = c + 1 - a by omega] at h
    exact h.symm
  rw [this, List.all_append, h1, h2]; rfl

end EnvCert
end R3Cert
