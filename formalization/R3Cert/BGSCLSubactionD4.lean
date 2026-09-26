/-
  The degree-4 hub `IsSubaction ρwit` enclosure atoms (2026-09-03).

  A degree-4 hub has 3 children; `ρwit(node) = bY(node)/384`.  Every one of the 35 child-degree profiles
  (multisets from {leaf, 2, 3, 4, ≥5}) closes with a SINGLE `log_tangent` at its binding corner, reducing to a
  single-log enclosure `log A + kL·log(3/2) − kF·F* ≤ B` — ALL on the **tangent route** (`log x ≤ x−1`), the
  cheapest.  See `proof/docs/BG_SUBACTION_D4_TAIL_TIE_SPEC.md` for the derivation and the recipe.

  This file DOGFOODS the whole 35-atom table against the kernel via one reusable lemma `tangent_atom`
  (the tangent-route enclosure generator, `zpow` so one lemma covers every `log(3/2)`-fold sign), then 35
  one-line applications.  Names `d4_<profile>` with `L` = leaf.  Kernel-checked, no `sorry`.
  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

open Real

/-- **The tangent-route enclosure generator.**  For any `A > 0` and integer fold exponents `kL, kF`, if the
    folded rational `X = A¹¹·(3/2)^(11kL)·(621/64)^(−kF)` satisfies `X − 1 ≤ 11·B` (a `norm_num` fact), then
    `log A + kL·log(3/2) − kF·F* ≤ B`.  This is the `emit_log_combination` tangent route, dogfooded once;
    every d=4 atom below is a one-line application. -/
theorem tangent_atom (A : ℝ) (kL kF : ℤ) (B : ℝ) (hA : 0 < A)
    (hfold : A ^ (11:ℤ) * (3/2 : ℝ) ^ (11 * kL) * (621/64 : ℝ) ^ (-kF) - 1 ≤ 11 * B) :
    Real.log A + (kL : ℝ) * Real.log (3/2) - (kF : ℝ) * FSTAR ≤ B := by
  rw [FSTAR]
  have hpos : (0:ℝ) < A ^ (11:ℤ) * (3/2 : ℝ) ^ (11 * kL) * (621/64 : ℝ) ^ (-kF) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log (A ^ (11:ℤ) * (3/2 : ℝ) ^ (11 * kL) * (621/64 : ℝ) ^ (-kF))
      = 11 * Real.log A + (11 * (kL:ℝ)) * Real.log (3/2) - (kF:ℝ) * Real.log (621/64) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_zpow, Real.log_zpow, Real.log_zpow]
    push_cast; ring
  rw [hsplit] at hr
  linarith

/-! ### The 35 degree-4 enclosure atoms (all tangent route). -/

theorem d4_LLL : Real.log (7/4 : ℝ) + (0 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (-1/2688 : ℝ) :=
  tangent_atom (7/4 : ℝ) (0) (4) (-1/2688 : ℝ) (by norm_num) (by norm_num)
theorem d4_2LL : Real.log (19/12 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (-1/2432 : ℝ) :=
  tangent_atom (19/12 : ℝ) (-1) (5) (-1/2432 : ℝ) (by norm_num) (by norm_num)
theorem d4_22L : Real.log (17/12 : ℝ) + (-2 : ℤ) * Real.log (3/2) - (6 : ℤ) * FSTAR ≤ (-1/2176 : ℝ) :=
  tangent_atom (17/12 : ℝ) (-2) (6) (-1/2176 : ℝ) (by norm_num) (by norm_num)
theorem d4_222 : Real.log (5/4 : ℝ) + (-3 : ℤ) * Real.log (3/2) - (7 : ℤ) * FSTAR ≤ (-1/1920 : ℝ) :=
  tangent_atom (5/4 : ℝ) (-3) (7) (-1/1920 : ℝ) (by norm_num) (by norm_num)
theorem d4_223 : Real.log (5/4 : ℝ) + (-2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (53/5376 : ℝ) :=
  tangent_atom (5/4 : ℝ) (-2) (5) (53/5376 : ℝ) (by norm_num) (by norm_num)
theorem d4_224 : Real.log (59/48 : ℝ) + (-2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (1/10752 : ℝ) :=
  tangent_atom (59/48 : ℝ) (-2) (5) (1/10752 : ℝ) (by norm_num) (by norm_num)
theorem d4_225 : Real.log (73/60 : ℝ) + (-2 : ℤ) * Real.log (3/2) - (5 : ℤ) * FSTAR ≤ (-1/1792 : ℝ) :=
  tangent_atom (73/60 : ℝ) (-2) (5) (-1/1792 : ℝ) (by norm_num) (by norm_num)
theorem d4_23L : Real.log (17/12 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (61/6144 : ℝ) :=
  tangent_atom (17/12 : ℝ) (-1) (4) (61/6144 : ℝ) (by norm_num) (by norm_num)
theorem d4_233 : Real.log (5/4 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (101/4992 : ℝ) :=
  tangent_atom (5/4 : ℝ) (-1) (3) (101/4992 : ℝ) (by norm_num) (by norm_num)
theorem d4_234 : Real.log (59/48 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (209/19968 : ℝ) :=
  tangent_atom (59/48 : ℝ) (-1) (3) (209/19968 : ℝ) (by norm_num) (by norm_num)
theorem d4_235 : Real.log (73/60 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (49/4992 : ℝ) :=
  tangent_atom (73/60 : ℝ) (-1) (3) (49/4992 : ℝ) (by norm_num) (by norm_num)
theorem d4_24L : Real.log (67/48 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (1/6144 : ℝ) :=
  tangent_atom (67/48 : ℝ) (-1) (4) (1/6144 : ℝ) (by norm_num) (by norm_num)
theorem d4_244 : Real.log (29/24 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (7/9984 : ℝ) :=
  tangent_atom (29/24 : ℝ) (-1) (3) (7/9984 : ℝ) (by norm_num) (by norm_num)
theorem d4_245 : Real.log (287/240 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (1/19968 : ℝ) :=
  tangent_atom (287/240 : ℝ) (-1) (3) (1/19968 : ℝ) (by norm_num) (by norm_num)
theorem d4_25L : Real.log (83/60 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (4 : ℤ) * FSTAR ≤ (-1/2048 : ℝ) :=
  tangent_atom (83/60 : ℝ) (-1) (4) (-1/2048 : ℝ) (by norm_num) (by norm_num)
theorem d4_255 : Real.log (71/60 : ℝ) + (-1 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (-1/1664 : ℝ) :=
  tangent_atom (71/60 : ℝ) (-1) (3) (-1/1664 : ℝ) (by norm_num) (by norm_num)
theorem d4_3LL : Real.log (19/12 : ℝ) + (0 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (23/2304 : ℝ) :=
  tangent_atom (19/12 : ℝ) (0) (3) (23/2304 : ℝ) (by norm_num) (by norm_num)
theorem d4_33L : Real.log (17/12 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (13/640 : ℝ) :=
  tangent_atom (17/12 : ℝ) (0) (2) (13/640 : ℝ) (by norm_num) (by norm_num)
theorem d4_333 : Real.log (5/4 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (47/1536 : ℝ) :=
  tangent_atom (5/4 : ℝ) (0) (1) (47/1536 : ℝ) (by norm_num) (by norm_num)
theorem d4_334 : Real.log (59/48 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (1/48 : ℝ) :=
  tangent_atom (59/48 : ℝ) (0) (1) (1/48 : ℝ) (by norm_num) (by norm_num)
theorem d4_335 : Real.log (73/60 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (31/1536 : ℝ) :=
  tangent_atom (73/60 : ℝ) (0) (1) (31/1536 : ℝ) (by norm_num) (by norm_num)
theorem d4_34L : Real.log (67/48 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (27/2560 : ℝ) :=
  tangent_atom (67/48 : ℝ) (0) (2) (27/2560 : ℝ) (by norm_num) (by norm_num)
theorem d4_344 : Real.log (29/24 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (17/1536 : ℝ) :=
  tangent_atom (29/24 : ℝ) (0) (1) (17/1536 : ℝ) (by norm_num) (by norm_num)
theorem d4_345 : Real.log (287/240 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (1/96 : ℝ) :=
  tangent_atom (287/240 : ℝ) (0) (1) (1/96 : ℝ) (by norm_num) (by norm_num)
theorem d4_35L : Real.log (83/60 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (19/1920 : ℝ) :=
  tangent_atom (83/60 : ℝ) (0) (2) (19/1920 : ℝ) (by norm_num) (by norm_num)
theorem d4_355 : Real.log (71/60 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (5/512 : ℝ) :=
  tangent_atom (71/60 : ℝ) (0) (1) (5/512 : ℝ) (by norm_num) (by norm_num)
theorem d4_4LL : Real.log (25/16 : ℝ) + (0 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (1/4608 : ℝ) :=
  tangent_atom (25/16 : ℝ) (0) (3) (1/4608 : ℝ) (by norm_num) (by norm_num)
theorem d4_44L : Real.log (11/8 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (1/1280 : ℝ) :=
  tangent_atom (11/8 : ℝ) (0) (2) (1/1280 : ℝ) (by norm_num) (by norm_num)
theorem d4_444 : Real.log (19/16 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (1/768 : ℝ) :=
  tangent_atom (19/16 : ℝ) (0) (1) (1/768 : ℝ) (by norm_num) (by norm_num)
theorem d4_445 : Real.log (47/40 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (1/1536 : ℝ) :=
  tangent_atom (47/40 : ℝ) (0) (1) (1/1536 : ℝ) (by norm_num) (by norm_num)
theorem d4_45L : Real.log (109/80 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (1/7680 : ℝ) :=
  tangent_atom (109/80 : ℝ) (0) (2) (1/7680 : ℝ) (by norm_num) (by norm_num)
theorem d4_455 : Real.log (93/80 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (0 : ℝ) :=
  tangent_atom (93/80 : ℝ) (0) (1) (0 : ℝ) (by norm_num) (by norm_num)
theorem d4_5LL : Real.log (31/20 : ℝ) + (0 : ℤ) * Real.log (3/2) - (3 : ℤ) * FSTAR ≤ (-1/2304 : ℝ) :=
  tangent_atom (31/20 : ℝ) (0) (3) (-1/2304 : ℝ) (by norm_num) (by norm_num)
theorem d4_55L : Real.log (27/20 : ℝ) + (0 : ℤ) * Real.log (3/2) - (2 : ℤ) * FSTAR ≤ (-1/1920 : ℝ) :=
  tangent_atom (27/20 : ℝ) (0) (2) (-1/1920 : ℝ) (by norm_num) (by norm_num)
theorem d4_555 : Real.log (23/20 : ℝ) + (0 : ℤ) * Real.log (3/2) - (1 : ℤ) * FSTAR ≤ (-1/1536 : ℝ) :=
  tangent_atom (23/20 : ℝ) (0) (1) (-1/1536 : ℝ) (by norm_num) (by norm_num)

end BGSCL
end R3Cert
