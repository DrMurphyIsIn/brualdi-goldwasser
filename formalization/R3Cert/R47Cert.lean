/-
  R4-R7 campaign, PHASE 4a: the topped-up merge certificates -- infrastructure + the
  first proven cell.

  P2b's `Aobj_mono_chain` consumes per-step monotonicity as a named hypothesis; its
  discharge is the 36-cell certificate table of `kelmans_unified_merge.py`
  (`certify_unified_table`, cap 3/16): the merge comparison
      D = after - before,
      before = F(da,cA) F(db,cb) ((1 + za sQ)(1 + zb (k z15 + sr)) + za zb),
      after  = Wt^k F(da+db-1,cA) F(1,5) (1 + za'' (sQ + k z14 + sr + z15)),
  is >= 0 over the environment box sQ in [0,(da-1)cap], sr-box, for every load cell.
  D is BILINEAR in (sQ, sr), so the box reduces to 4 corners; each corner is a rational
  function of the degree shifts (u, v) with an all-nonnegative-coefficient numerator
  over a positive denominator (the Polya certificates, verified exactly in sympy).

  This file machine-checks:
  * `Fw`/`zw`         -- the loaded-hub factor F(d,c) and activity z(d,c) (formulas
                         cross-checked exactly against the Python F_of/z_of);
  * `bilinear_corner_nonneg` -- the box-to-corner reduction for bilinear forms;
  * the DIRECT cell (cA = 0, cb = 5): all four Polya corner certificates
    (numerators exported from the sympy certification, equality by field_simp+ring,
    nonnegativity by positivity) + the assembled box theorem `directA0_cell`.

  HONEST SCOPE: 1 of 36 cells; the other 35 are the same pipeline (P4b+, generated).
  The seam from D >= 0 to actual `Aobj` monotonicity of a `Step` (the environment
  factorization pi(T'') - pi(T) = Penv * FQ * FSr * D) is a LATER phase -- nothing
  here asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

/-! ### The loaded-hub factors -/

/-- `F(d, c)`: the loaded-hub factor (matches Python `F_of`; `c = 0` gives 1). -/
noncomputable def Fw (d : ℝ) (c : ℕ) : ℝ :=
  (3 / 2) ^ c + (c : ℝ) / (2 * (d + c)) * (3 / 2) ^ (c - 1)

/-- `z(d, c) = 3/(3d + 4c)`: the loaded activity (matches Python `z_of`). -/
noncomputable def zw (d : ℝ) (c : ℕ) : ℝ := 3 / (3 * d + 4 * c)

theorem Fw_zero (d : ℝ) : Fw d 0 = 1 := by simp [Fw]

theorem Fw_five (d : ℝ) : Fw d 5 = (3 / 2) ^ 5 + 5 / (2 * (d + 5)) * (3 / 2) ^ 4 := by
  norm_num [Fw]

theorem Fw_one_five : Fw 1 5 = 621 / 64 := by norm_num [Fw]

theorem zw_one_five : zw 1 5 = 3 / 23 := by norm_num [zw]

/-! ### The merge comparison D -/

/-- The pre-merge side of the unified-merge comparison (donor load `cb`, `k = 5 - cb`
    borrows; environment enters only via `sQ`, `sr`). -/
noncomputable def beforeD (da db : ℝ) (cA cb k : ℕ) (sQ sr : ℝ) : ℝ :=
  Fw da cA * Fw db cb
    * ((1 + zw da cA * sQ) * (1 + zw db cb * ((k : ℝ) * (3 / 23) + sr))
        + zw da cA * zw db cb)

/-- The post-merge side: the donor lands as a canonical load-5 arm, `k` load-4 residue
    arms (`Wt = F(1,4)/F(1,5) = 76/115`, `F(1,5) = 621/64`). -/
noncomputable def afterD (da db : ℝ) (cA k : ℕ) (sQ sr : ℝ) : ℝ :=
  (76 / 115) ^ k * Fw (da + db - 1) cA * (621 / 64)
    * (1 + zw (da + db - 1) cA * (sQ + (k : ℝ) * (3 / 19) + sr + 3 / 23))

/-! ### The box-to-corner reduction (D is bilinear in the environment scalars) -/

/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it. -/
theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : 0 ≤ A + B * s0 + C * t0 + E * (s0 * t0))
    (h01 : 0 ≤ A + B * s0 + C * t1 + E * (s0 * t1))
    (h10 : 0 ≤ A + B * s1 + C * t0 + E * (s1 * t0))
    (h11 : 0 ≤ A + B * s1 + C * t1 + E * (s1 * t1)) :
    0 ≤ A + B * s + C * t + E * (s * t) := by
  have hfix : ∀ sv : ℝ, 0 ≤ A + B * sv + C * t0 + E * (sv * t0) →
      0 ≤ A + B * sv + C * t1 + E * (sv * t1) →
      0 ≤ A + B * sv + C * t + E * (sv * t) := by
    intro sv e0 e1
    rcases le_total 0 (C + E * sv) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr ht1)]
  have H0 := hfix s0 h00 h01
  have H1 := hfix s1 h10 h11
  rcases le_total 0 (B + E * t) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hs0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hs1)]

/-! ### The direct cell cA = 0 (cb = 5, k = 0): bilinear coefficients -/

/-- Constant coefficient of `afterD - beforeD` for the direct cA = 0 cell
    (`da = 2+v+u`, `db = 2+v`; `da + db - 1 = u + 2v + 3`). -/
noncomputable def dA0c1 (u v : ℝ) : ℝ :=
  Fw 1 5 * (1 + zw (u + 2 * v + 3) 0 * zw 1 5)
    - Fw (2 + v) 5 * (1 + zw (2 + v + u) 0 * zw (2 + v) 5)

/-- `sQ` coefficient. -/
noncomputable def dA0c2 (u v : ℝ) : ℝ :=
  Fw 1 5 * zw (u + 2 * v + 3) 0 - Fw (2 + v) 5 * zw (2 + v + u) 0

/-- `sS` coefficient. -/
noncomputable def dA0c3 (u v : ℝ) : ℝ :=
  Fw 1 5 * zw (u + 2 * v + 3) 0 - Fw (2 + v) 5 * zw (2 + v) 5

/-- `sQ * sS` coefficient. -/
noncomputable def dA0c4 (u v : ℝ) : ℝ :=
  -(Fw (2 + v) 5 * (zw (2 + v + u) 0 * zw (2 + v) 5))

/-- The bilinear decomposition of the direct cA = 0 cell (cross-checked exactly against
    `D_unified` on 50 random rational points including non-integer degrees). -/
theorem dA0_bilinear (u v sQ sS : ℝ) :
    afterD (2 + v + u) (2 + v) 0 0 sQ sS - beforeD (2 + v + u) (2 + v) 0 5 0 sQ sS
      = dA0c1 u v + dA0c2 u v * sQ + dA0c3 u v * sS + dA0c4 u v * (sQ * sS) := by
  simp only [afterD, beforeD, dA0c1, dA0c2, dA0c3, dA0c4, Fw_zero, Fw_five, zw]
  push_cast
  ring

/-! ### The four Polya corner certificates (numerators from the sympy certification) -/

/-- Corner (sQ, sS) = (0, 3/23). -/
theorem dA0_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ dA0c1 u v + dA0c2 u v * 0 + dA0c3 u v * (3 / 23) + dA0c4 u v * (0 * (3 / 23)) := by
  have h7 : (v : ℝ) + 7 ≠ 0 := by positivity
  have h2 : (u : ℝ) + v + 2 ≠ 0 := by positivity
  have h3 : (u : ℝ) + 2 * v + 3 ≠ 0 := by positivity
  have h26 : 3 * (v : ℝ) + 26 ≠ 0 := by positivity
  have hd1 : (2 : ℝ) * (2 + v + 5) ≠ 0 := by positivity
  have hd2 : 3 * ((2 : ℝ) + v) + 4 * 5 ≠ 0 := by positivity
  have hd3 : 3 * ((2 : ℝ) + v + u) + 4 * 0 ≠ 0 := by positivity
  have hd4 : 3 * ((u : ℝ) + 2 * v + 3) + 4 * 0 ≠ 0 := by positivity
  have hkey : dA0c1 u v + dA0c2 u v * 0 + dA0c3 u v * (3 / 23) + dA0c4 u v * (0 * (3 / 23))
      = (3105 * u ^ 2 * v + 1647 * u ^ 2 + 9315 * u * v ^ 2 + 24192 * u * v + 23139 * u
          + 6210 * v ^ 3 + 28755 * v ^ 2 + 41337 * v + 28512)
        / (1472 * (v + 7) * (u + v + 2) * (u + 2 * v + 3)) := by
    simp only [dA0c1, dA0c2, dA0c3, dA0c4, Fw_five, Fw_one_five, zw_one_five, zw]
    field_simp
    ring
  rw [hkey]
  positivity

/-- Corner (sQ, sS) = (0, (v+1) * 3/16). -/
theorem dA0_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ dA0c1 u v + dA0c2 u v * 0 + dA0c3 u v * ((v + 1) * (3 / 16))
        + dA0c4 u v * (0 * ((v + 1) * (3 / 16))) := by
  have h7 : (v : ℝ) + 7 ≠ 0 := by positivity
  have h2 : (u : ℝ) + v + 2 ≠ 0 := by positivity
  have h3 : (u : ℝ) + 2 * v + 3 ≠ 0 := by positivity
  have h26 : 3 * (v : ℝ) + 26 ≠ 0 := by positivity
  have hd1 : (2 : ℝ) * (2 + v + 5) ≠ 0 := by positivity
  have hd2 : 3 * ((2 : ℝ) + v) + 4 * 5 ≠ 0 := by positivity
  have hd3 : 3 * ((2 : ℝ) + v + u) + 4 * 0 ≠ 0 := by positivity
  have hd4 : 3 * ((u : ℝ) + 2 * v + 3) + 4 * 0 ≠ 0 := by positivity
  have hkey : dA0c1 u v + dA0c2 u v * 0 + dA0c3 u v * ((v + 1) * (3 / 16))
        + dA0c4 u v * (0 * ((v + 1) * (3 / 16)))
      = (702 * u ^ 2 * v + 702 * u ^ 2 + 3969 * u * v ^ 2 + 21816 * u * v + 17847 * u
          + 3267 * v ^ 3 + 26244 * v ^ 2 + 48087 * v + 25110)
        / (1024 * (v + 7) * (u + v + 2) * (u + 2 * v + 3)) := by
    simp only [dA0c1, dA0c2, dA0c3, dA0c4, Fw_five, Fw_one_five, zw_one_five, zw]
    field_simp
    ring
  rw [hkey]
  positivity

/-- Corner (sQ, sS) = ((u+v+1) * 3/16, 3/23). -/
theorem dA0_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ dA0c1 u v + dA0c2 u v * ((u + v + 1) * (3 / 16)) + dA0c3 u v * (3 / 23)
        + dA0c4 u v * ((u + v + 1) * (3 / 16) * (3 / 23)) := by
  have h7 : (v : ℝ) + 7 ≠ 0 := by positivity
  have h2 : (u : ℝ) + v + 2 ≠ 0 := by positivity
  have h3 : (u : ℝ) + 2 * v + 3 ≠ 0 := by positivity
  have h26 : 3 * (v : ℝ) + 26 ≠ 0 := by positivity
  have hd1 : (2 : ℝ) * (2 + v + 5) ≠ 0 := by positivity
  have hd2 : 3 * ((2 : ℝ) + v) + 4 * 5 ≠ 0 := by positivity
  have hd3 : 3 * ((2 : ℝ) + v + u) + 4 * 0 ≠ 0 := by positivity
  have hd4 : 3 * ((u : ℝ) + 2 * v + 3) + 4 * 0 ≠ 0 := by positivity
  have hkey : dA0c1 u v + dA0c2 u v * ((u + v + 1) * (3 / 16)) + dA0c3 u v * (3 / 23)
        + dA0c4 u v * ((u + v + 1) * (3 / 16) * (3 / 23))
      = (176985 * u ^ 2 * v ^ 2 + 1627749 * u ^ 2 * v + 813618 * u ^ 2
          + 402408 * u * v ^ 3 + 3776625 * u * v ^ 2 + 2775573 * u * v + 2341170 * u
          + 225423 * v ^ 4 + 2346354 * v ^ 3 + 3617217 * v ^ 2 + 2367198 * v + 4447872)
        / (23552 * (v + 7) * (3 * v + 26) * (u + v + 2) * (u + 2 * v + 3)) := by
    simp only [dA0c1, dA0c2, dA0c3, dA0c4, Fw_five, Fw_one_five, zw_one_five, zw]
    field_simp
    ring
  rw [hkey]
  positivity

/-- Corner (sQ, sS) = ((u+v+1) * 3/16, (v+1) * 3/16). -/
theorem dA0_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ dA0c1 u v + dA0c2 u v * ((u + v + 1) * (3 / 16))
        + dA0c3 u v * ((v + 1) * (3 / 16))
        + dA0c4 u v * ((u + v + 1) * (3 / 16) * ((v + 1) * (3 / 16))) := by
  have h7 : (v : ℝ) + 7 ≠ 0 := by positivity
  have h2 : (u : ℝ) + v + 2 ≠ 0 := by positivity
  have h3 : (u : ℝ) + 2 * v + 3 ≠ 0 := by positivity
  have h26 : 3 * (v : ℝ) + 26 ≠ 0 := by positivity
  have hd1 : (2 : ℝ) * (2 + v + 5) ≠ 0 := by positivity
  have hd2 : 3 * ((2 : ℝ) + v) + 4 * 5 ≠ 0 := by positivity
  have hd3 : 3 * ((2 : ℝ) + v + u) + 4 * 0 ≠ 0 := by positivity
  have hd4 : 3 * ((u : ℝ) + 2 * v + 3) + 4 * 0 ≠ 0 := by positivity
  have hkey : dA0c1 u v + dA0c2 u v * ((u + v + 1) * (3 / 16))
        + dA0c3 u v * ((v + 1) * (3 / 16))
        + dA0c4 u v * ((u + v + 1) * (3 / 16) * ((v + 1) * (3 / 16)))
      = (20007 * u ^ 2 * v ^ 2 + 193401 * u ^ 2 * v + 173394 * u ^ 2
          + 60021 * u * v ^ 3 + 708183 * u * v ^ 2 + 1757322 * u * v + 1109160 * u
          + 40014 * v ^ 4 + 596349 * v ^ 3 + 2671542 * v ^ 2 + 4707693 * v + 2592486)
        / (8192 * (v + 7) * (3 * v + 26) * (u + v + 2) * (u + 2 * v + 3)) := by
    simp only [dA0c1, dA0c2, dA0c3, dA0c4, Fw_five, Fw_one_five, zw_one_five, zw]
    field_simp
    ring
  rw [hkey]
  positivity

/-! ### The assembled cell theorem -/

/-- **The direct cell cA = 0, certified on the whole environment box** (cap 3/16,
    one-arm floor 3/23): the topped-up merge comparison is nonnegative for every
    admissible environment.  First of the 36 cells. -/
theorem directA0_cell (u v sQ sS : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ sQ) (hQ1 : sQ ≤ (u + v + 1) * (3 / 16))
    (hS0 : 3 / 23 ≤ sS) (hS1 : sS ≤ (v + 1) * (3 / 16)) :
    beforeD (2 + v + u) (2 + v) 0 5 0 sQ sS ≤ afterD (2 + v + u) (2 + v) 0 0 sQ sS := by
  rw [← sub_nonneg, dA0_bilinear]
  have h00 := dA0_corner00 u v hu hv
  have h01 := dA0_corner01 u v hu hv
  have h10 := dA0_corner10 u v hu hv
  have h11 := dA0_corner11 u v hu hv
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 h00 h01 h10 h11

end Step3
end R3Cert
