/-
  The (L) layer: cherries-optimal certificates (R2) -- LB_LAYER_DESIGN.md.

  Exact-rational content of legs.py's `certify_cherries_optimal`, re-validated GREEN
  and each inequality re-checked exactly at generation time:
  * `phiL` -- the leg matching factor (phiL 0 = 2 pads the recursion uniformly:
    phiL 2 = 1 + 2/4 = 3/2);
  * `phiL_le_beta` -- the envelope `phiL (n+3) <= (483/400)^(n+3)` (two norm_num
    bases + the induction step from beta^2 >= beta + 1/4);
  * `tie_anchor` -- F_2(6) = 621/64 EXACTLY (the cherry-bundle tie, c = 5);
  * `ell1_base`, `ell1_c1..c3` -- the length-1 row;
  * `legs_bignum` -- THE tail: 483^253 * 3^11 * 64^23 < 400^253 * 2^11 * 621^23
    (726-digit kernel arithmetic, ratio 1.108);
  * `sweep_l*_c*` -- the 39 finite-region certificates (c * l <= 21), each cleared
    to naturals.

  HONEST SCOPE: gadget-level (growth-rate) certificates -- the "legs are cherries"
  necessary condition.  The classification seam (rate-maximal families have cherry
  arms) is named at R7' assembly time.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47StepMono

namespace R3Cert
namespace Step3

set_option maxHeartbeats 4000000

/-! ### The leg matching factor -/

/-- `phiL 0 = 2` pads the recursion so `phiL 2 = 1 + 2/4 = 3/2` uniformly. -/
def phiL : ℕ → ℚ
  | 0 => 2
  | 1 => 1
  | n + 2 => phiL (n + 1) + phiL n / 4

theorem phiL_pos : ∀ l, 0 < phiL l
  | 0 => by norm_num [phiL]
  | 1 => by norm_num [phiL]
  | (n + 2) => by
    have h1 := phiL_pos (n + 1)
    have h2 := phiL_pos n
    rw [phiL]
    positivity

/-- The envelope: `phiL (n+3) <= (483/400)^(n+3)`. -/
theorem phiL_le_beta : ∀ n, phiL (n + 3) ≤ (483 / 400 : ℚ) ^ (n + 3)
  | 0 => by norm_num [phiL]
  | 1 => by norm_num [phiL]
  | (n + 2) => by
    have h1 := phiL_le_beta (n + 1)
    have h2 := phiL_le_beta n
    have e1 : n + 2 + 3 = (n + 3) + 2 := by omega
    have e2 : n + 1 + 3 = (n + 3) + 1 := by omega
    rw [e1, phiL]
    rw [e2] at h1
    have ep1 : (483 / 400 : ℚ) ^ ((n + 3) + 1) = (483 / 400) ^ (n + 3) * (483 / 400) :=
      pow_succ _ _
    have ep2 : (483 / 400 : ℚ) ^ ((n + 3) + 2)
        = (483 / 400) ^ (n + 3) * (483 / 400) * (483 / 400) := by
      rw [pow_succ, pow_succ]
    rw [ep2]
    rw [ep1] at h1
    nlinarith [h1, h2, mul_nonneg (pow_nonneg (by norm_num : (0:ℚ) ≤ 483 / 400) (n + 3))
      (by norm_num : (0:ℚ) ≤ (483 / 400 : ℚ) ^ 2 - 483 / 400 - 1 / 4)]

/-! ### The anchors and tails -/

/-- The cherry-bundle tie: `F_2(6) = 621/64` exactly (c = 5, the rho_B rate). -/
theorem tie_anchor : (3 / 2 : ℚ) ^ 5 + 5 * (1 / (6 * 2)) * 1 * (3 / 2 : ℚ) ^ 4
    = 621 / 64 := by norm_num

/-- The length-1 tail base: `2^11 * 64^5 < 621^5`. -/
theorem ell1_base : (2 : ℕ) ^ 11 * 64 ^ 5 < 621 ^ 5 := by norm_num

/-- **THE bignum tail** (c*l >= 22): `beta^253 (3/2)^11 < (621/64)^23` cleared. -/
theorem legs_bignum :
    (483 : ℕ) ^ 253 * 3 ^ 11 * 64 ^ 23 < 400 ^ 253 * 2 ^ 11 * 621 ^ 23 := by
  norm_num

/-! ### The length-1 row and the finite sweep (generated; each re-checked exactly) -/

theorem ell1_c1 : (3 : ℕ) ^ 11 * 64 ^ 2 < 621 ^ 2 * 2 ^ 11 := by norm_num

theorem ell1_c2 : (5 : ℕ) ^ 11 * 64 ^ 3 < 621 ^ 3 * 3 ^ 11 := by norm_num

theorem ell1_c3 : (7 : ℕ) ^ 11 * 64 ^ 4 < 621 ^ 4 * 4 ^ 11 := by norm_num

/-- **The general ℓ=1 rate row**: the single-legged star grows strictly slower
    than `rho_B` for EVERY `c ≥ 1` — `((1+2c)/(1+c))^11 < (621/64)^(1+c)` cleared
    to `ℕ`.  Upgrades the three finite `ell1_c*` checks to a statement quantified
    over ALL `c`: the `c ≤ 3` cases are exact (`interval_cases`), and the `c ≥ 4`
    tail is `(1+2c)^11 < 2^11 (1+c)^11` (from `1+2c < 2(1+c)`) together with
    `2^11 · 64^(1+c) ≤ 621^(1+c)` (from `ell1_base : 2^11·64^5 < 621^5` and `ℕ`
    monotonicity, splitting `1+c = 5 + (c-4)`).  Gadget level; the classification
    seam ("rate-maximal families have cherry arms") is named at R7' assembly.
    conjecture1_proved = False. -/
theorem ell1_rate (c : ℕ) (hc : 1 ≤ c) :
    (1 + 2 * c) ^ 11 * 64 ^ (1 + c) < 621 ^ (1 + c) * (1 + c) ^ 11 := by
  rcases Nat.lt_or_ge c 4 with h | h
  · interval_cases c <;> norm_num
  · have hbase : 2 ^ 11 * 64 ^ (1 + c) ≤ 621 ^ (1 + c) := by
      have hsplit : (1 : ℕ) + c = 5 + (c - 4) := by omega
      rw [hsplit, pow_add, pow_add]
      calc 2 ^ 11 * (64 ^ 5 * 64 ^ (c - 4))
          = 2 ^ 11 * 64 ^ 5 * 64 ^ (c - 4) := by ring
        _ ≤ 621 ^ 5 * 621 ^ (c - 4) := by gcongr <;> norm_num
    calc (1 + 2 * c) ^ 11 * 64 ^ (1 + c)
        < (2 * (1 + c)) ^ 11 * 64 ^ (1 + c) := by gcongr <;> omega
      _ = (1 + c) ^ 11 * (2 ^ 11 * 64 ^ (1 + c)) := by rw [mul_pow]; ring
      _ ≤ (1 + c) ^ 11 * 621 ^ (1 + c) := mul_le_mul_of_nonneg_left hbase (Nat.zero_le _)
      _ = 621 ^ (1 + c) * (1 + c) ^ 11 := by ring

theorem sweep_l3_c1 : (17 : ℕ) ^ 11 * 64 ^ 4 < 621 ^ 4 * 8 ^ 11 := by norm_num

theorem sweep_l3_c2 : (63 : ℕ) ^ 11 * 64 ^ 7 < 621 ^ 7 * 16 ^ 11 := by norm_num

theorem sweep_l3_c3 : (1813 : ℕ) ^ 11 * 64 ^ 10 < 621 ^ 10 * 256 ^ 11 := by norm_num

theorem sweep_l3_c4 : (16121 : ℕ) ^ 11 * 64 ^ 13 < 621 ^ 13 * 1280 ^ 11 := by norm_num

theorem sweep_l3_c5 : (45619 : ℕ) ^ 11 * 64 ^ 16 < 621 ^ 16 * 2048 ^ 11 := by norm_num

theorem sweep_l3_c6 : (160867 : ℕ) ^ 11 * 64 ^ 19 < 621 ^ 19 * 4096 ^ 11 := by norm_num

theorem sweep_l3_c7 : (9058973 : ℕ) ^ 11 * 64 ^ 22 < 621 ^ 22 * 131072 ^ 11 := by norm_num

theorem sweep_l4_c1 : (41 : ℕ) ^ 11 * 64 ^ 5 < 621 ^ 5 * 16 ^ 11 := by norm_num

theorem sweep_l4_c2 : (1105 : ℕ) ^ 11 * 64 ^ 9 < 621 ^ 9 * 192 ^ 11 := by norm_num

theorem sweep_l4_c3 : (25721 : ℕ) ^ 11 * 64 ^ 13 < 621 ^ 13 * 2048 ^ 11 := by norm_num

theorem sweep_l4_c4 : (555169 : ℕ) ^ 11 * 64 ^ 17 < 621 ^ 17 * 20480 ^ 11 := by norm_num

theorem sweep_l4_c5 : (11442377 : ℕ) ^ 11 * 64 ^ 21 < 621 ^ 21 * 196608 ^ 11 := by norm_num

theorem sweep_l5_c1 : (99 : ℕ) ^ 11 * 64 ^ 6 < 621 ^ 6 * 32 ^ 11 := by norm_num

theorem sweep_l5_c2 : (6437 : ℕ) ^ 11 * 64 ^ 11 < 621 ^ 11 * 768 ^ 11 := by norm_num

theorem sweep_l5_c3 : (361415 : ℕ) ^ 11 * 64 ^ 16 < 621 ^ 16 * 16384 ^ 11 := by norm_num

theorem sweep_l5_c4 : (18815433 : ℕ) ^ 11 * 64 ^ 21 < 621 ^ 21 * 327680 ^ 11 := by norm_num

theorem sweep_l6_c1 : (239 : ℕ) ^ 11 * 64 ^ 7 < 621 ^ 7 * 64 ^ 11 := by norm_num

theorem sweep_l6_c2 : (12507 : ℕ) ^ 11 * 64 ^ 13 < 621 ^ 13 * 1024 ^ 11 := by norm_num

theorem sweep_l6_c3 : (5086719 : ℕ) ^ 11 * 64 ^ 19 < 621 ^ 19 * 131072 ^ 11 := by norm_num

theorem sweep_l7_c1 : (577 : ℕ) ^ 11 * 64 ^ 8 < 621 ^ 8 * 128 ^ 11 := by norm_num

theorem sweep_l7_c2 : (72895 : ℕ) ^ 11 * 64 ^ 15 < 621 ^ 15 * 4096 ^ 11 := by norm_num

theorem sweep_l7_c3 : (71572613 : ℕ) ^ 11 * 64 ^ 22 < 621 ^ 22 * 1048576 ^ 11 := by norm_num

theorem sweep_l8_c1 : (1393 : ℕ) ^ 11 * 64 ^ 9 < 621 ^ 9 * 256 ^ 11 := by norm_num

theorem sweep_l8_c2 : (1274593 : ℕ) ^ 11 * 64 ^ 17 < 621 ^ 17 * 49152 ^ 11 := by norm_num

theorem sweep_l9_c1 : (3363 : ℕ) ^ 11 * 64 ^ 10 < 621 ^ 10 * 512 ^ 11 := by norm_num

theorem sweep_l9_c2 : (7428869 : ℕ) ^ 11 * 64 ^ 19 < 621 ^ 19 * 196608 ^ 11 := by norm_num

theorem sweep_l10_c1 : (8119 : ℕ) ^ 11 * 64 ^ 11 < 621 ^ 11 * 1024 ^ 11 := by norm_num

theorem sweep_l10_c2 : (14432875 : ℕ) ^ 11 * 64 ^ 21 < 621 ^ 21 * 262144 ^ 11 := by norm_num

theorem sweep_l11_c1 : (19601 : ℕ) ^ 11 * 64 ^ 12 < 621 ^ 12 * 2048 ^ 11 := by norm_num

theorem sweep_l12_c1 : (47321 : ℕ) ^ 11 * 64 ^ 13 < 621 ^ 13 * 4096 ^ 11 := by norm_num

theorem sweep_l13_c1 : (114243 : ℕ) ^ 11 * 64 ^ 14 < 621 ^ 14 * 8192 ^ 11 := by norm_num

theorem sweep_l14_c1 : (275807 : ℕ) ^ 11 * 64 ^ 15 < 621 ^ 15 * 16384 ^ 11 := by norm_num

theorem sweep_l15_c1 : (665857 : ℕ) ^ 11 * 64 ^ 16 < 621 ^ 16 * 32768 ^ 11 := by norm_num

theorem sweep_l16_c1 : (1607521 : ℕ) ^ 11 * 64 ^ 17 < 621 ^ 17 * 65536 ^ 11 := by norm_num

theorem sweep_l17_c1 : (3880899 : ℕ) ^ 11 * 64 ^ 18 < 621 ^ 18 * 131072 ^ 11 := by norm_num

theorem sweep_l18_c1 : (9369319 : ℕ) ^ 11 * 64 ^ 19 < 621 ^ 19 * 262144 ^ 11 := by norm_num

theorem sweep_l19_c1 : (22619537 : ℕ) ^ 11 * 64 ^ 20 < 621 ^ 20 * 524288 ^ 11 := by norm_num

theorem sweep_l20_c1 : (54608393 : ℕ) ^ 11 * 64 ^ 21 < 621 ^ 21 * 1048576 ^ 11 := by norm_num

theorem sweep_l21_c1 : (131836323 : ℕ) ^ 11 * 64 ^ 22 < 621 ^ 22 * 2097152 ^ 11 := by norm_num

end Step3
end R3Cert
