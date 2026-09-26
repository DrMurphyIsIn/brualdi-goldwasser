/-
  R47 R6 single-hub balancing-transfer Aobj comparison -- the connective identity, assembled.

  Combines the Aobj list-split (`Aobj_cons2`, #117), the arm-value closed form
  (`Ztot_dtSub_armU`), and the Nat-indexed coupled comparison
  (`armBalance_coupled_le_nat`, #116) into the actual objective inequality: on a single hub,
  moving a cherry from the longer arm `b` to the shorter arm `a` (`(a,b) -> (a+1,b-1)`,
  `3 <= a`, `a+2 <= b`) does not decrease `Aobj`, provided the hub is in the certified
  many-arm regime `|a::b::rest| + c >= 6`.

  HONEST SCOPE.  The balancing-transfer Aobj comparison -- the connective identity for the
  Hnorm (general tree -> star) direction.  It does NOT include the transfer induction to a
  canonical form, the tie instantiation, nor the conjecture.  Self-contained; genuine proof
  (no `sorry`, no `axiom`, no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6AobjSplitCert
import R3Cert.R47R6CoupledNatCert
import R3Cert.R47HubForms
import R3Cert.R47Mono

namespace R3Cert
namespace Step3

open RTree

/-- **Single-hub balancing-transfer Aobj comparison.** -/
theorem Aobj_balance_le (a b : ℕ) (rest : List ℕ) (c : ℕ)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) (hd6 : 6 ≤ (a :: b :: rest).length + c) :
    Aobj (backboneU [(a :: b :: rest, c)])
      ≤ Aobj (backboneU [((a + 1) :: (b - 1) :: rest, c)]) := by
  have hbpos : 1 ≤ b := by omega
  have hbge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbpos
  have hd1 : 0 < (a :: b :: rest).length + c := by omega
  have hd2 : 0 < ((a + 1) :: (b - 1) :: rest).length + c := by omega
  have hlen : ((a + 1) :: (b - 1) :: rest).length = (a :: b :: rest).length := by simp
  -- the shared degree and coupling factor
  set D : ℝ := (((a :: b :: rest).length + c : ℕ) : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast hd1
  have hD6 : (6 : ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hd6
  set S : ℝ := (rest.map (fun j : ℕ => 3 / (D * (4 * (j : ℝ) + 3)))).sum with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; positivity
  -- environment parameters for the coupled comparison
  have hP : (1 : ℝ) ≤ 1 + (S + (c : ℝ) * (1 / (3 * D))) := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * (1 / (3 * D)) := by positivity
    linarith [hSnn]
  have hz0 : 1 / D ≤ 1 / 6 := by gcongr
  -- the coupled comparison at Nat indices a, b (explicit environment factor, unfolded)
  have hcoup := armBalance_coupled_le_nat a b ha hb
    (1 + (S + (c : ℝ) * (1 / (3 * D)))) (1 / D) hP hz0
  -- unfold abR/abH in the coupled comparison to the raw arm form
  have hbridge : ∀ x : ℝ, 0 ≤ x → abR x = 1 + x / (3 * (x + 1)) := by
    intro x hx; rw [abR]
    have h1 : (3 : ℝ) * x + 3 ≠ 0 := by positivity
    have h2 : (3 : ℝ) * (x + 1) ≠ 0 := by positivity
    field_simp; ring
  have hbridgeH : ∀ x : ℝ, abH x = 3 / (4 * x + 3) := fun x => by rw [abH]
  rw [hbridge _ (Nat.cast_nonneg a), hbridge _ (Nat.cast_nonneg b),
    hbridge _ (by positivity : (0:ℝ) ≤ (a:ℝ) + 1),
    hbridge _ (by linarith : (0:ℝ) ≤ (b:ℝ) - 1),
    hbridgeH _, hbridgeH _, hbridgeH _, hbridgeH _] at hcoup
  -- split both objectives and expand the four arm values
  rw [Aobj_cons2 a b rest c hd1, Aobj_cons2 (a + 1) (b - 1) rest c hd2, hlen,
    Ztot_dtSub_armU a, Ztot_dtSub_armU b, Ztot_dtSub_armU (a + 1), Ztot_dtSub_armU (b - 1)]
  -- fold the shared degree and sum
  rw [← hDdef, ← hSdef]
  -- normalize the Nat casts of a+1, b-1
  have ha1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hbpos, Nat.cast_one]
  rw [ha1, hb1]
  -- prefactor and power identity
  have hpre : 0 ≤ armProd rest * (3 / 2 : ℝ) ^ c * ((3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ b) :=
    mul_nonneg (mul_nonneg (armProd_pos rest).le (by positivity)) (by positivity)
  -- put both power products into the common form (3/2)^a, (3/2)^(b-1), (3/2)
  have hb2 : (3 / 2 : ℝ) ^ b = (3 / 2 : ℝ) ^ (b - 1) * (3 / 2) := by
    rw [← pow_succ]; congr 1; omega
  rw [pow_succ (3 / 2 : ℝ) a, hb2]
  rw [hb2] at hpre
  -- nonzero denominators for field_simp (ring cannot factor D*(4a+3))
  have e1 : (a : ℝ) + 1 ≠ 0 := by positivity
  have e2 : (b : ℝ) + 1 ≠ 0 := by positivity
  have e3 : (a : ℝ) + 1 + 1 ≠ 0 := by positivity
  have e4 : (b : ℝ) - 1 + 1 ≠ 0 := by
    rw [show (b : ℝ) - 1 + 1 = (b : ℝ) from by ring]; exact (by linarith : (0 : ℝ) < (b : ℝ)).ne'
  have e5 : 4 * (a : ℝ) + 3 ≠ 0 := by positivity
  have e6 : 4 * (b : ℝ) + 3 ≠ 0 := by positivity
  have e7 : 4 * ((a : ℝ) + 1) + 3 ≠ 0 := by positivity
  have e8 : 4 * ((b : ℝ) - 1) + 3 ≠ 0 := by
    rw [show 4 * ((b : ℝ) - 1) + 3 = 4 * (b : ℝ) - 1 from by ring]
    exact (by linarith : (0 : ℝ) < 4 * (b : ℝ) - 1).ne'
  have e9 : D ≠ 0 := hDpos.ne'
  exact le_trans (le_of_eq (by field_simp; ring))
    (le_trans (mul_le_mul_of_nonneg_left hcoup hpre) (le_of_eq (by field_simp; ring)))

end Step3
end R3Cert
