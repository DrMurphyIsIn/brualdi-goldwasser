/-
  R47 R6 TAIL-GENERAL balancing transfer -- lifting the single-hub balance comparison to a hub
  carrying an ARBITRARY further child block `ts` (in particular, the chain tail of a multi-hub
  backbone).

  `Aobj_balance_le` (#118, R47R6BalanceLeCert) proves that on a SINGLE hub `[(arms, c)]` (no tail),
  moving a cherry from the longer arm `b` to the shorter arm `a` (`(a,b) -> (a+1,b-1)`) does not
  decrease `Aobj`.  Its hard core is the ABSTRACT coupled comparison `armBalance_coupled_le_nat`
  (R47R6CoupledNatCert), which holds for ANY environment `P >= 1` and coupling `z0 <= 1/6`.

  The single-hub split `Aobj_cons2` fixes the tail to be empty.  Here we replace it with the general
  hub-node formula `Ztot_hubNode` (R47Backbone), which already handles an arbitrary further child
  block `ts`: `ts` enters ONLY as a common prefactor `(∏ Ztot(dtSub K))` and a common environment
  term `Σ p.1·Zopen/Ztot`, BOTH untouched by the arm transfer (which preserves the arm count, hence
  the node degree `d = |a::b::rest| + c + |ts|`, and fixes `c`, `rest`, `ts`).  So the same abstract
  comparison closes it with `P = 1 + (rest-sum + c/(3d) + ts-term) >= 1` and `z0 = 1/d <= 1/6`.

  MAIN RESULTS:
    * `Aobj_cons2_tail`        -- the tail-general two-arm objective split (analogue of `Aobj_cons2`).
    * `Aobj_balance_le_tail`   -- the tail-general first-two-arms balance comparison.
    * `Aobj_transfer_le_tail`  -- the tail-general ARBITRARY-pair transfer (via `Aobj_node_perm`).
    * `Aobj_balance_le_backbone` -- specialization: balancing the arms of the TOP hub of ANY
      multi-hub backbone `(arms, c) :: hubs` does not decrease `Aobj`.

  HONEST SCOPE.  This is the tail-general balancing comparison for the TOP hub of a backbone -- one
  step toward the multi-hub `Hnorm`.  It does NOT include balancing DEEPER hubs (which needs the
  spine `Aobj`-monotonicity in a child's weight), the `{4,5}` arm-rate pinning, `Capped`, the
  arbitrary tree -> hub-state reduction, nor the conjecture.  Self-contained; genuine proof
  (no `sorry`, no `axiom`, no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6BalanceLeCert
import R3Cert.R47R6CoupledNatCert
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47HubForms
import R3Cert.R47Mono
import R3Cert.R47ArmPerm

namespace R3Cert
namespace Step3

open RTree

/-- The tail environment term `Σ_{p ∈ dtChildren d ts} p.1 · Zopen(p.2)/Ztot(p.2)` is nonnegative:
    each `p = (1/(d·udeg K), dtSub K)`, and `Zopen(dtSub K), Ztot(dtSub K) > 0` (`Zopen_dt_pos`,
    `Ztot_dt_pos`). -/
theorem tail_env_nonneg (d : ℕ) (ts : List UTree) :
    0 ≤ ((dtChildren d ts).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨K, -, hp1, hp2⟩ := mem_dtChildren hp
  rw [hp1, hp2]
  have hZt := Ztot_dt_pos K
  have hZo := Zopen_dt_pos K
  positivity

/-- **Tail-general two-arm objective split.**  `d = (|a::b::rest| + c + |ts| : ℕ)`.  Peels the
    leading two arms `a, b` off a hub node carrying an arbitrary further child block `ts`, exposing
    the head arm values, the common tail product `armProd rest`, the common cherry factor `(3/2)^c`,
    the common `ts` product, and the coupling with the two head slot-activities separated. -/
theorem Aobj_cons2_tail (a b : ℕ) (rest : List ℕ) (c : ℕ) (ts : List UTree)
    (hd : 0 < (a :: b :: rest).length + c + ts.length) :
    Aobj (UTree.node ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts))
      = Ztot (dtSub (armU a)) * Ztot (dtSub (armU b)) * armProd rest * (3 / 2) ^ c
          * (ts.map (fun K => Ztot (dtSub K))).prod
        * (1 + (3 / ((((a :: b :: rest).length + c + ts.length : ℕ) : ℝ) * (4 * (a : ℝ) + 3))
              + 3 / ((((a :: b :: rest).length + c + ts.length : ℕ) : ℝ) * (4 * (b : ℝ) + 3))
              + (rest.map (fun j : ℕ =>
                  3 / ((((a :: b :: rest).length + c + ts.length : ℕ) : ℝ) * (4 * (j : ℝ) + 3)))).sum
              + (c : ℝ) * (1 / (3 * (((a :: b :: rest).length + c + ts.length : ℕ) : ℝ)))
              + ((dtChildren ((a :: b :: rest).length + c + ts.length) ts).map
                  (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)) := by
  have hlen : ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts).length
      = (a :: b :: rest).length + c + ts.length := by
    rw [List.length_append, List.length_append, List.length_map, List.length_replicate]
  simp only [Aobj, dtRealize_node]
  rw [hlen]
  set d : ℕ := (a :: b :: rest).length + c + ts.length with hd_def
  clear_value d
  rw [Ztot_hubNode d hd (a :: b :: rest) c ts (fun K _ => Ztot_dt_pos K)]
  simp only [List.map_cons, List.prod_cons, List.sum_cons, armProd, List.map_map, Function.comp_def]
  ring

/-- **Tail-general single-hub balancing comparison.**  On a hub carrying an arbitrary further child
    block `ts`, moving a cherry from the longer arm `b` to the shorter arm `a` (`(a,b) -> (a+1,b-1)`,
    `3 <= a`, `a+2 <= b`, many-arm regime `|a::b::rest| + c + |ts| >= 6`) does not decrease `Aobj`. -/
theorem Aobj_balance_le_tail (a b : ℕ) (rest : List ℕ) (c : ℕ) (ts : List UTree)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) (hd6 : 6 ≤ (a :: b :: rest).length + c + ts.length) :
    Aobj (UTree.node ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts))
      ≤ Aobj (UTree.node (((a + 1) :: (b - 1) :: rest).map armU
          ++ List.replicate c cherryU ++ ts)) := by
  have hbpos : 1 ≤ b := by omega
  have hbge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbpos
  have hd1 : 0 < (a :: b :: rest).length + c + ts.length := by omega
  have hlen : ((a + 1) :: (b - 1) :: rest).length = (a :: b :: rest).length := by simp
  have hd2 : 0 < ((a + 1) :: (b - 1) :: rest).length + c + ts.length := by omega
  -- shared degree, tail product, tail-env, rest sum
  set D : ℝ := (((a :: b :: rest).length + c + ts.length : ℕ) : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast hd1
  have hD6 : (6 : ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hd6
  set Pts : ℝ := (ts.map (fun K => Ztot (dtSub K))).prod with hPtsdef
  set S : ℝ := (rest.map (fun j : ℕ => 3 / (D * (4 * (j : ℝ) + 3)))).sum with hSdef
  set Tts : ℝ :=
      ((dtChildren ((a :: b :: rest).length + c + ts.length) ts).map
        (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum with hTtsdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; positivity
  have hTtsnn : 0 ≤ Tts := by rw [hTtsdef]; exact tail_env_nonneg _ ts
  -- environment for the coupled comparison
  have hP : (1 : ℝ) ≤ 1 + (S + (c : ℝ) * (1 / (3 * D)) + Tts) := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * (1 / (3 * D)) := by positivity
    linarith [hSnn, hTtsnn]
  have hz0 : 1 / D ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hDpos (by norm_num)]; linarith [hD6]
  have hcoup := armBalance_coupled_le_nat a b ha hb
    (1 + (S + (c : ℝ) * (1 / (3 * D)) + Tts)) (1 / D) hP hz0
  -- unfold abR/abH to raw arm form
  have hbridge : ∀ x : ℝ, 0 ≤ x → abR x = 1 + x / (3 * (x + 1)) := by
    intro x hx; rw [abR]
    have h1 : (3 : ℝ) * x + 3 ≠ 0 := by positivity
    have h2 : (3 : ℝ) * (x + 1) ≠ 0 := by positivity
    field_simp; ring
  have hbridgeH : ∀ x : ℝ, abH x = 3 / (4 * x + 3) := fun x => by rw [abH]
  rw [hbridge _ (Nat.cast_nonneg a), hbridge _ (Nat.cast_nonneg b),
    hbridge _ (by positivity : (0:ℝ) ≤ (a:ℝ) + 1),
    hbridge _ (by linarith [hbge1] : (0:ℝ) ≤ (b:ℝ) - 1),
    hbridgeH _, hbridgeH _, hbridgeH _, hbridgeH _] at hcoup
  -- split both objectives (tail-general) and expand the four arm values
  rw [Aobj_cons2_tail a b rest c ts hd1]
  rw [show ((a + 1) :: (b - 1) :: rest).map armU ++ List.replicate c cherryU ++ ts
        = ((a + 1) :: (b - 1) :: rest).map armU ++ List.replicate c cherryU ++ ts from rfl]
  rw [Aobj_cons2_tail (a + 1) (b - 1) rest c ts hd2]
  rw [Ztot_dtSub_armU a, Ztot_dtSub_armU b, Ztot_dtSub_armU (a + 1), Ztot_dtSub_armU (b - 1)]
  -- fold shared degree, tail product/env, rest sum; align the two length forms
  simp only [hlen]
  rw [← hDdef, ← hSdef, ← hPtsdef, ← hTtsdef]
  -- normalize Nat casts of a+1, b-1
  have ha1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hbpos, Nat.cast_one]
  rw [ha1, hb1]
  -- common nonneg prefactor and the (3/2) power identity
  have hb2 : (3 / 2 : ℝ) ^ b = (3 / 2 : ℝ) ^ (b - 1) * (3 / 2) := by
    rw [← pow_succ]; congr 1; omega
  have hPtsnn : 0 ≤ Pts := by
    rw [hPtsdef]; apply List.prod_nonneg; intro x hx
    obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos K).le
  have hpre : 0 ≤ armProd rest * (3 / 2 : ℝ) ^ c * Pts
      * ((3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ (b - 1) * (3 / 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (armProd_pos rest).le (by positivity)) hPtsnn)
      (by positivity)
  rw [pow_succ (3 / 2 : ℝ) a, hb2]
  -- nonzero denominators for field_simp
  have e5 : 4 * (a : ℝ) + 3 ≠ 0 := by positivity
  have e6 : 4 * (b : ℝ) + 3 ≠ 0 := by positivity
  have e7 : 4 * ((a : ℝ) + 1) + 3 ≠ 0 := by positivity
  have e8 : 4 * ((b : ℝ) - 1) + 3 ≠ 0 := by
    rw [show 4 * ((b : ℝ) - 1) + 3 = 4 * (b : ℝ) - 1 from by ring]
    exact (by linarith : (0 : ℝ) < 4 * (b : ℝ) - 1).ne'
  have e9 : D ≠ 0 := hDpos.ne'
  exact le_trans (le_of_eq (by field_simp; ring))
    (le_trans (mul_le_mul_of_nonneg_left hcoup hpre) (le_of_eq (by field_simp; ring)))

/-- **Tail-general arbitrary-pair transfer.**  If a hub (with tail block `ts`) has arms containing
    `a` and `b` (`arms ~ a :: b :: rest`) with `3 <= a`, `a + 2 <= b`, and `arms'` moves one cherry
    from the `b`-arm to the `a`-arm (`arms' ~ (a+1) :: (b-1) :: rest`), then `Aobj` does not decrease.
    Proof: permute the pair to the front (`Aobj_node_perm`, which is general), apply
    `Aobj_balance_le_tail`, permute back. -/
theorem Aobj_transfer_le_tail {arms arms' : List ℕ} (a b : ℕ) (rest : List ℕ) (c : ℕ)
    (ts : List UTree) (ha : 3 ≤ a) (hb : a + 2 ≤ b)
    (hperm : arms.Perm (a :: b :: rest)) (hperm' : arms'.Perm ((a + 1) :: (b - 1) :: rest))
    (hd6 : 6 ≤ arms.length + c + ts.length) :
    Aobj (UTree.node (arms.map armU ++ List.replicate c cherryU ++ ts))
      ≤ Aobj (UTree.node (arms'.map armU ++ List.replicate c cherryU ++ ts)) := by
  have hlen : arms.length = (a :: b :: rest).length := hperm.length_eq
  have hpermC : (arms.map armU ++ List.replicate c cherryU ++ ts).Perm
      ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts) :=
    ((hperm.map armU).append_right _).append_right _
  have hpermC' : (arms'.map armU ++ List.replicate c cherryU ++ ts).Perm
      (((a + 1) :: (b - 1) :: rest).map armU ++ List.replicate c cherryU ++ ts) :=
    ((hperm'.map armU).append_right _).append_right _
  calc Aobj (UTree.node (arms.map armU ++ List.replicate c cherryU ++ ts))
      = Aobj (UTree.node ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts)) :=
        Aobj_node_perm hpermC
    _ ≤ Aobj (UTree.node (((a + 1) :: (b - 1) :: rest).map armU
          ++ List.replicate c cherryU ++ ts)) :=
        Aobj_balance_le_tail a b rest c ts ha hb (hlen ▸ hd6)
    _ = Aobj (UTree.node (arms'.map armU ++ List.replicate c cherryU ++ ts)) :=
        (Aobj_node_perm hpermC').symm

/-- **Balancing the TOP hub of any multi-hub backbone.**  Moving a cherry between two arms of the
    top hub `(a :: b :: rest, c)` of a backbone `... :: hubs` (with the rest of the chain `hubs` as
    its tail child) does not decrease `Aobj`.  Specializes `Aobj_balance_le_tail` with
    `ts = tailU hubs`. -/
theorem Aobj_balance_le_backbone (a b : ℕ) (rest : List ℕ) (c : ℕ) (hubs : List Hub)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b)
    (hd6 : 6 ≤ (a :: b :: rest).length + c + (tailU hubs).length) :
    Aobj (backboneU ((a :: b :: rest, c) :: hubs))
      ≤ Aobj (backboneU (((a + 1) :: (b - 1) :: rest, c) :: hubs)) := by
  rw [backboneU_eq, backboneU_eq]
  exact Aobj_balance_le_tail a b rest c (tailU hubs) ha hb hd6

end Step3
end R3Cert
