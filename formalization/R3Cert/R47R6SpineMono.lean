/-
  R47 R6 SPINE MONOTONICITY -- propagating a balancing gain from a NESTED hub up the backbone.

  `Aobj_balance_le_tail` / `Aobj_balance_le_backbone` (R47R6BalanceTail, #132) balance the arms of the
  TOP hub of a backbone.  To reach a DEEPER hub, a local balancing gain in a sub-backbone must
  propagate up through the cavity recursion.  The engine is that `Ztot`/`Zopen` of a hub node are
  BOTH monotone in the `(Ztot, Zopen)` of the tail child:

    Ztot(node) = M·E·Ztot(child) + (M/(d·u))·Zopen(child),   Zopen(node) = M·Ztot(child)

  with `M = ∏arm·(3/2)^c ≥ 0`, `E = 1 + armsum + c/(3d) ≥ 0`, `u = udeg child`, from `Ztot_hubNode`.

  FOUNDATIONS (this stage):
    * `abR_balance_le`            -- the `z0 = 0` case of the coupled comparison: `abR a·abR b ≤ abR(a+1)·abR(b-1)`.
    * `armZ_balance_le`           -- one arm-pair transfer raises the arm value product `∏ Ztot(dtSub(armU·))`.
    * `hub_Zopen_balance_le`      -- balancing raises `Zopen` of a hub node (any degree `d`).
    * `hub_Ztot_split`           -- the abstract-degree two-arm `Ztot` split (analogue of `Aobj_cons2_tail`).
    * `hub_Ztot_balance_le`      -- balancing raises `Ztot` of a hub node (any degree `d ≥ 6`).

  HONEST SCOPE.  These are the balance-monotonicity foundations for the deep-hub propagation.  The
  child-replacement monotonicity and the spine induction that assemble them into
  `Aobj_balance_le_deep` are separate.  conjecture1_proved = False.  Self-contained; no `sorry`/`axiom`.
-/
import Mathlib
import R3Cert.R47R6BalanceTail
import R3Cert.R47R6CoupledNatCert
import R3Cert.R47R6ArmBalanceIdCert
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47HubForms
import R3Cert.R47Mono

namespace R3Cert
namespace Step3

open RTree

/-- `Ztot (dtSub (armU j)) = (3/2)^j · abR j` -- the arm value in `abR` form. -/
theorem Ztot_dtSub_armU_abR (j : ℕ) : Ztot (dtSub (armU j)) = (3 / 2) ^ j * abR (j : ℝ) := by
  rw [Ztot_dtSub_armU, abR]
  have h1 : (3 : ℝ) * ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (3 : ℝ) * (j : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- **The `z0 = 0` arm-balance:** `abR a · abR b ≤ abR (a+1) · abR (b-1)` -- the coupled comparison with
    zero coupling (pure Pólya arm-product balancing). -/
theorem abR_balance_le (a b : ℕ) (ha : 3 ≤ a) (hb : a + 2 ≤ b) :
    abR (a : ℝ) * abR (b : ℝ) ≤ abR ((a : ℝ) + 1) * abR ((b : ℝ) - 1) := by
  have h := armBalance_coupled_le_nat a b ha hb 1 0 (le_refl 1) (by norm_num)
  simpa using h

/-- **One arm-pair transfer raises the arm value product.**  `Ztot(dtSub(armU a))·Ztot(dtSub(armU b))
    ≤ Ztot(dtSub(armU(a+1)))·Ztot(dtSub(armU(b-1)))`: the `(3/2)` powers are common, and the `abR`
    factors obey `abR_balance_le`. -/
theorem armZ_balance_le (a b : ℕ) (ha : 3 ≤ a) (hb : a + 2 ≤ b) :
    Ztot (dtSub (armU a)) * Ztot (dtSub (armU b))
      ≤ Ztot (dtSub (armU (a + 1))) * Ztot (dtSub (armU (b - 1))) := by
  have hbpos : 1 ≤ b := by omega
  rw [Ztot_dtSub_armU_abR, Ztot_dtSub_armU_abR, Ztot_dtSub_armU_abR, Ztot_dtSub_armU_abR]
  have ha1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hbpos, Nat.cast_one]
  rw [ha1, hb1]
  have hpow : (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ b = (3 / 2 : ℝ) ^ (a + 1) * (3 / 2 : ℝ) ^ (b - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have habr := abR_balance_le a b ha hb
  have hpos : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (a + 1) * (3 / 2 : ℝ) ^ (b - 1) := by positivity
  calc (3 / 2 : ℝ) ^ a * abR (a : ℝ) * ((3 / 2 : ℝ) ^ b * abR (b : ℝ))
      = ((3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ b) * (abR (a : ℝ) * abR (b : ℝ)) := by ring
    _ ≤ ((3 / 2 : ℝ) ^ (a + 1) * (3 / 2 : ℝ) ^ (b - 1)) * (abR ((a : ℝ) + 1) * abR ((b : ℝ) - 1)) := by
        rw [hpow]; exact mul_le_mul_of_nonneg_left habr hpos
    _ = (3 / 2 : ℝ) ^ (a + 1) * abR ((a : ℝ) + 1) * ((3 / 2 : ℝ) ^ (b - 1) * abR ((b : ℝ) - 1)) := by ring

/-- **Balancing raises `Zopen` of a hub node** (any degree `d`).  `Zopen(node(dtChildren d cs)) =
    ∏ Ztot(dtSub child)` is degree-independent; the arm-pair transfer raises the arm-value product
    `armProd` (`armZ_balance_le`) while the cherries and tail are common. -/
theorem hub_Zopen_balance_le (a b : ℕ) (rest : List ℕ) (c : ℕ) (ts : List UTree) (d : ℕ)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) :
    Zopen (RTree.node (dtChildren d ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts)))
      ≤ Zopen (RTree.node (dtChildren d (((a + 1) :: (b - 1) :: rest).map armU
          ++ List.replicate c cherryU ++ ts))) := by
  rw [Zopen, Zopen, Popen_dtChildren, Popen_dtChildren]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def,
    List.map_cons, List.prod_cons]
  set Prest : ℝ := (List.map (fun j => Ztot (dtSub (armU j))) rest).prod with hPrest
  set Pcherry : ℝ := (List.map (fun K => Ztot (dtSub K)) (List.replicate c cherryU)).prod with hPcherry
  set Pts : ℝ := (List.map (fun K => Ztot (dtSub K)) ts).prod with hPts
  have hK : 0 ≤ Prest * (Pcherry * Pts) := by
    have hp : 0 ≤ Prest := by
      rw [hPrest]; apply List.prod_nonneg; intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le
    have hc : 0 ≤ Pcherry := by
      rw [hPcherry]; apply List.prod_nonneg; intro x hx
      obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le
    have ht : 0 ≤ Pts := by
      rw [hPts]; apply List.prod_nonneg; intro x hx
      obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le
    positivity
  have harm := armZ_balance_le a b ha hb
  calc Ztot (dtSub (armU a)) * (Ztot (dtSub (armU b)) * Prest) * Pcherry * Pts
      = (Ztot (dtSub (armU a)) * Ztot (dtSub (armU b))) * (Prest * (Pcherry * Pts)) := by ring
    _ ≤ (Ztot (dtSub (armU (a + 1))) * Ztot (dtSub (armU (b - 1)))) * (Prest * (Pcherry * Pts)) :=
        mul_le_mul_of_nonneg_right harm hK
    _ = Ztot (dtSub (armU (a + 1))) * (Ztot (dtSub (armU (b - 1))) * Prest) * Pcherry * Pts := by ring

/-- **Abstract-degree two-arm `Ztot` split** (analogue of `Aobj_cons2_tail` with the degree `d` a free
    parameter instead of the child count).  Peels the head arms `a, b` off `Ztot(node(dtChildren d …))`. -/
theorem hub_Ztot_split (a b : ℕ) (rest : List ℕ) (c : ℕ) (ts : List UTree) (d : ℕ) (hd : 0 < d) :
    Ztot (RTree.node (dtChildren d ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts)))
      = Ztot (dtSub (armU a)) * Ztot (dtSub (armU b)) * armProd rest * (3 / 2) ^ c
          * (ts.map (fun K => Ztot (dtSub K))).prod
        * (1 + (3 / ((d : ℝ) * (4 * (a : ℝ) + 3)) + 3 / ((d : ℝ) * (4 * (b : ℝ) + 3))
              + (rest.map (fun j : ℕ => 3 / ((d : ℝ) * (4 * (j : ℝ) + 3)))).sum
              + (c : ℝ) * (1 / (3 * (d : ℝ)))
              + ((dtChildren d ts).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)) := by
  rw [Ztot_hubNode d hd (a :: b :: rest) c ts (fun K _ => Ztot_dt_pos K)]
  simp only [List.map_cons, List.prod_cons, List.sum_cons, armProd, List.map_map, Function.comp_def]
  ring

/-- **Balancing raises `Ztot` of a hub node** for any degree `d ≥ 6`.  The abstract-degree analogue of
    `Aobj_balance_le_tail`: the tail block, cherries and rest arms are common; the head arm-pair transfer
    is closed by the abstract coupled comparison `armBalance_coupled_le_nat` with `P ≥ 1`, `z0 = 1/d ≤ 1/6`. -/
theorem hub_Ztot_balance_le (a b : ℕ) (rest : List ℕ) (c : ℕ) (ts : List UTree) (d : ℕ)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) (hd6 : 6 ≤ d) :
    Ztot (RTree.node (dtChildren d ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ ts)))
      ≤ Ztot (RTree.node (dtChildren d (((a + 1) :: (b - 1) :: rest).map armU
          ++ List.replicate c cherryU ++ ts))) := by
  have hbpos : 1 ≤ b := by omega
  have hbge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbpos
  have hd0 : 0 < d := by omega
  set D : ℝ := (d : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast hd0
  have hD6 : (6 : ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hd6
  set Pts : ℝ := (ts.map (fun K => Ztot (dtSub K))).prod with hPtsdef
  set S : ℝ := (rest.map (fun j : ℕ => 3 / (D * (4 * (j : ℝ) + 3)))).sum with hSdef
  set Tts : ℝ := ((dtChildren d ts).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum with hTtsdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply List.sum_nonneg; intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; positivity
  have hTtsnn : 0 ≤ Tts := by rw [hTtsdef]; exact tail_env_nonneg _ ts
  have hP : (1 : ℝ) ≤ 1 + (S + (c : ℝ) * (1 / (3 * D)) + Tts) := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * (1 / (3 * D)) := by positivity
    linarith [hSnn, hTtsnn]
  have hz0 : 1 / D ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hDpos (by norm_num)]; linarith [hD6]
  have hcoup := armBalance_coupled_le_nat a b ha hb
    (1 + (S + (c : ℝ) * (1 / (3 * D)) + Tts)) (1 / D) hP hz0
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
  rw [hub_Ztot_split a b rest c ts d hd0, hub_Ztot_split (a + 1) (b - 1) rest c ts d hd0]
  rw [Ztot_dtSub_armU a, Ztot_dtSub_armU b, Ztot_dtSub_armU (a + 1), Ztot_dtSub_armU (b - 1)]
  rw [← hDdef, ← hSdef, ← hPtsdef, ← hTtsdef]
  have ha1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hbpos, Nat.cast_one]
  rw [ha1, hb1]
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
  have e5 : 4 * (a : ℝ) + 3 ≠ 0 := by positivity
  have e6 : 4 * (b : ℝ) + 3 ≠ 0 := by positivity
  have e7 : 4 * ((a : ℝ) + 1) + 3 ≠ 0 := by positivity
  have e8 : 4 * ((b : ℝ) - 1) + 3 ≠ 0 := by
    rw [show 4 * ((b : ℝ) - 1) + 3 = 4 * (b : ℝ) - 1 from by ring]
    exact (by linarith : (0 : ℝ) < 4 * (b : ℝ) - 1).ne'
  have e9 : D ≠ 0 := hDpos.ne'
  exact le_trans (le_of_eq (by field_simp; ring))
    (le_trans (mul_le_mul_of_nonneg_left hcoup hpre) (le_of_eq (by field_simp; ring)))

/-! ### Child-replacement monotonicity -- the cavity recursion is linear-nonnegative in the tail child. -/

/-- **The snoc `Ztot` decomposition.**  `Ztot(node(dtChildren d (pre ++ [T])))` is LINEAR in the tail
    child's `(Ztot, Zopen)` with nonnegative coefficients:
      `= Popen(A)·(1 + Σ_A)·Ztot(dtSub T) + Popen(A)·(1/(d·udeg T))·Zopen(dtSub T)`,
    `A = dtChildren d pre`, `Σ_A = Σ p.1·Zopen/Ztot`.  Via `Matched_factor` + `Popen_append`. -/
theorem Ztot_node_snoc (pre : List UTree) (T : UTree) (d : ℕ) :
    Ztot (RTree.node (dtChildren d (pre ++ [T])))
      = Popen (dtChildren d pre)
          * (1 + ((dtChildren d pre).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum)
          * Ztot (dtSub T)
        + Popen (dtChildren d pre) * (1 / ((d : ℝ) * (udeg T : ℝ))) * Zopen (dtSub T) := by
  have hne : ∀ p ∈ dtChildren d (pre ++ [T]), Ztot p.2 ≠ 0 := by
    intro p hp; obtain ⟨K, -, -, hp2⟩ := mem_dtChildren hp; rw [hp2]; exact (Ztot_dt_pos K).ne'
  have hzt : Ztot (dtSub T) ≠ 0 := (Ztot_dt_pos T).ne'
  rw [Ztot, Matched_factor _ hne]
  simp only [dtChildren_append, dtChildren_cons, dtChildren_nil, Popen_append, Popen_cons,
    show Popen ([] : List (ℝ × RTree)) = 1 from rfl, mul_one, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  field_simp
  ring

/-- **`Zopen` is monotone in the tail child's `Ztot`.**  `Zopen(node) = ∏ Ztot(dtSub child)`, so replacing
    the tail child by one of larger `Ztot(dtSub)` does not decrease it. -/
theorem node_Zopen_child_mono (pre : List UTree) (T T' : UTree) (d : ℕ)
    (h : Ztot (dtSub T) ≤ Ztot (dtSub T')) :
    Zopen (RTree.node (dtChildren d (pre ++ [T])))
      ≤ Zopen (RTree.node (dtChildren d (pre ++ [T']))) := by
  rw [Zopen, Zopen, Popen_dtChildren, Popen_dtChildren]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  apply mul_le_mul_of_nonneg_left h
  apply List.prod_nonneg; intro x hx
  obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le

/-- **`Ztot` is monotone in the tail child's `(Ztot, Zopen)`** (given equal root degree `udeg`).  From the
    snoc decomposition: both coefficients are nonnegative and common. -/
theorem node_Ztot_child_mono (pre : List UTree) (T T' : UTree) (d : ℕ)
    (hzt : Ztot (dtSub T) ≤ Ztot (dtSub T')) (hzo : Zopen (dtSub T) ≤ Zopen (dtSub T'))
    (hu : udeg T = udeg T') :
    Ztot (RTree.node (dtChildren d (pre ++ [T])))
      ≤ Ztot (RTree.node (dtChildren d (pre ++ [T']))) := by
  rw [Ztot_node_snoc, Ztot_node_snoc, hu]
  have hPopen : 0 ≤ Popen (dtChildren d pre) := by
    rw [Popen_dtChildren]; apply List.prod_nonneg; intro x hx
    obtain ⟨K, -, rfl⟩ := List.mem_map.1 hx; exact (Ztot_dt_pos _).le
  have hSum : 0 ≤ ((dtChildren d pre).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum :=
    tail_env_nonneg d pre
  have hC1 : 0 ≤ Popen (dtChildren d pre)
      * (1 + ((dtChildren d pre).map (fun p => p.1 * (Zopen p.2 / Ztot p.2))).sum) :=
    mul_nonneg hPopen (by linarith [hSum])
  have hC2 : 0 ≤ Popen (dtChildren d pre) * (1 / ((d : ℝ) * (udeg T' : ℝ))) :=
    mul_nonneg hPopen (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hzt hC1) (mul_le_mul_of_nonneg_left hzo hC2)

/-! ### The spine induction -- propagating the balancing gain up to `Aobj`. -/

/-- The chain tail of a NONEMPTY hub list is the single realized backbone. -/
theorem tailU_ne_nil (l : List Hub) (h : l ≠ []) : tailU l = [backboneU l] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- Balancing a hub deep in a backbone preserves the ROOT degree `udeg (backboneU …)` (the balancing
    hub keeps its arm count, and every hub keeps the chain-tail child). -/
theorem udeg_backboneU_balance (pre' : List Hub) (a b : ℕ) (rest : List ℕ) (c : ℕ) (post : List Hub) :
    udeg (backboneU (pre' ++ (a :: b :: rest, c) :: post))
      = udeg (backboneU (pre' ++ ((a + 1) :: (b - 1) :: rest, c) :: post)) := by
  cases pre' with
  | nil =>
    simp only [List.nil_append]
    rw [backboneU_eq, backboneU_eq, udeg_node, udeg_node]
    simp only [List.length_append, List.length_map, List.length_replicate, List.length_cons]
  | cons h t =>
    obtain ⟨arms_h, c_h⟩ := h
    simp only [List.cons_append]
    rw [backboneU_eq, backboneU_eq, udeg_node, udeg_node,
      tailU_ne_nil _ (by simp), tailU_ne_nil _ (by simp)]
    simp only [List.length_append, List.length_map, List.length_replicate, List.length_cons]

/-- **The spine pair-induction.**  Balancing the arm-pair `(a,b)` of the hub at position `|pre|` in a
    backbone raises BOTH `Zopen` and `Ztot` of the realized subtree `dtSub (backboneU …)`.  Base: the
    balanced hub is the head, closed by `hub_Zopen_balance_le`/`hub_Ztot_balance_le` at its `dtSub`
    degree.  Step: the balanced hub is inside the tail child; the IH raises the child pair, and
    `node_Zopen_child_mono`/`node_Ztot_child_mono` propagate it up. -/
theorem spine_balance_pair (pre : List Hub) (a b : ℕ) (rest : List ℕ) (c : ℕ) (post : List Hub)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) (hreg : 6 ≤ (a :: b :: rest).length + c + (tailU post).length) :
    Zopen (dtSub (backboneU (pre ++ (a :: b :: rest, c) :: post)))
        ≤ Zopen (dtSub (backboneU (pre ++ ((a + 1) :: (b - 1) :: rest, c) :: post)))
      ∧ Ztot (dtSub (backboneU (pre ++ (a :: b :: rest, c) :: post)))
        ≤ Ztot (dtSub (backboneU (pre ++ ((a + 1) :: (b - 1) :: rest, c) :: post))) := by
  induction pre with
  | nil =>
    simp only [List.nil_append]
    rw [backboneU_eq, backboneU_eq, dtSub_node, dtSub_node]
    have hlenEq : (((a + 1) :: (b - 1) :: rest).map armU ++ List.replicate c cherryU ++ tailU post).length
        = ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ tailU post).length := by
      simp [List.length_append, List.length_map]
    rw [hlenEq]
    set D : ℕ := ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ tailU post).length + 1
      with hD
    have hcslen : ((a :: b :: rest).map armU ++ List.replicate c cherryU ++ tailU post).length
        = (a :: b :: rest).length + c + (tailU post).length := by
      rw [List.length_append, List.length_append, List.length_map, List.length_replicate]
    have hD6 : 6 ≤ D := by rw [hD]; omega
    exact ⟨hub_Zopen_balance_le a b rest c (tailU post) D ha hb,
      hub_Ztot_balance_le a b rest c (tailU post) D ha hb hD6⟩
  | cons h0 pre' ih =>
    obtain ⟨arms0, c0⟩ := h0
    simp only [List.cons_append]
    rw [backboneU_eq, backboneU_eq, tailU_ne_nil _ (by simp), tailU_ne_nil _ (by simp),
      dtSub_node, dtSub_node]
    have hlenEq : (arms0.map armU ++ List.replicate c0 cherryU
          ++ [backboneU (pre' ++ ((a + 1) :: (b - 1) :: rest, c) :: post)]).length
        = (arms0.map armU ++ List.replicate c0 cherryU
          ++ [backboneU (pre' ++ (a :: b :: rest, c) :: post)]).length := by
      simp [List.length_append]
    rw [hlenEq]
    obtain ⟨ihZo, ihZt⟩ := ih
    have hu := udeg_backboneU_balance pre' a b rest c post
    exact ⟨node_Zopen_child_mono _ _ _ _ ihZt, node_Ztot_child_mono _ _ _ _ ihZt ihZo hu⟩

/-- **Deep-hub balancing raises `Aobj`.**  Balancing the arm-pair `(a,b)` of the hub at ANY position
    `|pre|` in a backbone does not decrease `Aobj`.  For `pre = []` it is `Aobj_balance_le_tail` (the top
    hub, #132); otherwise the balanced hub is inside the tail child, and `spine_balance_pair` +
    `node_Ztot_child_mono` propagate the gain to the root. -/
theorem Aobj_balance_le_deep (pre : List Hub) (a b : ℕ) (rest : List ℕ) (c : ℕ) (post : List Hub)
    (ha : 3 ≤ a) (hb : a + 2 ≤ b) (hreg : 6 ≤ (a :: b :: rest).length + c + (tailU post).length) :
    Aobj (backboneU (pre ++ (a :: b :: rest, c) :: post))
      ≤ Aobj (backboneU (pre ++ ((a + 1) :: (b - 1) :: rest, c) :: post)) := by
  cases pre with
  | nil =>
    simp only [List.nil_append]
    rw [backboneU_eq, backboneU_eq]
    exact Aobj_balance_le_tail a b rest c (tailU post) ha hb hreg
  | cons h0 pre' =>
    obtain ⟨arms0, c0⟩ := h0
    simp only [List.cons_append]
    rw [backboneU_eq, backboneU_eq, tailU_ne_nil _ (by simp), tailU_ne_nil _ (by simp)]
    simp only [Aobj, dtRealize_node]
    have hlenEq : (arms0.map armU ++ List.replicate c0 cherryU
          ++ [backboneU (pre' ++ ((a + 1) :: (b - 1) :: rest, c) :: post)]).length
        = (arms0.map armU ++ List.replicate c0 cherryU
          ++ [backboneU (pre' ++ (a :: b :: rest, c) :: post)]).length := by
      simp [List.length_append]
    rw [hlenEq]
    obtain ⟨ihZo, ihZt⟩ := spine_balance_pair pre' a b rest c post ha hb hreg
    have hu := udeg_backboneU_balance pre' a b rest c post
    exact node_Ztot_child_mono _ _ _ _ ihZt ihZo hu

end Step3
end R3Cert
