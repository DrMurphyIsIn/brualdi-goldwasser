/-
  R3Cert.BGGrowthRate -- the exponential growth rate of the Brualdi-Goldwasser maximum.

  Brualdi and Goldwasser (1984) asked for the maximum of the Laplacian ratio
  `pi(T) = per(L(T)) / prod_v deg(v)` over trees on `n` vertices (`Aobj`, via `pi_utree`).
  The exact maximizer is open.  This file pins down its exponential order EXACTLY:

      (64/621) * rhoB^n  <=  max_{|T| = n} pi(T)  <=  2 * rhoB^(n-1),
      rhoB = (621/64)^(1/11) ~ 1.22948,

  so `(max pi)^(1/n) -> rhoB`.  (Pant 2026's families grow like (3/2)^(n/2) ~ 1.2247^n.)

  Upper bound.  Root any tree at a vertex with children `cs` (true root degree `d = |cs|`):
  `Aobj = P * (1 + qSum/d)` (`Ztot_node_deg`), where `P` is the product of the children's
  PLANTED partition functions -- each child's root degree already counts the edge to the centre --
  so `P <= rhoB^(n-1)` by the planted ceiling `Ztot_dtSub_le_rhoB_pow` (the `Phi <= 1` hinge),
  and every `qSum` term is `Zopen/Ztot/udeg <= 1`.
  Lower bound.  The centre carrying `K` arms of five cherries (`armU 5`, planted value exactly
  `621/64 = rhoB^11`, the unique equality case of the sharp ceiling `bg_sharp`) plus at most ten
  filler vertices (cherries and one leaf).

  Kernel-checked, no `sorry`.  This is the growth rate, not the exact maximizer:
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47RootRate
import R3Cert.R47NearStarValue
import R3Cert.LemmaA

namespace R3Cert
namespace Step3

open RTree

theorem rhoB_pow_eleven : rhoB ^ 11 = (621 / 64 : ℝ) := by
  unfold rhoB
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `Aobj` of a root with children `cs`, at its true degree. -/
theorem Aobj_node_eq (cs : List UTree) :
    Aobj (UTree.node cs)
      = (cs.map fun K => Ztot (dtSub K)).prod * (1 + (1 / (cs.length : ℝ)) * qSum cs) := by
  rw [Aobj, dtRealize_node, Ztot_node_deg]

/-- The product of planted child values is at most `rhoB ^ (total child size)`. -/
theorem prod_Ztot_le (cs : List UTree) :
    (cs.map fun K => Ztot (dtSub K)).prod ≤ rhoB ^ usizeList cs := by
  induction cs with
  | nil => simp [usizeList]
  | cons c rest ih =>
    simp only [List.map_cons, List.prod_cons, usizeList_cons, pow_add]
    exact mul_le_mul (Ztot_dtSub_le_rhoB_pow c) ih
      (List.prod_nonneg (fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨K, _, rfl⟩ := hx
        exact le_of_lt (Ztot_dt_pos K)))
      (pow_nonneg (le_of_lt rhoB_pos) _)

/-- Every dressed cavity term is at most one, so `qSum cs ≤ |cs|`. -/
theorem qSum_le_length (cs : List UTree) : qSum cs ≤ (cs.length : ℝ) := by
  unfold qSum
  induction cs with
  | nil => simp
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have hZ := Ztot_dt_pos c
    have hle := Zopen_le_Ztot_dt c
    have hr : Zopen (dtSub c) / Ztot (dtSub c) ≤ 1 := (div_le_one hZ).mpr hle
    have hr0 : 0 ≤ Zopen (dtSub c) / Ztot (dtSub c) := le_of_lt (div_pos (Zopen_dt_pos c) hZ)
    have hu : (1 : ℝ) ≤ (udeg c : ℝ) := by
      cases c with
      | node ks => rw [udeg_node]; push_cast; linarith [(Nat.cast_nonneg ks.length : (0:ℝ) ≤ _)]
    have h1 : Zopen (dtSub c) / Ztot (dtSub c) / (udeg c : ℝ) ≤ 1 :=
      (div_le_one (by linarith)).mpr (le_trans hr hu)
    linarith

/-- **Upper bound.**  Every tree on `n` vertices has `pi(T) = Aobj ≤ 2 · rhoB^(n-1)`. -/
theorem Aobj_le_two_rhoB_pow (t : UTree) : Aobj t ≤ 2 * rhoB ^ (usize t - 1) := by
  cases t with
  | node cs =>
    rw [Aobj_node_eq, usize_node, Nat.add_sub_cancel_left]
    have hP := prod_Ztot_le cs
    have hP0 : 0 ≤ (cs.map fun K => Ztot (dtSub K)).prod :=
      List.prod_nonneg (fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨K, _, rfl⟩ := hx
        exact le_of_lt (Ztot_dt_pos K))
    have hq0 := qSum_nonneg cs
    have hbr : 1 + (1 / (cs.length : ℝ)) * qSum cs ≤ 2 := by
      rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
      · rw [h0]; simp
      · have hd : (0 : ℝ) < cs.length := by exact_mod_cast hpos
        have := qSum_le_length cs
        have h1 : (1 / (cs.length : ℝ)) * qSum cs ≤ 1 := by
          rw [one_div, inv_mul_le_iff₀ hd]; linarith
        linarith
    have hbr0 : 0 ≤ 1 + (1 / (cs.length : ℝ)) * qSum cs := by positivity
    calc (cs.map fun K => Ztot (dtSub K)).prod * (1 + (1 / (cs.length : ℝ)) * qSum cs)
        ≤ rhoB ^ usizeList cs * 2 := mul_le_mul hP hbr hbr0 (pow_nonneg (le_of_lt rhoB_pos) _)
      _ = 2 * rhoB ^ usizeList cs := by ring

/-- The same bound for the literal Laplacian permanent ratio of the realized tree. -/
theorem perm_ratio_le_two_rhoB_pow (t : UTree) :
    (lapl (aGraph (realize (dtRealize t)))).permanent
        / (∏ v, ((aGraph (realize (dtRealize t))).degree v : ℝ))
      ≤ 2 * rhoB ^ (usize t - 1) := by
  rw [pi_utree]; exact Aobj_le_two_rhoB_pow t

/-- `Aobj` is at least the product of the planted child values. -/
theorem prod_Ztot_le_Aobj (cs : List UTree) :
    (cs.map fun K => Ztot (dtSub K)).prod ≤ Aobj (UTree.node cs) := by
  rw [Aobj_node_eq]
  have hP0 : 0 ≤ (cs.map fun K => Ztot (dtSub K)).prod :=
    List.prod_nonneg (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨K, _, rfl⟩ := hx
      exact le_of_lt (Ztot_dt_pos K))
  have hq : 0 ≤ (1 / (cs.length : ℝ)) * qSum cs := by
    have := qSum_nonneg cs; positivity
  nlinarith

/-- The witness family: a centre carrying `K` five-cherry arms, `c` cherries and `l` leaves. -/
def growthWitness (K c l : ℕ) : UTree :=
  UTree.node (List.replicate K (armU 5) ++ List.replicate c cherryU ++
    List.replicate l (UTree.node []))

theorem usizeList_replicate (m : ℕ) (K : UTree) :
    usizeList (List.replicate m K) = m * usize K := by
  induction m with
  | zero => simp [usizeList]
  | succ m ih => rw [List.replicate_succ, usizeList_cons, ih]; ring

theorem usize_growthWitness (K c l : ℕ) :
    usize (growthWitness K c l) = 1 + 11 * K + 2 * c + l := by
  rw [growthWitness, usize_node, usizeList_append, usizeList_append,
    usizeList_replicate, usizeList_replicate, usizeList_replicate, usize_armU, usize_cherryU]
  have : usize (UTree.node []) = 1 := by rw [usize_node]; simp [usizeList]
  rw [this]; ring

theorem prod_growthWitness (K c l : ℕ) :
    ((List.replicate K (armU 5) ++ List.replicate c cherryU ++
      List.replicate l (UTree.node [])).map fun K => Ztot (dtSub K)).prod
      = (621 / 64 : ℝ) ^ K * (3 / 2) ^ c := by
  have hleaf : Ztot (dtSub (UTree.node [])) = 1 := by
    rw [dtSub_leaf, Ztot, Popen, Matched]; ring
  simp only [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
    Ztot_armU_five, Ztot_dtSub_cherryU, hleaf, one_pow, mul_one]

/-- **Lower bound.**  For every `n ≥ 1` some tree on `n` vertices has
    `Aobj ≥ (64/621) · rhoB^n`. -/
theorem exists_Aobj_ge (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : UTree, usize t = n ∧ (64 / 621 : ℝ) * rhoB ^ n ≤ Aobj t := by
  set K := (n - 1) / 11
  set r := (n - 1) % 11
  have hr : r < 11 := Nat.mod_lt _ (by norm_num)
  have hnK : n = 1 + 11 * K + r := by
    have := Nat.div_add_mod (n - 1) 11; omega
  refine ⟨growthWitness K (r / 2) (r % 2), ?_, ?_⟩
  · rw [usize_growthWitness]; have := Nat.div_add_mod r 2; omega
  · have hA := prod_Ztot_le_Aobj (List.replicate K (armU 5) ++ List.replicate (r / 2) cherryU ++
      List.replicate (r % 2) (UTree.node []))
    rw [prod_growthWitness] at hA
    have hρ1 : (1 : ℝ) ≤ rhoB := le_of_lt rhoB_gt_one
    have hρ0 : (0 : ℝ) ≤ rhoB := le_of_lt rhoB_pos
    have hpow : rhoB ^ (1 + r) ≤ rhoB ^ 11 := pow_le_pow_right₀ hρ1 (by omega)
    have hsplit : rhoB ^ n = rhoB ^ (11 * K) * rhoB ^ (1 + r) := by
      rw [hnK, ← pow_add]; congr 1; ring
    have h11K : rhoB ^ (11 * K) = (621 / 64 : ℝ) ^ K := by rw [pow_mul, rhoB_pow_eleven]
    have hc : (1 : ℝ) ≤ (3 / 2) ^ (r / 2) := one_le_pow₀ (by norm_num)
    have hK0 : (0 : ℝ) ≤ (621 / 64) ^ K := by positivity
    calc (64 / 621 : ℝ) * rhoB ^ n
        = (621 / 64) ^ K * ((64 / 621) * rhoB ^ (1 + r)) := by rw [hsplit, h11K]; ring
      _ ≤ (621 / 64) ^ K * 1 := by
          apply mul_le_mul_of_nonneg_left _ hK0
          rw [rhoB_pow_eleven] at hpow
          linarith
      _ ≤ (621 / 64) ^ K * (3 / 2) ^ (r / 2) := mul_le_mul_of_nonneg_left hc hK0
      _ ≤ Aobj (growthWitness K (r / 2) (r % 2)) := hA

/-- **The growth rate of the Brualdi-Goldwasser maximum.**  For every `n ≥ 1`:
    some tree on `n` vertices has `pi ≥ (64/621)·rhoB^n`, and every tree on `n` vertices has
    `pi ≤ 2·rhoB^(n-1)`.  Hence `(max_{|T|=n} pi(T))^(1/n) → rhoB = (621/64)^(1/11)`. -/
theorem bg_max_growth (n : ℕ) (hn : 1 ≤ n) :
    (∃ t : UTree, usize t = n ∧ (64 / 621 : ℝ) * rhoB ^ n ≤ Aobj t) ∧
    (∀ t : UTree, usize t = n → Aobj t ≤ 2 * rhoB ^ (n - 1)) :=
  ⟨exists_Aobj_ge n hn, fun t ht => ht ▸ Aobj_le_two_rhoB_pow t⟩

end Step3
end R3Cert
