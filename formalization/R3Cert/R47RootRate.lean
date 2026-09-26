import Mathlib
import R3Cert.R47Head
import R3Cert.R47Backbone
import R3Cert.R47BackboneAmp
import R3Cert.R47RateZBound

/-!
  # The general phantom-root identity and rooting bound (Hdom rate-assembly brick)

  `R47RateZBound.pi_le_rate` handles a SINGLE-child leaf rooting `node [K]`:
  `Aobj (node [K]) ≤ (4/3)·rhoB^n`, via the phantom-root split `Aobj = A0 + A1/m`,
  `Ztot(dtSub) = A0 + A1/(2m)`.  This file generalizes that split to an ARBITRARY
  multi-child root, which is what a hub/backbone root actually is.

  The exact structural fact: for `t = node cs` with root child count `d = |cs|`, the
  matching partition function factors (via `Matched_factor` + `Popen_dtChildren` +
  `wQ_ts_factor`) as

      Ztot(node (dtChildren k cs)) = P·(1 + qSum/k),   P = ∏_child Ztot(dtSub K)

  with `P`, `qSum cs` both INDEPENDENT of the realization degree `k`.  Since
  `Aobj t = Ztot(dtRealize t)` uses root degree `k = d` and `Ztot(dtSub t)` uses
  `k = d+1`, and `Zopen(dtSub t) = P`, this gives the exact **phantom-root identity**

      (d+1)·Ztot(dtSub t) = d·Aobj(t) + Zopen(dtSub t)        (`rooting_identity`)

  and hence, since `Zopen ≥ 0`, the **rooting bound**

      Aobj(t) ≤ (d+1)/d · Ztot(dtSub t)                       (`Aobj_le_rooting`)

  Composed with `Ztot_dtSub_le_rhoB_pow` (`Ztot(dtSub t) ≤ rhoB^(usize t)`) and a
  capped root (`d ≥ 5`, so `(d+1)/d ≤ 6/5`), this bounds a capped backbone's
  objective by `(6/5)·rhoB^n`.

  HONEST SCOPE.  This bounds `Aobj(backboneU s)` by `(6/5)·rhoB^n`, which sits ABOVE
  the tie `~0.92·rhoB^n` — so it does NOT close the Hdom domination layer.  The gap
  between `(d+1)/d` (worst rooting) and the tie's `~0.92` rooting factor is exactly
  the rooting/Ztot TRADE-OFF (a bad-rooting tree pays with a low `Ztot`): the
  irreducible combinatorial content of the seam, which a size-normalized rate bound
  cannot see.  This file supplies the exact rooting factor as a reusable identity;
  the trade-off itself remains the open Hdom crux.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

open RTree

/-- The dressed cavity sum is nonnegative (a sum of nonnegative per-child cavities). -/
theorem qSum_nonneg (cs : List UTree) : 0 ≤ qSum cs := by
  unfold qSum
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨K, _, rfl⟩ := hx
  have h1 := Zopen_dt_pos K
  have h2 := Ztot_dt_pos K
  positivity

/-- **Root-degree factorization.**  Realizing `cs` as node children at ANY degree `k`
    gives `Ztot = (∏ child Ztot)·(1 + qSum/k)`; the product `P` and `qSum cs` do not
    depend on `k` (only the `1/k` weight does).  Holds for `k = 0` too (both sides `P`,
    since `1/0 = 0` and `qSum` is finite). -/
theorem Ztot_node_deg (k : ℕ) (cs : List UTree) :
    Ztot (RTree.node (dtChildren k cs))
      = (cs.map fun K => Ztot (dtSub K)).prod * (1 + (1 / (k : ℝ)) * qSum cs) := by
  have hne : ∀ p ∈ dtChildren k cs, Ztot p.2 ≠ 0 := by
    intro p hp
    obtain ⟨K, _, _, hp2⟩ := mem_dtChildren hp
    rw [hp2]; exact ne_of_gt (Ztot_dt_pos K)
  have hZ : Ztot (RTree.node (dtChildren k cs))
      = Popen (dtChildren k cs) + Matched (dtChildren k cs) := rfl
  rw [hZ, Matched_factor _ hne]
  simp only [Popen_dtChildren]
  rw [wQ_ts_factor]
  ring

/-- **The general phantom-root identity** (multi-child generalization of `Ztot_single`
    / the `pi_le_rate` split): for `t = node cs` with root child count `d = |cs|`,

      (d+1)·Ztot(dtSub t) = d·Aobj(t) + Zopen(dtSub t).

    `Aobj` roots at degree `d`, `Ztot(dtSub)` at degree `d+1`, and both share the same
    child product `P = Zopen(dtSub t)` and cavity sum `qSum cs`; the identity is the
    exact bookkeeping of the two `1/degree` weightings. -/
theorem rooting_identity (cs : List UTree) :
    ((cs.length : ℝ) + 1) * Ztot (dtSub (UTree.node cs))
      = (cs.length : ℝ) * Aobj (UTree.node cs) + Zopen (dtSub (UTree.node cs)) := by
  have hZopen : Zopen (RTree.node (dtChildren (cs.length + 1) cs))
      = (cs.map fun K => Ztot (dtSub K)).prod := by
    have h : Zopen (RTree.node (dtChildren (cs.length + 1) cs))
        = Popen (dtChildren (cs.length + 1) cs) := rfl
    rw [h, Popen_dtChildren]
  rw [Aobj, dtRealize_node, dtSub_node, Ztot_node_deg, Ztot_node_deg, hZopen]
  rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
  · -- degenerate leaf-like root: cs.length = 0 forces qSum cs = 0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero h0
    subst hcs
    norm_num [qSum]
  · have hd : (cs.length : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
    ring

/-- **The rooting bound**: `Aobj(t) ≤ (d+1)/d · Ztot(dtSub t)` for a root with `d ≥ 1`
    children.  Immediate from `rooting_identity` and `Zopen ≥ 0`.  (`pi_le_rate` is the
    `d = 1` case, giving `4/3`; a capped root has `d ≥ 5`, giving `≤ 6/5`.) -/
theorem Aobj_le_rooting (cs : List UTree) (hpos : 0 < cs.length) :
    Aobj (UTree.node cs)
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * Ztot (dtSub (UTree.node cs)) := by
  have hid := rooting_identity cs
  have hd : (0 : ℝ) < (cs.length : ℝ) := by exact_mod_cast hpos
  have hZop : 0 ≤ Zopen (dtSub (UTree.node cs)) := le_of_lt (Zopen_dt_pos _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith [hid, hZop]

/-- **The rooting bound against the rate**: `Aobj(t) ≤ (d+1)/d · rhoB^(usize t)`.
    Chains `Aobj_le_rooting` with `Ztot_dtSub_le_rhoB_pow`. -/
theorem Aobj_le_rooting_rate (cs : List UTree) (hpos : 0 < cs.length) :
    Aobj (UTree.node cs)
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * rhoB ^ usize (UTree.node cs) := by
  have h1 := Aobj_le_rooting cs hpos
  have h2 : Ztot (dtSub (UTree.node cs)) ≤ rhoB ^ usize (UTree.node cs) :=
    Ztot_dtSub_le_rhoB_pow (UTree.node cs)
  have hfac : (0 : ℝ) ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) := by positivity
  calc Aobj (UTree.node cs)
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * Ztot (dtSub (UTree.node cs)) := h1
    _ ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * rhoB ^ usize (UTree.node cs) :=
        mul_le_mul_of_nonneg_left h2 hfac

/-- **Capped backbone rate bound**: a nonempty backbone whose root hub carries `≥ 5`
    arms (in particular any `Capped` state, the Hdom domain) has `Aobj ≤ (6/5)·rhoB^n`.
    The general rooting bound at a Capped root degree `d = arms + cherries + tail ≥ 5`,
    where `(d+1)/d ≤ 6/5`.

    HONEST: `(6/5)·rhoB^n` sits ABOVE the tie `~0.92·rhoB^n`, so this does NOT close the
    Hdom domination layer — it is the rate-assembly upper side, isolating the residual
    rooting/Ztot trade-off as the open crux.  conjecture1_proved = False. -/
theorem Aobj_backbone_le_rate (arms : List ℕ) (c : ℕ) (rest : List Hub)
    (hcap : 5 ≤ arms.length) :
    Aobj (backboneU ((arms, c) :: rest))
      ≤ (6 / 5 : ℝ) * rhoB ^ usize (backboneU ((arms, c) :: rest)) := by
  rw [backboneU_eq]
  set cs := arms.map armU ++ List.replicate c cherryU ++ tailU rest with hcs
  have h5 : 5 ≤ cs.length := by
    rw [hcs]
    simp only [List.length_append, List.length_map, List.length_replicate]
    omega
  have hpos : 0 < cs.length := by omega
  have hdpos : (0 : ℝ) < (cs.length : ℝ) := by exact_mod_cast hpos
  have hd : (5 : ℝ) ≤ (cs.length : ℝ) := by exact_mod_cast h5
  have hbound := Aobj_le_rooting_rate cs hpos
  have hfac : ((cs.length : ℝ) + 1) / (cs.length : ℝ) ≤ 6 / 5 := by
    rw [div_le_iff₀ hdpos]; nlinarith [hd]
  have hrho : (0 : ℝ) ≤ rhoB ^ usize (UTree.node cs) := le_of_lt (pow_pos rhoB_pos _)
  calc Aobj (UTree.node cs)
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * rhoB ^ usize (UTree.node cs) := hbound
    _ ≤ (6 / 5 : ℝ) * rhoB ^ usize (UTree.node cs) := mul_le_mul_of_nonneg_right hfac hrho

end Step3
end R3Cert
