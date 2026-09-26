/-
  Bridge STEP 4b: BRANCH MULTIPLICATIVITY in the cherry-hub limit -- machine-checked.

  `branch_multiplicativity.py` promotes `Phi(G) = prod_i Phi(G_i)` to "proven in the limit,
  O(1/p^2) error, mechanism rigorous", and notes the only missing piece for full formality is
  the uniform bound on the O(1/p^2) constant.  KEY SIMPLIFICATION here: since the DEC amplitude
  is DEFINED by the `p -> infinity` hub limit, the multiplicativity statement only needs the
  LIMIT, not the rate -- the O(1/p^2) constant was needed only for numerical extrapolation.

  At the `Branch` level the mechanism is an EXACT finite-`p` identity plus one vanishing term:

    logPhi (hub_p ++ Gs) - logPhi (hub_p)
        = logPhiSum Gs + [eroot cH (rep p arm ++ Gs) - eroot cH (rep p arm)]     (exact, all p)

  and the bracket -> 0 as `p -> infinity`:
  * the `log (ac cH nch)` terms both -> `log ((3/2)^cH / rhoB^(1+2cH))` (the `1 + c/(3d)` factor
    -> 1 as the hub degree grows), so their difference -> 0;
  * the `log (1 + z*S)` terms both -> `log (1 + cav arm)` (the same decoupling as
    `hub_rho0_limit`: the branch contribution to the hub cavity sum is O(1/p)), difference -> 0.

  Main result: `logPhi_hub_diff_tendsto` --

    Tendsto (fun p => logPhi (node cH (replicate p arm ++ Gs)) - logPhi (node cH (replicate p arm)))
      atTop (nhds (logPhiSum Gs))

  i.e. the hub-limit amplitude of a gadget list is EXACTLY the sum of the branch log-amplitudes:
  `Phi(G) = prod_i Phi(G_i)` in the limit, for EVERY hub cherry-count, arm shape and gadget list.
  This machine-checks the assembly mechanism of the near-star reduction (R7): what remains of
  Step 4 after this file is the amplitude seam tying `logPhi`/DEC to the RAW finite-tree
  `per L / prod deg` (the `a(d,c)`/cherry-folding accounting), plus independent review.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4
import R3Cert.NearStar

namespace R3Cert
namespace Step4

open Filter Topology

/-- Sum of child log-amplitudes splits over list append. -/
theorem logPhiSum_append (l1 l2 : List Branch) :
    logPhiSum (l1 ++ l2) = logPhiSum l1 + logPhiSum l2 := by
  induction l1 with
  | nil => simp [logPhiSum]
  | cons b rest ih => rw [List.cons_append, logPhiSum, logPhiSum, ih]; ring

/-- The generic hub-denominator limit `3(pm + S)/(3p + D) -> m` (the `hub_rho0_limit` inner
    step, extracted as a reusable lemma). -/
theorem tendsto_zc_term (m S D : ℝ) (hD : 0 < D) :
    Tendsto (fun p : ℕ => 3 * ((p : ℝ) * m + S) / (3 * (p : ℝ) + D)) atTop (𝓝 m) := by
  have hdenpos : ∀ p : ℕ, 0 < 3 * (p : ℝ) + D := fun p => by positivity
  have hden : Tendsto (fun p : ℕ => 3 * (p : ℝ) + D) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have heq : (fun p : ℕ => 3 * ((p : ℝ) * m + S) / (3 * (p : ℝ) + D))
      = fun p : ℕ => m + (3 * S - m * D) / (3 * (p : ℝ) + D) := by
    ext p
    have hne := (hdenpos p).ne'
    field_simp
    ring
  rw [heq]
  have h0 : Tendsto (fun p : ℕ => (3 * S - m * D) / (3 * (p : ℝ) + D)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  simpa using tendsto_const_nhds.add h0

/-- As the hub degree grows, the DEC dressing `a(d,c)` converges to `(3/2)^c / rhoB^(1+2c)`
    (the `1 + c/(3d)` factor -> 1), uniformly in a fixed length offset `b`. -/
theorem tendsto_ac_shift (c b : ℕ) :
    Tendsto (fun p : ℕ => ac c (p + b)) atTop
      (𝓝 ((3 / 2 : ℝ) ^ c / rhoB ^ (1 + 2 * c))) := by
  have hden : Tendsto (fun p : ℕ => 3 * ((p : ℝ) + (b : ℝ) + 1 + (c : ℝ))) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
    apply tendsto_atTop_add_const_right
    apply tendsto_atTop_add_const_right
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun p : ℕ => (c : ℝ) / (3 * ((p : ℝ) + (b : ℝ) + 1 + (c : ℝ))))
      atTop (𝓝 0) := Tendsto.div_atTop tendsto_const_nhds hden
  have heq : (fun p : ℕ => ac c (p + b)) = fun p : ℕ =>
      (3 / 2 : ℝ) ^ c * (1 + (c : ℝ) / (3 * ((p : ℝ) + (b : ℝ) + 1 + (c : ℝ))))
        / rhoB ^ (1 + 2 * c) := by
    funext p
    rw [ac]
    push_cast
    ring
  rw [heq]
  have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).add h0).const_mul ((3 / 2 : ℝ) ^ c)
  have h2 := h1.div_const (rhoB ^ (1 + 2 * c))
  simpa using h2

/-- **The vanishing seam term**: the `eroot` difference between the hub with and without the
    gadget list tends to `0` -- the hub forgets the gadgets. -/
theorem eroot_hub_diff_tendsto (cH : ℕ) (arm : Branch) (Gs : List Branch) :
    Tendsto (fun p : ℕ =>
        eroot cH (List.replicate p arm ++ Gs) - eroot cH (List.replicate p arm))
      atTop (𝓝 0) := by
  set b : ℕ := Gs.length with hbdef
  set m : ℝ := cav arm with hm
  set S : ℝ := cavSum Gs with hS
  set Db : ℝ := 3 * (b : ℝ) + 3 + 4 * (cH : ℝ) with hDb
  set D0 : ℝ := (3 : ℝ) + 4 * (cH : ℝ) with hD0
  have hDbpos : 0 < Db := by rw [hDb]; positivity
  have hD0pos : 0 < D0 := by rw [hD0]; positivity
  have hLpos : 0 < (3 / 2 : ℝ) ^ cH / rhoB ^ (1 + 2 * cH) :=
    div_pos (pow_pos (by norm_num) _) (pow_pos rhoB_pos _)
  have hmpos : 0 < m := by rw [hm]; exact cav_pos arm
  have h1m : (1 : ℝ) + m ≠ 0 := ne_of_gt (by linarith)
  have hA1 : Tendsto (fun p : ℕ => Real.log (ac cH (p + b))) atTop
      (𝓝 (Real.log ((3 / 2 : ℝ) ^ cH / rhoB ^ (1 + 2 * cH)))) :=
    (tendsto_ac_shift cH b).log hLpos.ne'
  have hA2 : Tendsto (fun p : ℕ => Real.log (ac cH p)) atTop
      (𝓝 (Real.log ((3 / 2 : ℝ) ^ cH / rhoB ^ (1 + 2 * cH)))) := by
    have h := (tendsto_ac_shift cH 0).log hLpos.ne'
    simpa using h
  have hZ1 : Tendsto (fun p : ℕ =>
      Real.log (1 + 3 * ((p : ℝ) * m + S) / (3 * (p : ℝ) + Db)))
      atTop (𝓝 (Real.log (1 + m))) :=
    (tendsto_const_nhds.add (tendsto_zc_term m S Db hDbpos)).log h1m
  have hZ2 : Tendsto (fun p : ℕ =>
      Real.log (1 + 3 * ((p : ℝ) * m) / (3 * (p : ℝ) + D0)))
      atTop (𝓝 (Real.log (1 + m))) := by
    have h := (tendsto_const_nhds.add (tendsto_zc_term m 0 D0 hD0pos)).log h1m
    simpa using h
  have hcomb := (hA1.sub hA2).add (hZ1.sub hZ2)
  have hpt : ∀ p : ℕ, eroot cH (List.replicate p arm ++ Gs)
      - eroot cH (List.replicate p arm)
      = (Real.log (ac cH (p + b)) - Real.log (ac cH p))
        + (Real.log (1 + 3 * ((p : ℝ) * m + S) / (3 * (p : ℝ) + Db))
          - Real.log (1 + 3 * ((p : ℝ) * m) / (3 * (p : ℝ) + D0))) := by
    intro p
    have hl1 : (List.replicate p arm ++ Gs).length = p + b := by simp [hbdef]
    have hl2 : (List.replicate p arm).length = p := by simp
    have hc1 : cavSum (List.replicate p arm ++ Gs) = (p : ℝ) * m + S := by
      rw [cavSum_append, cavSum_replicate, ← hm, ← hS]
    have hc2 : cavSum (List.replicate p arm) = (p : ℝ) * m := by
      rw [cavSum_replicate, ← hm]
    rw [eroot, eroot, hl1, hl2, hc1, hc2]
    have harg1 : (1 : ℝ) + zc cH (p + b) * ((p : ℝ) * m + S)
        = 1 + 3 * ((p : ℝ) * m + S) / (3 * (p : ℝ) + Db) := by
      rw [zc, hDb]; push_cast; ring
    have harg2 : (1 : ℝ) + zc cH p * ((p : ℝ) * m)
        = 1 + 3 * ((p : ℝ) * m) / (3 * (p : ℝ) + D0) := by
      rw [zc, hD0]; push_cast; ring
    rw [harg1, harg2]
    ring
  simp_rw [hpt]
  simpa using hcomb

/-- **STEP 4b (main): branch multiplicativity in the hub limit.**  The log-amplitude EXCESS of
    the hub carrying a gadget list `Gs`, over the bare hub, converges to `logPhiSum Gs` -- i.e.
    `Phi(G) = prod_i Phi(G_i)` in the `p -> infinity` cherry-hub limit, for every hub
    cherry-count `cH`, arm shape and gadget list.  The finite-`p` identity is exact; the only
    limit content is the vanishing `eroot` seam. -/
theorem logPhi_hub_diff_tendsto (cH : ℕ) (arm : Branch) (Gs : List Branch) :
    Tendsto (fun p : ℕ =>
        logPhi (Branch.node cH (List.replicate p arm ++ Gs))
          - logPhi (Branch.node cH (List.replicate p arm)))
      atTop (𝓝 (logPhiSum Gs)) := by
  have hpt : ∀ p : ℕ, logPhi (Branch.node cH (List.replicate p arm ++ Gs))
      - logPhi (Branch.node cH (List.replicate p arm))
      = logPhiSum Gs + (eroot cH (List.replicate p arm ++ Gs)
        - eroot cH (List.replicate p arm)) := by
    intro p
    rw [logPhi, logPhi, logPhiSum_append, logPhiSum_replicate]
    ring
  have h : Tendsto (fun p : ℕ => logPhiSum Gs
      + (eroot cH (List.replicate p arm ++ Gs) - eroot cH (List.replicate p arm)))
      atTop (𝓝 (logPhiSum Gs + 0)) :=
    tendsto_const_nhds.add (eroot_hub_diff_tendsto cH arm Gs)
  simp_rw [hpt]
  simpa using h

end Step4
end R3Cert
