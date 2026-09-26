/-
  Bridge STEP 4d: the HUB SEAM -- the raw hub amplitude ratio converges to the DEC amplitude.

  STEP4C_DESIGN.md item (iv).  With items (i)+(ii) (BridgeStep4c: `Ztot_lit_eq_Wb`,
  `exp_logPhi_mul_rhoB_pow`) the amplitude is finite and local; what remains of the bridge is
  the TRUE-ROOT hub: the finite competitor tree's hub has NO phantom parent edge, so its raw
  hub factor differs from the branch closed form -- but only by a factor that -> 1.

  * `Ztot_litHub` -- the exact closed form of the literal hub partition function:
      `Ztot (litHub c ch) = (3/2)^c * WbProd ch * (1 + (c/3 + cavSum ch) / D)`,  `D = c + #ch`
    (true root degree, no `+1`).  Same `Matched_factor` computation as the branch case.
  * `amplitude_bridge` -- the finite-`p` ratio of the gadget-carrying hub over the bare hub:
      `Ztot (litHub cH (arms_p ++ [b])) / Ztot (litHub cH arms_p)  ->  Wb b`  as `p -> inf`.
    The `(3/2)^cH * WbProd arms` factors cancel EXACTLY at every finite `p`; the gadget
    contributes `Wb b` times the hub factor `(1 + S'_p)/(1 + S_p) -> (1+m)/(1+m) = 1`.

  As in Step 4b, no `O(1/p^2)` (or even `O(1/p)`) envelope is needed: the bridge statement is
  a limit, so `Tendsto` algebra on the exact rational closed forms suffices.

  Composed with `exp_logPhi_mul_rhoB_pow` (4c) and `phi_le_one` (the capstone), this ties the
  Branch amplitude to the raw matching partition functions of the literal competitor trees.
  The remaining glue to `per L / prod deg` is item (iii) (`litEdges`/`IsEdgeEnum`).

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4b
import R3Cert.BridgeStep4c

namespace R3Cert

open RTree Filter Topology Step4

/-! ### The literal hub (true root: degree `c + #children`, no phantom parent) -/

/-- The literal hub competitor: `c` cherries plus child branches `ch`, every hub-incident
    weight computed with the TRUE root degree `D = c + ch.length`. -/
noncomputable def litHub (c : ℕ) (ch : List Branch) : RTree :=
  RTree.node (List.replicate c (litCherry (c + ch.length)) ++ litChildren (c + ch.length) ch)

/-- Product of `Wb` splits over append. -/
theorem WbProd_append (l1 l2 : List Branch) :
    WbProd (l1 ++ l2) = WbProd l1 * WbProd l2 := by
  induction l1 with
  | nil => rw [List.nil_append, WbProd]; ring
  | cons K rest ih => rw [List.cons_append, WbProd, WbProd, ih]; ring

/-- **The exact hub closed form.** -/
theorem Ztot_litHub (c : ℕ) (ch : List Branch) (hD : 0 < c + ch.length) :
    Ztot (litHub c ch)
      = (3 / 2) ^ c * WbProd ch
        * (1 + ((c : ℝ) / 3 + cavSum ch) / ((c + ch.length : ℕ) : ℝ)) := by
  have hDR : (((c + ch.length : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hne : ∀ q ∈ List.replicate c (litCherry (c + ch.length))
      ++ litChildren (c + ch.length) ch, Ztot q.2 ≠ 0 := by
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · have hqe : q = litCherry (c + ch.length) := List.eq_of_mem_replicate h
      rw [hqe, Ztot_litCherry_snd]; norm_num
    · exact hne_litCh (c + ch.length) ch q h
  have hsum : ((List.replicate c (litCherry (c + ch.length))
        ++ litChildren (c + ch.length) ch).map
          (fun q => q.1 * (Zopen q.2 / Ztot q.2))).sum
      = (c : ℝ) * (1 / (3 * ((c + ch.length : ℕ) : ℝ)))
        + cavSum ch / ((c + ch.length : ℕ) : ℝ) := by
    simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul]
    rw [cherry_term _ hD, litCh_sum _ ch hD]
  rw [litHub, Ztot, Matched_factor _ hne, hsum, Popen_append, Popen_replicate_cherry,
    Popen_litCh_eq]
  field_simp

/-! ### The generic hub-load limit (denominator shift may be zero, so work eventually) -/

/-- `(p*m + S)/(p + E) -> m` for ANY real shift `E` (the denominator is only eventually
    nonzero, so the algebraic identity is applied eventually). -/
theorem tendsto_ratio_term (m S E : ℝ) :
    Tendsto (fun p : ℕ => ((p : ℝ) * m + S) / ((p : ℝ) + E)) atTop (𝓝 m) := by
  have hden : Tendsto (fun p : ℕ => (p : ℝ) + E) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun p : ℕ => (S - m * E) / ((p : ℝ) + E)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  have hlim0 : Tendsto (fun p : ℕ => m + (S - m * E) / ((p : ℝ) + E)) atTop (𝓝 (m + 0)) :=
    tendsto_const_nhds.add h0
  have hlim : Tendsto (fun p : ℕ => m + (S - m * E) / ((p : ℝ) + E)) atTop (𝓝 m) := by
    simpa using hlim0
  refine Tendsto.congr' ?_ hlim
  have hpos := hden.eventually_gt_atTop 0
  filter_upwards [hpos] with p hp
  have hne : ((p : ℝ) + E) ≠ 0 := hp.ne'
  field_simp
  ring

/-! ### The hub seam -/

/-- **STEP 4d (main): THE AMPLITUDE BRIDGE.**  The raw partition-function ratio of the
    gadget-carrying literal hub over the bare hub converges to the DEC amplitude `Wb b`
    (`= exp (logPhi b) * rhoB^(Vb b)` by 4c) as the arm count `p -> infinity` -- for every hub
    cherry count `cH`, arm shape and gadget branch `b`. -/
theorem amplitude_bridge (cH : ℕ) (arm b : Branch) :
    Tendsto (fun p : ℕ =>
        Ztot (litHub cH (List.replicate p arm ++ [b]))
          / Ztot (litHub cH (List.replicate p arm)))
      atTop (𝓝 (Wb b)) := by
  set m : ℝ := cav arm with hm
  have hmpos : 0 < m := by rw [hm]; exact cav_pos arm
  have h1m : (1 : ℝ) + m ≠ 0 := ne_of_gt (by linarith)
  -- the closed-form comparison sequence and its limit
  have hN : Tendsto (fun p : ℕ =>
      1 + ((p : ℝ) * m + ((cH : ℝ) / 3 + cav b)) / ((p : ℝ) + ((cH : ℝ) + 1)))
      atTop (𝓝 (1 + m)) :=
    tendsto_const_nhds.add (tendsto_ratio_term m ((cH : ℝ) / 3 + cav b) ((cH : ℝ) + 1))
  have hDn : Tendsto (fun p : ℕ =>
      1 + ((p : ℝ) * m + (cH : ℝ) / 3) / ((p : ℝ) + (cH : ℝ)))
      atTop (𝓝 (1 + m)) :=
    tendsto_const_nhds.add (tendsto_ratio_term m ((cH : ℝ) / 3) (cH : ℝ))
  have hF : Tendsto (fun p : ℕ => Wb b
      * ((1 + ((p : ℝ) * m + ((cH : ℝ) / 3 + cav b)) / ((p : ℝ) + ((cH : ℝ) + 1)))
        / (1 + ((p : ℝ) * m + (cH : ℝ) / 3) / ((p : ℝ) + (cH : ℝ)))))
      atTop (𝓝 (Wb b * ((1 + m) / (1 + m)))) :=
    ((hN.div hDn h1m)).const_mul (Wb b)
  rw [div_self h1m, mul_one] at hF
  refine Tendsto.congr' (Filter.EventuallyEq.symm ?_) hF
  filter_upwards [Filter.eventually_ge_atTop 1] with p hp
  -- pointwise, for p >= 1: both hubs have the exact closed form and the shared factor cancels
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hD0 : 0 < cH + (List.replicate p arm).length := by
    simp only [List.length_replicate]; omega
  have hD1 : 0 < cH + (List.replicate p arm ++ [b]).length := by
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  have hZ0 := Ztot_litHub cH (List.replicate p arm) hD0
  have hZ1 := Ztot_litHub cH (List.replicate p arm ++ [b]) hD1
  have hcs0 : cavSum (List.replicate p arm) = (p : ℝ) * m := by
    rw [cavSum_replicate, ← hm]
  have hcs1 : cavSum (List.replicate p arm ++ [b]) = (p : ℝ) * m + cav b := by
    rw [cavSum_append, cavSum_replicate, ← hm, cavSum, cavSum, add_zero]
  have hwp : WbProd (List.replicate p arm ++ [b])
      = WbProd (List.replicate p arm) * Wb b := by
    rw [WbProd_append, WbProd, WbProd, mul_one]
  rw [hZ0, hZ1, hcs0, hcs1, hwp]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    zero_add]
  push_cast
  -- nonvanishing facts for the cancellation
  have hcast_c : (0 : ℝ) ≤ (cH : ℝ) := by positivity
  have hA : (0 : ℝ) < (3 / 2) ^ cH * WbProd (List.replicate p arm) :=
    mul_pos (pow_pos (by norm_num) _) (WbProd_pos _)
  have hd0 : (0 : ℝ) < (cH : ℝ) + (p : ℝ) := by linarith
  have hd1 : (0 : ℝ) < (cH : ℝ) + ((p : ℝ) + 1) := by linarith
  have hload : (0 : ℝ) ≤ ((p : ℝ) * m + (cH : ℝ) / 3) / ((p : ℝ) + (cH : ℝ)) := by
    have hpm : (0 : ℝ) ≤ (p : ℝ) * m := mul_nonneg (by linarith) hmpos.le
    have hnum : (0 : ℝ) ≤ (p : ℝ) * m + (cH : ℝ) / 3 := by linarith
    exact div_nonneg hnum (by linarith)
  have hDnpos : (0 : ℝ) < 1 + ((p : ℝ) * m + (cH : ℝ) / 3) / ((p : ℝ) + (cH : ℝ)) := by
    linarith
  have hd0' : ((cH : ℝ) + (p : ℝ)) ≠ 0 := hd0.ne'
  have hd0'' : ((p : ℝ) + (cH : ℝ)) ≠ 0 := by
    rw [show (p : ℝ) + (cH : ℝ) = (cH : ℝ) + (p : ℝ) from by ring]; exact hd0.ne'
  have hd1' : ((cH : ℝ) + ((p : ℝ) + 1)) ≠ 0 := hd1.ne'
  have hd1'' : ((p : ℝ) + ((cH : ℝ) + 1)) ≠ 0 := by
    rw [show (p : ℝ) + ((cH : ℝ) + 1) = (cH : ℝ) + ((p : ℝ) + 1) from by ring]; exact hd1.ne'
  have hpow : ((3 / 2 : ℝ) ^ cH) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hWne : WbProd (List.replicate p arm) ≠ 0 := (WbProd_pos _).ne'
  have hA' : ((3 / 2 : ℝ) ^ cH * WbProd (List.replicate p arm)) ≠ 0 := hA.ne'
  have hDn' : (1 + ((p : ℝ) * m + (cH : ℝ) / 3) / ((p : ℝ) + (cH : ℝ))) ≠ 0 := hDnpos.ne'
  have hbase : (0 : ℝ) < 1 + ((cH : ℝ) / 3 + (p : ℝ) * m) / ((cH : ℝ) + (p : ℝ)) := by
    have hpm : (0 : ℝ) ≤ (p : ℝ) * m := mul_nonneg (by linarith) hmpos.le
    have hnum : (0 : ℝ) ≤ (cH : ℝ) / 3 + (p : ℝ) * m := by linarith
    have := div_nonneg hnum (by linarith : (0 : ℝ) ≤ (cH : ℝ) + (p : ℝ))
    linarith
  have hbase' : (1 + ((cH : ℝ) / 3 + (p : ℝ) * m) / ((cH : ℝ) + (p : ℝ))) ≠ 0 := hbase.ne'
  field_simp <;> ring

/-- **The bridge in `logPhi` form** (composing with 4c's local amplitude identity): the raw hub
    ratio converges to `exp (logPhi b) * rhoB^(Vb b)`. -/
theorem amplitude_bridge_logPhi (cH : ℕ) (arm b : Branch) :
    Tendsto (fun p : ℕ =>
        Ztot (litHub cH (List.replicate p arm ++ [b]))
          / Ztot (litHub cH (List.replicate p arm)))
      atTop (𝓝 (Real.exp (logPhi b) * rhoB ^ (Vb b))) := by
  have h := amplitude_bridge cH arm b
  rw [← Ztot_lit_eq_Wb b, ← exp_logPhi_mul_rhoB_pow b] at h
  exact h

end R3Cert
