/-
  The two Jensen inputs for the multi-child sweep, constructed CONCRETELY (roadmap item 3).

  `node_jensen_reduction` (Jensen.lean) collapses the multi-child DEC node to the all-equal node, but it takes
  its two premises ABSTRACTLY: a concave hull `H` (`ConcaveOn ℝ I H`) and the induction hypothesis that every
  child amplitude lies below the hull (`∀ i, ell i ≤ H (mu i)`).  This file DISCHARGES both for the actual hull.

  KEY OBSERVATION.  The upper concave envelope of the amplitude menu is a CONCAVE piecewise-linear function, and
  a concave PL function is exactly the pointwise MINIMUM of the affine extensions of its segments.  In this
  "inf of affines" representation the two premises are immediate and need no numerics:

    (1) CONCAVITY (the Jensen premise).  A min of affine functions is concave -- `ConcaveOn.inf` folded over the
        segments.  No slope-monotonicity check is needed: the representation is concave BY CONSTRUCTION.  This
        replaces `adversary_sweep.hull_is_concave` (the a-posteriori decreasing-slopes check) with a proof.

    (2) DOMINATION (the induction hypothesis).  A menu point `(mu, ell)` lies below the hull iff it lies below
        EVERY segment line, so `ell ≤ H mu` reduces to the finite set of affine inequalities `ell ≤ a_k + b_k mu`
        -- exactly the a-posteriori `_hull_dominates` check of gap_interval_certification.py, now a proof.

  Both are machine-checked here with no `sorry`; the capstone `node_jensen_reduction_hull` feeds them into the
  Jensen reduction, so the multi-child node bound holds with the two premises fully constructed, parameterized
  only by the per-child affine domination inequalities (the concrete data the sweep actually verifies).
-/
import Mathlib
import R3Cert.Jensen

namespace R3Cert

open Real

/-- A single affine segment line `x ↦ a + b x`, given its `(a, b)` coefficients. -/
noncomputable def affineFn (ab : ℝ × ℝ) : ℝ → ℝ := fun x => ab.1 + ab.2 * x

/-- **Affine functions are concave** (on all of `ℝ`).  The linear part `x ↦ b x` is `b • id` (a linear map,
    hence concave by `LinearMap.concaveOn`), and `add_const` adds the intercept. -/
theorem affine_concaveOn (ab : ℝ × ℝ) : ConcaveOn ℝ Set.univ (affineFn ab) := by
  have hlin : ConcaveOn ℝ Set.univ (fun x : ℝ => (ab.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x) :=
    (ab.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).concaveOn convex_univ
  have h2 := hlin.add_const ab.1
  have heq : ((fun x => (ab.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x) + fun _ => ab.1) = affineFn ab := by
    funext x
    simp only [Pi.add_apply, affineFn, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul]
    ring
  rwa [heq] at h2

/-- The hull as the pointwise minimum of the affine extensions of its segments (a nonempty family: an explicit
    `seed` segment plus a list `segs` of the rest). -/
noncomputable def hullOf (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) : ℝ → ℝ :=
  fun x => segs.foldr (fun ab acc => min (affineFn ab x) acc) (affineFn seed x)

@[simp] theorem hullOf_nil (seed : ℝ × ℝ) : hullOf [] seed = affineFn seed := rfl

@[simp] theorem hullOf_cons (ab : ℝ × ℝ) (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) (x : ℝ) :
    hullOf (ab :: segs) seed x = min (affineFn ab x) (hullOf segs seed x) := rfl

/-- **(1) Hull concavity -- the Jensen premise, constructed.**  A min of affine functions is concave, proved by
    induction over the segment list via `ConcaveOn.inf`. -/
theorem hullOf_concave (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) :
    ConcaveOn ℝ Set.univ (hullOf segs seed) := by
  induction segs with
  | nil => simpa using affine_concaveOn seed
  | cons ab rest ih =>
      have h := (affine_concaveOn ab).inf ih
      have heq : (affineFn ab ⊓ hullOf rest seed) = hullOf (ab :: rest) seed := by
        funext x; rw [Pi.inf_apply, hullOf_cons]
      rwa [heq] at h

/-- **(2) Hull domination -- the induction hypothesis, constructed.**  If a point `(mu, ell)` lies weakly below
    every segment line (`ell ≤ affineFn ab mu` for the seed and each segment), it lies below the hull. -/
theorem hullOf_dominates (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) (ell mu : ℝ)
    (hseed : ell ≤ affineFn seed mu) (hsegs : ∀ ab ∈ segs, ell ≤ affineFn ab mu) :
    ell ≤ hullOf segs seed mu := by
  induction segs with
  | nil => simpa using hseed
  | cons ab rest ih =>
      rw [hullOf_cons]
      exact le_min (hsegs ab (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun a ha => hsegs a (List.mem_cons.mpr (Or.inr ha))))

/-- **The hull is `<=` its seed line everywhere.**  `hullOf` is a `foldr min` with base `affineFn seed`, so it
    is at most that base.  With a `seed = (0,0)` (the zero line) this gives `hullOf segs (0,0) <= 0` -- the
    upper cap of a menu whose amplitudes are all `<= 0`. -/
theorem hullOf_le_seed (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) (x : ℝ) :
    hullOf segs seed x ≤ affineFn seed x := by
  induction segs with
  | nil => simp
  | cons ab rest ih => rw [hullOf_cons]; exact le_trans (min_le_right _ _) ih

/-- **The hull is `<=` each of its segment lines.**  `hullOf` is an inf of affines, so it lies below every one
    of them -- used to give a per-cell UPPER bound on the hull (its active tangent line at a cell endpoint). -/
theorem hullOf_le_of_mem (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ) (ab : ℝ × ℝ) (x : ℝ)
    (hab : ab ∈ segs) : hullOf segs seed x ≤ affineFn ab x := by
  induction segs with
  | nil => simp at hab
  | cons a rest ih =>
      rw [hullOf_cons]
      rcases List.mem_cons.mp hab with h | h
      · subst h; exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

/-- **An affine function over an interval is bounded by the max of its endpoint values.**  On `[ml, mr]` the
    line `x ↦ a + b x` is monotone (sign of `b`), so its sup is at an endpoint.  This lifts a per-segment tangent
    bound from cell endpoints to the WHOLE cell -- the ingredient that turns the pointwise `hullOf_le_of_mem`
    into an interval (`∀ m ∈ cell`) hull bound, so a finite cavity grid tiles the continuum of mean-cavities. -/
theorem affineFn_le_max_endpoints (ab : ℝ × ℝ) (ml mr m : ℝ) (h1 : ml ≤ m) (h2 : m ≤ mr) :
    affineFn ab m ≤ max (affineFn ab ml) (affineFn ab mr) := by
  rcases le_total (0 : ℝ) ab.2 with hb | hb
  · have hp : (0 : ℝ) ≤ (mr - m) * ab.2 := mul_nonneg (by linarith) hb
    have : affineFn ab m ≤ affineFn ab mr := by simp only [affineFn]; nlinarith [hp]
    exact le_trans this (le_max_right _ _)
  · have hp : (0 : ℝ) ≤ (m - ml) * (-ab.2) := mul_nonneg (by linarith) (by linarith)
    have : affineFn ab m ≤ affineFn ab ml := by simp only [affineFn]; nlinarith [hp]
    exact le_trans this (le_max_left _ _)

/-- **The hull is `<=` a chosen segment's endpoint-max over the whole cell.**  Combines `hullOf_le_of_mem`
    (hull below every segment line) with `affineFn_le_max_endpoints` (the line below its endpoint max on the
    cell): for `ab ∈ segs` and `m ∈ [ml, mr]`, `hullOf segs seed m ≤ max (affineFn ab ml) (affineFn ab mr)`.
    The right side is a RATIONAL constant (the active tangent evaluated at the two rational cell endpoints) --
    the per-cell `hub` the grid supplies. -/
theorem hullOf_le_max_endpoints (segs : List (ℝ × ℝ)) (seed ab : ℝ × ℝ) (ml mr m : ℝ)
    (hab : ab ∈ segs) (h1 : ml ≤ m) (h2 : m ≤ mr) :
    hullOf segs seed m ≤ max (affineFn ab ml) (affineFn ab mr) :=
  le_trans (hullOf_le_of_mem segs seed ab m hab) (affineFn_le_max_endpoints ab ml mr m h1 h2)

/-- **Capstone: the multi-child node bound with BOTH Jensen premises constructed.**  Instantiating
    `node_jensen_reduction` with the concrete inf-of-affines hull `H = hullOf segs seed`.  The only remaining
    hypotheses are the per-child affine domination inequalities (`hdom`) -- the exact a-posteriori data the sweep
    verifies -- and `j > 0`.  Concavity (Jensen premise) and menu-domination (IH) are now theorems, not inputs. -/
theorem node_jensen_reduction_hull {s j : ℕ} (hj : 0 < j) (segs : List (ℝ × ℝ)) (seed : ℝ × ℝ)
    (ell mu : Fin j → ℝ)
    (hdom : ∀ i, ell i ≤ affineFn seed (mu i) ∧ ∀ ab ∈ segs, ell i ≤ affineFn ab (mu i)) :
    nodeAmp s j ell mu ≤ Qeq s j (hullOf segs seed) ((∑ i, mu i) / j) :=
  node_jensen_reduction hj (hullOf_concave segs seed) ell mu (fun _ => Set.mem_univ _)
    (fun i => hullOf_dominates segs seed (ell i) (mu i) (hdom i).1 (hdom i).2)

/-- A concrete demonstration: a 3-segment hull (seed `(-1, 0)` plus segments with slopes `-2` and `+1`) and a
    2-child node `(0, 2)` whose children sit below all three lines.  Everything discharges by `norm_num` --
    the whole Jensen setup (concavity + domination + reduction) is executable on explicit data. -/
example :
    nodeAmp 0 2 (fun _ : Fin 2 => (-2 : ℝ)) (fun _ : Fin 2 => (1 / 3 : ℝ))
      ≤ Qeq 0 2 (hullOf [(-1, -2), (-4/3, 1)] (-1, 0)) ((∑ _i : Fin 2, (1/3 : ℝ)) / 2) :=
  node_jensen_reduction_hull (by norm_num) [(-1, -2), (-4/3, 1)] (-1, 0) _ _
    (fun _ => ⟨by norm_num [affineFn], by
      intro ab hab; fin_cases hab <;> norm_num [affineFn]⟩)

end R3Cert
