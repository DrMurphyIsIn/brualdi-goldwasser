/-
  Bridge STEP 3e (= STEP4C_DESIGN item (iii-a)): the ADDRESS GRAPH and the `IsEdgeEnum`
  master lemma.

  `BridgeStep3d.pi_eq_msum` needs a finite `SimpleGraph` and an `IsEdgeEnum` edge list.  The
  competitor trees live as ADDRESS edge lists (`BridgeStep3.realize`, `litHub`).  This file
  builds the generic glue:

  * `aGraph E` -- the finite graph of an address edge list, on the vertex-support subtype;
    adjacency `u ≠ v ∧ HasKey E u v` makes looplessness free;
  * `liftEdges E` -- the edge list lifted to the subtype vertices (via `attach`);
  * `isEdgeEnum_liftEdges` -- `IsEdgeEnum (aGraph E) (liftEdges E)` from four checkable
    hypotheses (`Nodup`, no loops, unordered-key uniqueness, degree-weights);
  * `msum_liftEdges` -- `msum (liftEdges E) = msum E` (relabeling vertices along any
    injection preserves the matching sum), connecting back to `Ztot_eq_msum`.

  What remains for the full item (iii) is (iii-b): discharging the four hypotheses for the
  `realize (litHub ...)` lists (address-suffix machinery + the degree computation).

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep3d

namespace R3Cert
namespace Step3

/-! ### The address graph -/

/-- Address-typed weighted edges (the `BridgeStep3.realize` output shape). -/
abbrev AEdge := List ℕ × List ℕ × ℝ

/-- The vertex support of an address edge list. -/
def vertsOf (E : List AEdge) : List (List ℕ) := E.map Prod.fst ++ E.map (fun e => e.2.1)

theorem fst_mem_vertsOf {E : List AEdge} {e : AEdge} (he : e ∈ E) :
    e.1 ∈ (vertsOf E).toFinset := by
  rw [List.mem_toFinset, vertsOf]
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩))

theorem snd_mem_vertsOf {E : List AEdge} {e : AEdge} (he : e ∈ E) :
    e.2.1 ∈ (vertsOf E).toFinset := by
  rw [List.mem_toFinset, vertsOf]
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨e, he, rfl⟩))

/-- `E` records the unordered pair `{a, b}` (in either orientation). -/
def HasKey (E : List AEdge) (a b : List ℕ) : Prop :=
  ∃ e ∈ E, (e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a)

theorem HasKey.symm {E : List AEdge} {a b : List ℕ} (h : HasKey E a b) : HasKey E b a := by
  obtain ⟨e, he, hor⟩ := h
  exact ⟨e, he, hor.symm⟩

/-- The vertex type: the finite support of `E`. -/
abbrev AVert (E : List AEdge) := {a : List ℕ // a ∈ (vertsOf E).toFinset}

/-- The address graph: adjacency = distinct + recorded key.  Looplessness is free. -/
instance hasKey_decidable (E : List AEdge) (a b : List ℕ) : Decidable (HasKey E a b) :=
  decidable_of_iff (∃ e ∈ E, (e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a)) Iff.rfl

def aGraph (E : List AEdge) : SimpleGraph (AVert E) where
  Adj u v := u ≠ v ∧ HasKey E u.val v.val
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

theorem aGraph_adj (E : List AEdge) (u v : AVert E) :
    (aGraph E).Adj u v ↔ u ≠ v ∧ HasKey E u.val v.val := Iff.rfl

instance aGraph_adjDecidable (E : List AEdge) : DecidableRel (aGraph E).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ HasKey E u.val v.val))

/-! ### Lifting the edge list to the subtype vertices -/

/-- The edge list on the support-subtype vertices. -/
def liftEdges (E : List AEdge) : List (AVert E × AVert E × ℝ) :=
  E.attach.map (fun x =>
    (⟨x.val.1, fst_mem_vertsOf x.property⟩, ⟨x.val.2.1, snd_mem_vertsOf x.property⟩,
      x.val.2.2))

theorem lift_mem {E : List AEdge} {e : AEdge} (he : e ∈ E) :
    (⟨e.1, fst_mem_vertsOf he⟩, ⟨e.2.1, snd_mem_vertsOf he⟩, e.2.2) ∈ liftEdges E := by
  rw [liftEdges, List.mem_map]
  exact ⟨⟨e, he⟩, List.mem_attach E ⟨e, he⟩, rfl⟩

theorem of_mem_liftEdges {E : List AEdge} {q : AVert E × AVert E × ℝ}
    (hq : q ∈ liftEdges E) :
    ∃ e ∈ E, q.1.val = e.1 ∧ q.2.1.val = e.2.1 ∧ q.2.2 = e.2.2 := by
  rw [liftEdges, List.mem_map] at hq
  obtain ⟨x, _, rfl⟩ := hq
  exact ⟨x.val, x.property, rfl, rfl, rfl⟩

/-! ### The `IsEdgeEnum` master lemma -/

/-- **The master lemma**: the lifted list is an `IsEdgeEnum` of the address graph, given the
    four checkable hypotheses on the raw list. -/
theorem isEdgeEnum_liftEdges (E : List AEdge)
    (hnodup : E.Nodup)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2.1)
    (hkeys : ∀ e ∈ E, ∀ f ∈ E,
      (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e)
    (hw : ∀ q ∈ liftEdges E, q.2.2
      = 1 / (((aGraph E).degree q.1 : ℝ) * ((aGraph E).degree q.2.1 : ℝ))) :
    IsEdgeEnum (aGraph E) (liftEdges E) := by
  have hnd : (liftEdges E).Nodup := by
    rw [liftEdges]
    refine List.Nodup.map ?_ (List.nodup_attach.mpr hnodup)
    intro x y hxy
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    have hval : x.val = y.val := Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
    exact Subtype.ext hval
  have hadj : ∀ q ∈ liftEdges E, (aGraph E).Adj q.1 q.2.1 := by
    intro q hq
    obtain ⟨e, he, h1, h2, _⟩ := of_mem_liftEdges hq
    rw [aGraph_adj]
    refine ⟨?_, ⟨e, he, Or.inl ⟨h1.symm, h2.symm⟩⟩⟩
    intro hcontra
    apply hloop e he
    rw [← h1, ← h2, hcontra]
  have hcomp : ∀ {u v : AVert E}, (aGraph E).Adj u v →
      ∃ q ∈ liftEdges E, (q.1 = u ∧ q.2.1 = v) ∨ (q.1 = v ∧ q.2.1 = u) := by
    intro u v huv
    rw [aGraph_adj] at huv
    obtain ⟨-, e, he, hor⟩ := huv
    refine ⟨(⟨e.1, fst_mem_vertsOf he⟩, ⟨e.2.1, snd_mem_vertsOf he⟩, e.2.2),
      lift_mem he, ?_⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
    · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
  have huniq : ∀ q ∈ liftEdges E, ∀ r ∈ liftEdges E,
      (r.1 = q.1 ∧ r.2.1 = q.2.1) ∨ (r.1 = q.2.1 ∧ r.2.1 = q.1) → r = q := by
    intro q hq r hr hor
    obtain ⟨e, he, hq1, hq2, hq3⟩ := of_mem_liftEdges hq
    obtain ⟨f, hf, hr1, hr2, hr3⟩ := of_mem_liftEdges hr
    have hef : f = e := by
      apply hkeys e he f hf
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [← hr1, ← hq1]; exact congrArg Subtype.val h1
        · rw [← hr2, ← hq2]; exact congrArg Subtype.val h2
      · refine Or.inr ⟨?_, ?_⟩
        · rw [← hr1, ← hq2]; exact congrArg Subtype.val h1
        · rw [← hr2, ← hq1]; exact congrArg Subtype.val h2
    have h1 : r.1 = q.1 := Subtype.ext (by rw [hr1, hq1, hef])
    have h2 : r.2.1 = q.2.1 := Subtype.ext (by rw [hr2, hq2, hef])
    have h3 : r.2.2 = q.2.2 := by rw [hr3, hq3, hef]
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
  exact { nodup := hnd, adj := hadj, weight := hw, complete := hcomp, unique := huniq }

/-! ### The matching sum is invariant under vertex relabeling -/

theorem conflict_map {V W : Type} [DecidableEq V] [DecidableEq W] {g : V → W}
    (hg : Function.Injective g) (u v : V) (f : V × V × ℝ) :
    conflict (g u) (g v) (g f.1, g f.2.1, f.2.2) = conflict u v f := by
  simp only [conflict, decide_eq_decide, hg.eq_iff]

/-- Relabeling the vertices of an edge list along an injection preserves `msum`. -/
theorem msum_map_inj {V W : Type} [DecidableEq V] [DecidableEq W] {g : V → W}
    (hg : Function.Injective g) :
    ∀ E : List (V × V × ℝ),
      msum (E.map (fun e => (g e.1, g e.2.1, e.2.2))) = msum E
  | [] => by simp
  | e :: rest => by
    have hfil : ∀ (l : List (V × V × ℝ)),
        (l.map (fun f => (g f.1, g f.2.1, f.2.2))).filter
            (fun f => ! conflict (g e.1) (g e.2.1) f)
          = (l.filter (fun f => ! conflict e.1 e.2.1 f)).map
              (fun f => (g f.1, g f.2.1, f.2.2)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih =>
        rw [List.map_cons, List.filter_cons, List.filter_cons]
        rw [conflict_map hg]
        by_cases hca : (! conflict e.1 e.2.1 a) = true
        · rw [if_pos hca, if_pos hca, List.map_cons, ih]
        · rw [if_neg hca, if_neg hca, ih]
    rw [List.map_cons, msum_cons, msum_cons, msum_map_inj hg rest]
    dsimp only
    rw [hfil rest, msum_map_inj hg (rest.filter (fun f => ! conflict e.1 e.2.1 f))]
termination_by E => E.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact le_trans (List.length_filter_le _ _) (by simp [List.length_attach])

/-- The value projection of the lifted list is the original list. -/
theorem liftEdges_map_val (E : List AEdge) :
    (liftEdges E).map (fun q : AVert E × AVert E × ℝ => (q.1.val, q.2.1.val, q.2.2)) = E := by
  rw [liftEdges, List.map_map]
  have hcomp : ((fun q : AVert E × AVert E × ℝ => (q.1.val, q.2.1.val, q.2.2)) ∘
      (fun x : {e // e ∈ E} =>
        ((⟨x.val.1, fst_mem_vertsOf x.property⟩ : AVert E),
          (⟨x.val.2.1, snd_mem_vertsOf x.property⟩ : AVert E), x.val.2.2)))
      = (Subtype.val : {e // e ∈ E} → AEdge) := by
    funext x
    rfl
  rw [hcomp, List.attach_map_subtype_val]

/-- **`msum` transfers through the lift**: the subtype relabeling is invisible to the
    matching sum. -/
theorem msum_liftEdges (E : List AEdge) : msum (liftEdges E) = msum E := by
  conv_rhs => rw [← liftEdges_map_val E]
  exact (msum_map_inj Subtype.val_injective (liftEdges E)).symm

end Step3
end R3Cert
