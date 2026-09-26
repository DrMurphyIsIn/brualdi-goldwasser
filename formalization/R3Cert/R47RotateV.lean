/-
  R4-R5 campaign, PHASE 5e (part 2): the Vee objective and root rotation along the
  backbone.

  `AobjV up h down` realizes the state rooted at hub `h`, with a DOWN backbone (the
  usual tail) and an UP backbone (the rest of the chain, as a further child block).
  The one-step rotation

      `AobjV up h (g :: down) = AobjV (h :: up) g down`

  moves the root across the h--g edge: both sides reduce by `Ztot_append_split`
  (R47Rotate) to the SAME symmetric expression
      `Zt(h-side) * Zt(g-side) + w * (Zo(h-side) * Zo(g-side))`,
  because the h-side component realized from the h-rooting has the same full degree
  as `dtSub (backboneU (h :: up))` (the +1 is the h--g edge either way) and the edge
  weight `1/(D_h * D_g)` is symmetric.  Iterating (`Aobj_eq_AobjV`) places the root
  at any hub of the backbone -- the re-rooting the interior-merge assembly needs.

  Nothing here asserts per-step monotonicity.  conjecture1_proved=False.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Rotate

namespace R3Cert
namespace Step3

open RTree

/-! ### The Vee objective -/

/-- The state objective rooted at hub `h`: arms, cherries, the DOWN backbone, and the
    UP backbone as a further child block (up-tail last). -/
noncomputable def AobjV (up : List Hub) (h : Hub) (down : List Hub) : ℝ :=
  Ztot (dtRealize (UTree.node
    (h.1.map armU ++ List.replicate h.2 cherryU ++ tailU down ++ tailU up)))

/-- With an empty up-chain the Vee objective is the standard rooted objective. -/
theorem AobjV_nil (h : Hub) (down : List Hub) :
    AobjV [] h down = Aobj (backboneU (h :: down)) := by
  obtain ⟨arms, c⟩ := h
  show Ztot (dtRealize (UTree.node
      (arms.map armU ++ List.replicate c cherryU ++ tailU down ++ tailU []))) = _
  rw [tailU_nil, List.append_nil, backboneU_eq]
  rfl

/-! ### The one-step rotation -/

/-- **Root rotation across one backbone edge**: the root moves from `h` to its down
    neighbour `g`; `h` joins `g`'s up-chain. -/
theorem AobjV_shift (up : List Hub) (h g : Hub) (down : List Hub) :
    AobjV up h (g :: down) = AobjV (h :: up) g down := by
  obtain ⟨aH, cH⟩ := h
  obtain ⟨aG, cG⟩ := g
  -- the two subtree components across the rotated edge
  set BH : UTree := backboneU ((aH, cH) :: up) with hBH
  set BG : UTree := backboneU ((aG, cG) :: down) with hBG
  -- LHS: root at h, children = armsH ++ cherries ++ [BG] ++ tailU up
  have hL : AobjV up (aH, cH) ((aG, cG) :: down)
      = Ztot (RTree.node (dtChildren (udeg BH)
          (aH.map armU ++ List.replicate cH cherryU ++ [BG] ++ tailU up))) := by
    show Ztot (dtRealize (UTree.node
        (aH.map armU ++ List.replicate cH cherryU ++ tailU ((aG, cG) :: down)
          ++ tailU up))) = _
    rw [tailU_cons, dtRealize_node]
    have hlen : (aH.map armU ++ List.replicate cH cherryU ++ [BG] ++ tailU up).length
        = udeg BH := by
      rw [hBH, udeg_backbone]
      simp [List.length_append]
      omega
    rw [← hBG, hlen]
  -- RHS: root at g, children = armsG ++ cherries ++ tailU down ++ [BH]
  have hR : AobjV ((aH, cH) :: up) (aG, cG) down
      = Ztot (RTree.node (dtChildren (udeg BG)
          (aG.map armU ++ List.replicate cG cherryU ++ tailU down ++ [BH]))) := by
    show Ztot (dtRealize (UTree.node
        (aG.map armU ++ List.replicate cG cherryU ++ tailU down
          ++ tailU ((aH, cH) :: up)))) = _
    rw [tailU_cons, dtRealize_node]
    have hlen : (aG.map armU ++ List.replicate cG cherryU ++ tailU down ++ [BH]).length
        = udeg BG := by
      rw [hBG, udeg_backbone]
      simp [List.length_append]
      omega
    rw [← hBH, hlen]
  rw [hL, hR]
  -- split both sides at the rotated edge
  have hsplitL : Ztot (RTree.node (dtChildren (udeg BH)
      (aH.map armU ++ List.replicate cH cherryU ++ [BG] ++ tailU up)))
      = Ztot (RTree.node (dtChildren (udeg BH)
          (aH.map armU ++ List.replicate cH cherryU ++ tailU up))) * Ztot (dtSub BG)
        + 1 / ((udeg BH : ℝ) * (udeg BG : ℝ))
          * (Zopen (RTree.node (dtChildren (udeg BH)
              (aH.map armU ++ List.replicate cH cherryU ++ tailU up))) * Zopen (dtSub BG)) := by
    rw [show aH.map armU ++ List.replicate cH cherryU ++ [BG] ++ tailU up
        = (aH.map armU ++ List.replicate cH cherryU) ++ (BG :: tailU up) from by simp,
      dtChildren_append, dtChildren_cons, Ztot_append_split]
    simp only [← dtChildren_append]
  have hsplitR : Ztot (RTree.node (dtChildren (udeg BG)
      (aG.map armU ++ List.replicate cG cherryU ++ tailU down ++ [BH])))
      = Ztot (RTree.node (dtChildren (udeg BG)
          (aG.map armU ++ List.replicate cG cherryU ++ tailU down))) * Ztot (dtSub BH)
        + 1 / ((udeg BG : ℝ) * (udeg BH : ℝ))
          * (Zopen (RTree.node (dtChildren (udeg BG)
              (aG.map armU ++ List.replicate cG cherryU ++ tailU down))) * Zopen (dtSub BH)) := by
    rw [dtChildren_append, dtChildren_cons, dtChildren_nil, Ztot_append_split]
    simp only [List.append_nil]
  rw [hsplitL, hsplitR]
  -- both sides now share the same four component terms: the h-side node at degree
  -- udeg BH IS dtSub BH, and the g-side node at degree udeg BG IS dtSub BG
  have hcompH : RTree.node (dtChildren (udeg BH)
      (aH.map armU ++ List.replicate cH cherryU ++ tailU up)) = dtSub BH := by
    have hlen : (aH.map armU ++ List.replicate cH cherryU ++ tailU up).length + 1
        = udeg BH := by
      rw [hBH, udeg_backbone]
      simp [List.length_append]
      omega
    rw [← hlen, hBH, backboneU_eq, dtSub_node]
  have hcompG : RTree.node (dtChildren (udeg BG)
      (aG.map armU ++ List.replicate cG cherryU ++ tailU down)) = dtSub BG := by
    have hlen : (aG.map armU ++ List.replicate cG cherryU ++ tailU down).length + 1
        = udeg BG := by
      rw [hBG, udeg_backbone]
      simp [List.length_append]
      omega
    rw [← hlen, hBG, backboneU_eq, dtSub_node]
  rw [hcompH, hcompG]
  ring

/-! ### Rooting anywhere along the backbone -/

/-- **The rotation identity**: the standard objective of the backbone
    `pre.reverse ++ h :: down` equals the Vee objective rooted at `h`. -/
theorem Aobj_eq_AobjV : ∀ (pre : List Hub) (h : Hub) (down : List Hub),
    Aobj (backboneU (List.reverseAux pre (h :: down))) = AobjV pre h down := by
  intro pre
  induction pre with
  | nil =>
    intro h down
    rw [List.reverseAux_nil, AobjV_nil]
  | cons p pre' ih =>
    intro h down
    rw [List.reverseAux_cons, ih p (h :: down), AobjV_shift]

end Step3
end R3Cert
