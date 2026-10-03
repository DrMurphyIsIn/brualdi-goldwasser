/-
  BGUnique.AxiomGuard -- every headline theorem of the uniqueness development depends only on (a subset of)
  the three standard axioms of Lean 4 + Mathlib (propext, Classical.choice, Quot.sound).
  Run after `lake build BGUnique`:  lake env lean BGUnique/AxiomGuard.lean
-/
import BGUnique.Mathlib
import BGUnique.MidUnique
import BGUnique.AllUniqueIso
import BGUnique.RerootIsoBridgeMain

-- Mathlib vocabulary on the hypothesis side: the maximizing trees, exactly, for every n ≥ 4 (one class; two classes at n = 21).
#print axioms R3Cert.BGUnique.bg_maximizers_mathlib
#print axioms R3Cert.BGUnique.bg_maximizer_unique_mathlib
#print axioms R3Cert.BGUnique.bg_maximizers_21_mathlib
-- Spiders: strict optimality and uniqueness of the winner, n ≥ 150 (exchange chain for n ≥ 492, kernel sweep below).
#print axioms R3Cert.SpiderStrict.spider_strict_large
#print axioms R3Cert.SpiderStrict.spider_unique_large
#print axioms R3Cert.SpiderStrict.spider_strict_mid
#print axioms R3Cert.SpiderStrict.maximizer_unique_large
#print axioms R3Cert.SpiderStrict.bg_maximizer_unique
-- Every n ≥ 4, up to rerooting: the exact characterization, with the tie at n = 21.
#print axioms R3Cert.AllUnique.bg_maximizers_exact
#print axioms R3Cert.AllUnique.bg_maximizer_unique_all
#print axioms R3Cert.AllUnique.bg_maximizers_21
#print axioms R3Cert.AllUnique.bgMax21_not_S21
#print axioms R3Cert.AllUnique.Aobj_S21
-- Rerooting is exactly isomorphism of unrooted trees.
#print axioms R3Cert.RerootEquiv.equivalence
#print axioms R3Cert.RerootIso.uiso_of_rerootRel
#print axioms R3Cert.RerootIso.rerootRel_of_uiso
#print axioms R3Cert.RerootIso.rerootRel_iff_uiso
#print axioms R3Cert.AllUniqueIso.uiso_equivalence
#print axioms R3Cert.AllUniqueIso.bg_maximizers_exact_iso
#print axioms R3Cert.AllUniqueIso.bg_maximizer_unique_all_iso
#print axioms R3Cert.AllUniqueIso.bg_maximizers_21_iso
#print axioms R3Cert.AllUniqueIso.bgMax21_not_uiso_S21
-- The address graph is a tree of the right size, and it is the graph behind the ratio.
#print axioms R3Cert.RerootIso.card_V
#print axioms R3Cert.RerootIso.fintype_card_V
#print axioms R3Cert.RerootIso.G_isTree
#print axioms R3Cert.RerootIso.G_iso_aGraph
#print axioms R3Cert.RerootIso.uiso_iff_aGraph
#print axioms R3Cert.AllUniqueIso.bgRatio_eq
#print axioms R3Cert.AllUniqueIso.bg_maximizers_exact_aGraph
