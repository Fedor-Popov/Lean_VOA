import VOA.Examples
import VOA.ArakawaDai

/-! Classical-freeness campaign (2026-10-25): boundary affine L_{-2+2/q}(sl2), Virasoro
M(2,2m+3), and the reusable jet/Li/C2 interfaces.  Every declaration must report exactly
[propext, Classical.choice, Quot.sound]. -/

#print axioms VOA.AffineSl2BoundaryClassicalFreeness.canonicalMap_bijective
#print axioms VOA.AffineSl2BoundaryClassicalFreeness.boundary_classically_free
#print axioms VOA.AffineSl2BoundaryClassicalFreeness.arcPoissonEquiv
#print axioms VOA.AffineSl2BoundaryClassicalFreeness.arcPoissonEquiv_conformal_iff
#print axioms VOA.AffineSl2BoundaryClassicalFreeness.baseC2AlgEquiv
#print axioms VOA.AffineSl2BoundaryClassicalFreeness.actualC2ArcEquiv
#print axioms VOA.AffineSl2BoundaryCharacter.character_eq_product
#print axioms VOA.TwoSeries.DSSlice.virSymbol_twoSeries
#print axioms VOA.VirasoroClassicalFreeness.classicallyFree
#print axioms VOA.VirasoroClassicalFreeness.canonicalEquiv
#print axioms VOA.VirasoroClassicalFreeness.baseC2AlgEquiv
#print axioms VOA.VirasoroClassicalFreeness.actualC2ArcEquiv
#print axioms VOA.VirasoroClassicalFreeness.jetMap_translation
#print axioms VOA.VirasoroClassicalFreeness.jetMap_injective
#print axioms VOA.VirasoroClassicalFreeness.jetMap_surjective
#print axioms VOA.VirasoroClassicalFreeness.mk₂_omegaBar_pow_eq_zero
#print axioms VOA.VirasoroClassicalFreeness.mem_jetIdeal_of_psi_eq_zero
#print axioms VOA.VirasoroClassicalFreeness.cm_eq
#print axioms VOA.VirasoroLi.liFiltration_eq_virWordPiece
#print axioms VOA.VirasoroLi.simpleLiFiltration_eq_virWordPiece
#print axioms VOA.liFiltration_eq_genWordPiece
#print axioms VOA.liInfinitePresentedJetMap_surjective_of_genWordSpan
#print axioms VOA.liPresentedJetBidegreeMap_surjective_of_genWordSpan
#print axioms VOA.liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze_of_surjective
#print axioms VOA.baseC2AlgEquiv_of_arc_injective
#print axioms VOA.AffineVOA.CurrentLi.quotientLiFiltration_eq_map
#print axioms VOA.InfiniteJet.arcEquiv
#print axioms VOA.InfiniteJet.jetIdeal_span_eq_coefficientIdeal
#print axioms VOA.liFiltration_one_eq_O₂
#print axioms VOA.VirasoroClassicalFreeness.cm_zero
#print axioms VOA.VirasoroClassicalFreeness.cm_one
#print axioms VOA.VirasoroClassicalFreeness.classicallyFree_M23
#print axioms VOA.VirasoroClassicalFreeness.classicallyFree_leeYang
#print axioms VOA.VirasoroClassicalFreeness.arcPoissonEquiv
#print axioms VOA.VirasoroClassicalFreeness.arcLiPoissonHom
#print axioms VOA.VirasoroClassicalFreeness.liPoissonVertexAlgebra_mode_eq_zero
#print axioms VOA.VirasoroClassicalFreeness.mode_x_x
#print axioms VOA.zeroPVA
