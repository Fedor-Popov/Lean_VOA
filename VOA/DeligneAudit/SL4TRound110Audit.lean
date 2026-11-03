import VOA.DeligneAudit.SL4TGrassmannianFinite
import VOA.DeligneAudit.SL4TGrassmannianAugmentation
import VOA.DeligneAudit.LeviTypeA2CertGradedFinal
import VOA.DeligneAudit.LeviTypeA3GradedInductionFinal

/-!
# Cell lemma and Grassmannian bounds: declaration inventory and combined axiom audit

This target imports both type-A chains to check compatibility in their combined environment.
The cell lemma is complete. The Grassmannian results include the finite presentation,
both boundary quotient equivalences, the boundary product, and the binomial upper bound.
Not proved here: the binomial lower bound (a rectangle-basis independence proof).
The exact annihilator equalities and the ideal-module isomorphisms are not asserted.
K1 is not stated here, since it presupposes a complete part (b).

Each group below names its source file and audits every explicit declaration in that file.
-/

-- SL4TBalanced.lean
#print axioms VOA.DeligneAudit.SL4T.bal_prod_two
#print axioms VOA.DeligneAudit.SL4T.bal_prod_of_weight_le

-- SL4TCell.lean
#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound
#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound_two

-- SL4TCellBasic.lean
#print axioms VOA.DeligneAudit.SL4T.CurrentStable
#print axioms VOA.DeligneAudit.SL4T.currentSpan
#print axioms VOA.DeligneAudit.SL4T.subset_currentSpan
#print axioms VOA.DeligneAudit.SL4T.currentSpan_stable
#print axioms VOA.DeligneAudit.SL4T.currentSpan_le
#print axioms VOA.DeligneAudit.SL4T.currentSpan_mono
#print axioms VOA.DeligneAudit.SL4T.currentSpan_empty
#print axioms VOA.DeligneAudit.SL4T.cellFlag
#print axioms VOA.DeligneAudit.SL4T.cellFlag_stable
#print axioms VOA.DeligneAudit.SL4T.cellFlag_zero
#print axioms VOA.DeligneAudit.SL4T.cellFlag_mono
#print axioms VOA.DeligneAudit.SL4T.cellFlag_mem
#print axioms VOA.DeligneAudit.SL4T.cellFlag_le_iff
#print axioms VOA.DeligneAudit.SL4T.Fspan_le_of_stable
#print axioms VOA.DeligneAudit.SL4T.CellRelations

-- SL4TCellQuotient.lean
#print axioms VOA.DeligneAudit.SL4T.cellFlag_step_bound

-- SL4TFiniteExtension.lean
#print axioms VOA.DeligneAudit.SL4T.finite_of_annihilating_pair

-- SL4TGrassmannian.lean
#print axioms VOA.DeligneAudit.SL4T.SymPoly
#print axioms VOA.DeligneAudit.SL4T.elementary
#print axioms VOA.DeligneAudit.SL4T.complete
#print axioms VOA.DeligneAudit.SL4T.elementary_zero
#print axioms VOA.DeligneAudit.SL4T.elementary_succ
#print axioms VOA.DeligneAudit.SL4T.complete_zero
#print axioms VOA.DeligneAudit.SL4T.complete_succ
#print axioms VOA.DeligneAudit.SL4T.complete_relation
#print axioms VOA.DeligneAudit.SL4T.tailIdeal
#print axioms VOA.DeligneAudit.SL4T.tailIdeal_le_iff
#print axioms VOA.DeligneAudit.SL4T.mem_tailIdeal
#print axioms VOA.DeligneAudit.SL4T.tailIdeal_mono
#print axioms VOA.DeligneAudit.SL4T.tailIdeal_succ
#print axioms VOA.DeligneAudit.SL4T.grassIdeal
#print axioms VOA.DeligneAudit.SL4T.GrassRing
#print axioms VOA.DeligneAudit.SL4T.H
#print axioms VOA.DeligneAudit.SL4T.eClass
#print axioms VOA.DeligneAudit.SL4T.hClass
#print axioms VOA.DeligneAudit.SL4T.eClass_eq_zero
#print axioms VOA.DeligneAudit.SL4T.hClass_eq_zero
#print axioms VOA.DeligneAudit.SL4T.grassIdeal_peel_e
#print axioms VOA.DeligneAudit.SL4T.grassIdeal_peel_h
#print axioms VOA.DeligneAudit.SL4T.grassIdeal_finite

-- SL4TGrassmannianBoundary.lean
#print axioms VOA.DeligneAudit.SL4T.grassQuotE
#print axioms VOA.DeligneAudit.SL4T.grassQuotH
#print axioms VOA.DeligneAudit.SL4T.grassRingCongr
#print axioms VOA.DeligneAudit.SL4T.H_quot_e
#print axioms VOA.DeligneAudit.SL4T.H_quot_h
#print axioms VOA.DeligneAudit.SL4T.grass_boundary_product

-- SL4TGrassmannianFinite.lean
#print axioms VOA.DeligneAudit.SL4T.grass_convolution
#print axioms VOA.DeligneAudit.SL4T.eClass_width_zero
#print axioms VOA.DeligneAudit.SL4T.grass_finite_of_e_zero
#print axioms VOA.DeligneAudit.SL4T.grass_finite_rank_le
#print axioms VOA.DeligneAudit.SL4T.H_finite_rank_le

-- SL4TGrassmannianAugmentation.lean
#print axioms VOA.DeligneAudit.SL4T.symAugmentation
#print axioms VOA.DeligneAudit.SL4T.symAugmentation_elementary
#print axioms VOA.DeligneAudit.SL4T.symAugmentation_complete
#print axioms VOA.DeligneAudit.SL4T.grassIdeal_le_ker_augmentation
#print axioms VOA.DeligneAudit.SL4T.grassAugmentation
#print axioms VOA.DeligneAudit.SL4T.grass_nontrivial
