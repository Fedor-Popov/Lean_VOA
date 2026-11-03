import VOA.DeligneAudit.SL4TDoubledSiteChainAudit
import VOA.DeligneAudit.SL4TDoubledSiteRank

/-!
Declaration inventory and collision audit for the doubled-site rank bound (no hypotheses).

The two boundary projections compose to the ring with two roots removed. Their kernel
is killed by the surviving pair's Thom coefficient modulo the preceding pair ideal.
These prefix ideals include the flag-tail ideal from the outset. The proved boundary
products therefore incorporate the vanished pairs without adding cells for them.

For a valid reduction, the inner mixed spanning chain is transported through the composite
projection with the shortened characteristic and power relations. For an invalid reduction,
the Thom coefficient already belongs to the preceding ideal and its cell list is empty.
The ordered concatenation is identified with the doubled-site catalog, then mapped through
the flag-tail quotient. The resulting filtration discharges the Levi rank reduction.

The endpoint holds for every number of sites at least two, with no remaining filtration
hypothesis. The five content files are inventoried below.

Axiom check: the main results use exactly [propext, Classical.choice, Quot.sound]; the
outputs for all declarations, including the smaller dependency sets of elementary helpers, are
below. No `sorry` is used. No mathematical input is open for the stated rank bound.
-/

-- SL4TDoubledSiteTransport.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mul_mem_of_principal_image
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairStates
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteReducedParams
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRemovedTop
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRemovedTop_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_surjective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFlagPolynomials_characteristic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_polynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_boundaries
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_first_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_kernel

-- SL4TDoubledSiteCatalog.lean
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairs_indexed
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_outer
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_middle
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteReducedParams_labels
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteReducedParams_first_valid
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairStates_level
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePrepend_fiber
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_levels

-- SL4TDoubledSiteFiltration.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_invalid_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_spanningChain
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.join_finRange
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSite_spanningChain_before_quotient
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSpanningFiltration

-- SL4TDoubledSiteRank.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_doubledSite_rank_le
