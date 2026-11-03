import VOA.DeligneAudit.SL4TDoubledSiteAudit
import VOA.DeligneAudit.SL4TDoubledSiteVanishing
import VOA.DeligneAudit.SL4TMixedBoundaryProjection
import VOA.DeligneAudit.SL4TCompositeThomChain
import VOA.DeligneAudit.SL4TMiddleFlagPeel
import VOA.DeligneAudit.SL4TDoubledSitePairTruncation

/-!
Collision audit and complete declaration inventory for the doubled-site chain algebra.

Verified algebra for all valid blocks with zero outer labels and at least two middle sites:
* Principal four-block boundary ideals and exact, surjective reduced-ring projections.
* Forward and reverse site chains; composition of their Thom ideal families.
* The last-mode power-sum identity in the actual mixed ring, including empty blocks.
* Vanishing of every wrong-order composite Thom coefficient and all its multiples.
* Characteristic lifts after one or two removals, including repeated removals.
* Boundary control for all ten surviving pairs, and both shortened polynomial relations.
  `doubledSitePair_polynomialRelations` specializes these relations to the actual mixed ring.

**Not proved here:** `DoubledSiteSpanningFiltration B q`. Consequently
`truncatedWeyl_sl4_doubledSite_rank_le` is not declared here, and
`truncatedWeyl_sl4_doubledSite_rank_le_of_flags` remains conditional on the same flag input.

The remaining assembly, given the algebraic inputs above:
1. For each surviving pair, compose `mixedBProjection` twice. Use
   `middleFlag_stateIdeal_constant`, `middleFlagTwiceRemovedPolynomial_map`, and
   `doubledPairTop_boundaries` to control the composite kernel modulo `doubledPairPrefix`.
   Treat invalid first or second reductions as empty pieces, using the existing
   `mixedBStateIdeal_eq_top_of_invalid` and `mixedCellData_invalid`.
2. Transport `mixedCellFlag_recursive` on the remaining sites through
   `SpanningChain.thom_of_generators`, using `doubledSitePair_polynomialRelations`.
   Join the ten pieces, then map the chain through the tail quotient. The pair prefix
   starts at the tail ideal and ends at the full ring.
3. Identify the ordered concatenation with the levels of `mixedCatalogFiber q
   (doubledSiteCellCatalog (B - 2))`, using `mixedCatalogFiber_map` and
   `mixedCellCatalog_fiber`, and apply the conditional universal endpoint.

Conventions: `doubledSiteFlagIndex` is the permutation [0, 2, 1, 3] of original flag
indices. Signed characteristic constants and linear coefficients are used for the
composite coefficients; the last-mode identity then has no additional sign factor.
The ten pairs are in the same outer-forward, inner-reverse order as `doubledSitePairs`.
No finite-site instance is used in place of the general statement.

Axiom check: every main theorem depends exactly on `[propext, Classical.choice, Quot.sound]`.
The precise outputs, including smaller dependency sets for helper definitions, accompany the
complete inventory below.
-/

-- SL4TMiddleFlagBoundary.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTop
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_outer_lengths
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_first_top_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_second_top_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_top_product_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_stateIdeal
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteOuterOrder
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteInnerOrder
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteOuterThom
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteInnerThom
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteOuterChain
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteInnerChain
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalBoundary_mul_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteOuterThom_boundary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteInnerThom_boundary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteChains_endpoints

-- SL4TComplementPowerSum.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.powerSumSeries_eq_derivative_complement
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_eq_derivative_complement
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.coefficientEuler_degree
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.coefficientEuler_top
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_last_mode
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.coefficient_prod_sum_degrees

-- SL4TMiddleFlagPowerSum.lean
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.middleFlagLength
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagElementary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagLength_sum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagElementary_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetPowerSum_empty
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_newtonCoeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_series
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagComplementCoefficientPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_complement
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_last_mode

-- SL4TMixedBoundaryProjection.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_old_relations
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_evaluation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_surjective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_boundary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBProjection_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagProjection_kernel

-- SL4TCompositeThomChain.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_composite_step
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom_composite

-- SL4TMiddleFlagPeel.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.reflect_prod_sum_degrees
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagPolynomial_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagPolynomial_constant
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlag_stateIdeal_constant
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagLength_next
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagPolynomial_map_projection
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_map_divX
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagRemovedPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagRemovedPolynomial_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTwiceRemovedPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTwiceRemovedPolynomial_map

-- SL4TDoubledSiteVanishing.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.product_except_eq_ite
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.orderedPairThom
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.orderedPairThom_wrong_order
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.orderedPairThom_surviving
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFlagIndex
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSignedTop
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSignedLinear
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteThomClass
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSignedLinear_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteThomClass_wrong_order_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteThomClass_wrong_order_zero

-- SL4TDoubledSitePairRelations.lean
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairIndices
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairTop
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairPrefix
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairTop_boundaries
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairPolynomial
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledPairLevelShift

-- SL4TDoubledSitePairTruncation.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairPolynomial_relation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledPairPower_relation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFlagPolynomials
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_polynomialRelations
