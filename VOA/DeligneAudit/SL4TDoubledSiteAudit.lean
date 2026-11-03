import VOA.DeligneAudit.SL4TMixedLabelAssemblyAudit
import VOA.DeligneAudit.D4LevelBoundsAdjointAudit
import VOA.DeligneAudit.SL4TDoubledSiteRankReduction
import VOA.DeligneAudit.SL4TDoubledSitePolynomial

/-!
Collision audit and declaration inventory for the doubled-site middle-weight bound.

**Not proved here:** the universal rank bound without hypotheses. The endpoint is
`truncatedWeyl_sl4_doubledSite_rank_le_of_flags`, whose remaining hypothesis is exactly:
for every valid block at zero outer labels and B middle sites,
`DoubledSiteSpanningFiltration B q`. The desired range is every B at least two.

Proved ingredients:
* Independent-cutoff universal modules, finiteness, and high-current vanishing.
* Annihilation of all multiples of high alphabet power sums in the actual Levi evaluator.
* Surjective descent through the ideal of the four flag-block tail symbols.
* The all-site balanced count, including its partition by all valid mixed blocks.
* Polynomial identities for no retained root, one retained root, two distinct retained
  roots, and two retained roots in the same characteristic factor.
* Garland and the cell theorem after an arbitrary killed coefficient ideal and at an
  independent cutoff. Both Levi filtrations and the universal-module assembly consume
  the remaining flag hypothesis explicitly.

Open: the shortened-cutoff quotient spanning chain. In particular,
this needs the four-block presentation and its boundary quotients, the derivative
power-sum identity which kills the wrong-order pairs, and the composition of the outer and
reversed inner Thom chains with the mixed chain on the remaining sites. The supplied
polynomial identities handle the surviving-pair relation once those chains are built.
No existence theorem for these quotient flags is asserted in this audit.

Implementation choice: a linear evaluation kernel need not be an ideal. The ideal
`evaluationAnnihilator` records annihilation after every multiplier. The actual source
proof uses high positional modes and base coefficients before descending through either
quotient, and therefore does not assume the ideal property of a linear kernel.

Axiom check: all principal theorems depend exactly on `[propext, Classical.choice, Quot.sound]`.
The actual dependency lists for all explicit declarations follow, grouped by their files.
-/

-- SL4TTruncatedMiddleModule.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.TruncatedLabelModule
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_finite_and_local_bound
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_current_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedLabelModule_rank_iff_cyclic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.DoubledSiteModule
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientCartan_truncated

-- SL4TTruncatedCartanKernel.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.evaluationAnnihilator
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.evaluationAnnihilator_le_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.threeCartan_symbols_annihilate
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fourBlockPowerSumIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fourBlockPowerSumIdeal_le_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.multiplicityQuotientEvaluation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.multiplicityQuotientEvaluation_range
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.multiplicityQuotientEvaluation_surjective

-- SL4TTruncatedMultiplicity.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeProduct_zero_of_cutoff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_variable_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_base_relation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_powerSum_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_truncated
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_powerSum_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementaryAlphabet_evaluation_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_alphabetPowerSum_tail

-- SL4TTruncatedMultiplicityQuotient.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetTailIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_sum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetTailIdeal_le_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailIdeal_le_kernel
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagQuotientEvaluation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagQuotientEvaluation_surjective

-- SL4TDoubledSiteCount.lean
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairs
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRootCount
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledSiteDoubleCount
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledSiteTripleCount
-- Output: []
#print axioms VOA.DeligneAudit.SL4T.doubledSitePrepend
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSite_counts
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_doubledSitePrepend
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_mass
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_valid
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_count_weight
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSitePrepend_weight
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.balancedProduct_cellContribution
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_balanced
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSite_balanced_sum
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteBlockBound
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteBlockBound_sum_all_valid

-- SL4TDoubledSitePolynomial.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.characteristic_complement_shortened
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_distinct_removals
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_distinct_removals_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_equal_removals
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_equal_removals_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_no_retained_removal_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_one_retained_removal_mem

-- SL4TDoubledSiteRingImage.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedQuotientRingImage_bound_of_chain
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFiber_balanced_sum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.DoubledSiteSpanningFiltration
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRingImage_bound_of_chain

-- SL4TDoubledSiteOrbit.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSecondLeviOrbit_bound_of_chain

-- SL4TDoubledSiteRankReduction.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviFiltration_rank_le_of_orbit_bounds
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteNestedBlockBound_sum_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCyclic_rank_le_of_flags
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_doubledSite_rank_le_of_flags

