import VOA.DeligneAudit.SL4TRound112Audit
import VOA.DeligneAudit.SL4TMixedBlockTotal

/-!
# Mixed-site rings, cell filtration, and dimension audit

This leaf checks the mixed-site development together with the type-A audit it imports.
The maps run from the reduced ring onto the state quotient, and preserve the
characteristic polynomial after adjoining zero roots.

The quotient surjections, ideal chains, and truncation identities are proved.
The mixed spanning filtration peels b-sites first, then a-sites. Its cells record
double and triple counts, and have level equal to their sum and weight equal
to the double count plus twice the triple count. The ring-image bound derives
its nilpotence and characteristic hypotheses from the presentation. The word
catalog partitions into exactly the recursive block cells; its weighted total
is fifteen to the a-sites times six to the b-sites, including every valid block.

Every explicit declaration introduced in this module family is listed below.
Generated recursors, constructor declarations, and derived instances are omitted.
The comments record the actual axiom output. All principal quotient, filtration,
dimension, and counting theorems use exactly `[propext, Classical.choice, Quot.sound]`;
elementary helpers can use subsets.

The checked endpoint is the mixed ring-image bound and the total over all valid
parameter blocks. Applying these results to the actual sl4 Weyl-module
branching filtration, or to the D4 fusion capstone, is not done here.
-/

-- SL4TMixedStateQuotient.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateEvaluation_relation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateSurjection
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateSurjection_evaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedStateSurjection_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateEvaluation_boundary
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBState_relation_containment
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateEvaluation_relations
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_evaluation

-- SL4TMixedStateCharacteristic.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCharacteristic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.descendingPoly_remove_zero_root
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCharacteristic_state_evaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_characteristic_evaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_characteristic

-- SL4TMixedSeries.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_series
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabet_series_inverse
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_convolution
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_convolution
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedComplete_zero_of_empty
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedU_without_b_sites
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedV_without_b_sites
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirst_top_without_b_sites
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_top_without_b_sites

-- SL4TMixedASite.lean
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.MixedFirstChoice
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.MixedThirdChoice
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.MixedAState
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedANext
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedAZeroRoots
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAPair
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateIdeal
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedABoundary
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedANext_invalid_iff
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedANext_weight
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_boundary
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_first_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_third_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateEvaluation_relations
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_evaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAPair_one_of_invalid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAState_invalid

-- SL4TMixedACharacteristic.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAState_first_characteristic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAState_second_characteristic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_characteristic

-- SL4TMixedGrassmannian.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseIndex
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseSize
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseLength
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_valid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_elementary_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_complete_window
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_complete_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_corner_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedU_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedV_top

-- SL4TMixedIdealChain.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalIdealPrefix
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mem_principalIdealPrefix
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalIdealPrefix_mono
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalIdealPrefix_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalIdealPrefix_step
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.principalIdealPrefix_top_of_unit
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mul_pair_ideal_mem
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedBOrder
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBThom
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBChain
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBChain_mono
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBChain_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBChain_step
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBChain_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBThom_stateIdeal

-- SL4TMixedAChain.lean
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedAOrder
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAThom
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAChain
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_mono
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_step
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_top
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAThom_stateIdeal

-- SL4TMixedTruncationIdentity.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.characteristic_constant_power_decomposition
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.characteristic_constant_power_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCharacteristic_factors
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedTruncationIdeal
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedTopProduct_truncation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAThom_noRoot_truncation

-- SL4TMixedRelativeTail.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_relative_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedU_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedV_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_tail

-- SL4TMixedCharacteristicProduct.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_signed_coefficient_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedConv_characteristic_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedComplete_characteristic_sign
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementary_complement_convolution
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementary_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseChosenPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseComplementPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_characteristic_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstComplementPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondChosenPolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirst_relative_factorization
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_relative_factorization
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstAmbientComplement
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondAmbientComplement
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirst_ambient_factorization
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_ambient_factorization
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseChosenPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBaseComplementPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstComplementPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondChosenPolynomial_constant
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedFirstAmbientComplement_constant_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondAmbientComplement_constant_annihilated
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondAmbientComplement_constant_without_b

-- SL4TMixedThomTruncation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBThom_first_truncation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBThom_second_truncation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAThom_doubleRoot_truncation

-- SL4TMixedFlagMap.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.ideal_map_restrictScalars
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.ideal_map_linear_step
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.ideal_map_constant_polynomials
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.map_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_surjective_state
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_zero_state
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.join_range
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.polynomial_map_divX_of_zero_root
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.characteristic_divX_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_state_without_root
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_state_with_root

-- SL4TMixedStateFlag.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedTruncationIdeal_characteristic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedTruncationIdeal_power
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBState_flag
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAState_doubleRoot_lift
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedALevelShift
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedANext_sites
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAState_flag

-- SL4TMixedCellData.lean
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.MixedCellCounts
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevel
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedCellShift
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedADoubleCount
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedATripleCount
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedA_counts_level
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedA_counts_weight
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellShift_level
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellData
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellData_invalid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_invalid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_b_step
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_a_step

-- SL4TMixedCellFiltration.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRing_zero_algebraMap_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellFlag_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellFlag_recursive
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCell_spanningFiltration
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellData_weight

-- SL4TMixedPowerSum.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.coefficient_product_of_descending
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.coefficient_product_one_of_descending
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBase_series_units
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRelative_series_units
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_unit
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_zero
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedWeight_length
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_degree
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_newton
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_newton_tail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_nilpotent
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_descending

-- SL4TMixedCellBound.lean
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCellContribution
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCell_balanced_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCell_balanced_sum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRingImage_bound

-- SL4TMixedCellCatalog.lean
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedEmptyParams
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedAPrevious
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_previous
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious_next
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedANext_previous
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedAPrevious_next
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious_valid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAPrevious_valid
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedBPrepend
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedAPrepend
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_valid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_valid
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_flatMap
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_map
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_nil_of_invalid

-- SL4TMixedCellPartition.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedValid_zero_params
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_fiber
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_fiber
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRepresentedBlocks
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRepresentedBlocks_valid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_zero_of_unrepresented

-- SL4TMixedCellCount.lean
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCellContribution_shift
-- Axioms: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_flatMap
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_b_prepend
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_a_prepend
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_mass
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_mass
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_mass_sum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_total

-- SL4TMixedBlockTotal.lean
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.MixedBoundedIndices
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.mixedParamsOfIndices
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedValidBlocks
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mem_mixedValidBlocks
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_sum_all_valid
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedBlockRanks_sum_le
