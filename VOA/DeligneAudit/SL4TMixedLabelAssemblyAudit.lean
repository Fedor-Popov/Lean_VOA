import VOA.DeligneAudit.SL4TMixedLabelLevelTwoAudit
import VOA.DeligneAudit.SL4TMixedLabelRank

/-!
The mixed-label truncated sl₄ rank bound and its complete declaration inventory.

Theorem truncatedWeyl_sl4_mixed_rank_le proves, for every a b : ℕ,
FiniteDimensional ℂ (MixedLabelModule a b) and finrank at most 15 ^ a * 6 ^ b.
Theorem mixedLabelTruncatedRank proves the proposition MixedLabelTruncatedRank.
Both include zero labels. The final rank has no additional dimension or presentation hypothesis.

The mixedToRadicalRelative algebra homomorphism is surjective for every valid tuple.
Its ideal-containment proof checks the elementary tails, the three Grassmannian complete tails,
and both relative complete windows with their complementary-degree signs. The Grassmannian
model is unchanged. Its mixedPowerSum image is the last Cartan symbol. Composing with the
relative evaluator gives mixedSecondLeviEvaluation, surjective onto the actual
second multiplicity and equivariant for every positive last-Cartan mode.

The actual second multiplicities satisfy raising annihilation, the zero-mode weight, sharp
lowering nilpotence, and unsupported-count vanishing. Their last-root orbit obeys
mixedSecondLeviOrbit_bound. The other retained Cartan preserves that orbit, so it equals
the quotient image of the full second Levi closure. The two count filtrations are summed
without splitting mode degrees. Finite fibers and unsupported-count vanishing give the
supported finite sums, and mixedNestedBlockBound_sum_le compares them injectively with
mixedValidBlocks before applying mixedBlockBound_sum_all_valid.

The final proof works inside the already truncated universal module: current truncation
propagates from its generator and survives both Levi quotient actions. The local
Weyl bound supplies only finite-dimensionality. The reusable currentTruncationMap also
preserves surjectivity and right exactness, with currentTruncation_finrank_le for extensions.
The finite filtration assembly uses quotient-image dimension identities directly.

Scope: the mixed-label rank proposition is proved. The D4 bound is outside this module.

This audit imports the level-two audit and the final rank theorem. The 143 explicit
declarations, including definitions and auxiliary lemmas, are printed below, grouped by source
file; each output comment records the axiom list. Axiom check: all principal theorem outputs
are exactly [propext, Classical.choice, Quot.sound]; no nonstandard axiom occurs.
-/

-- SL4TNewtonSeries.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positivePowerSumSeries
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_congr_positive
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_derivative
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_unique
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_add
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_sub_mul
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_neg_of_inverse
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.specializedElementary_complete_inverse
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_elementary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_difference_alphabets

-- SL4TMixedElementarySource.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementary_symmetric
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_elementary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_complete
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricBase
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_elementary_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_complete_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_powerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementaryAlphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_alphabet

-- SL4TMixedRelativePresentation.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.complementaryDegree_sign
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAmbient_newtonCoeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedRelative_signedCoefficient
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_firstNewton
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_secondNewton
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_firstRelative
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_secondRelative

-- SL4TMixedSourceSurjective.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_powerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_generates
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_base_mem_range
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_surjective

-- SL4TMixedRelativeQuotient.lean
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelBlockParams
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_elementary_tail
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_ideal_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_mk
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_surjective

-- SL4TMixedCartanSymbols.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSignedSeries
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetPowerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSignedSeries_convolution
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSignedSeries_complete
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedAlphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_relativeAlphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedAmbient
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLastCartanPowerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedLastCartan
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLastCartan_newtonCoeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_eq_lastCartan

-- SL4TMixedRelativeEquivariance.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetPowerSum_specialization
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_abstractPowerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_alphabetPowerSum
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLastCartanPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLastCartanPolynomial_specialization
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_lastCartan
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_powerSum

-- SL4TMixedSecondLeviEvaluation.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelBlockParams_dominant
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_surjective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_cartan

-- SL4TCurrentTruncationExact.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.CurrentIntertwines
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentStable_comap
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentStable_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentSpan_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTailImages
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationSubmodule
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationSubmodule_map_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationSubmodule_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationMap
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationMap_surjective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncationMap_range_eq_ker
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentTruncation_finrank_le

-- SL4TSecondLeviCountSupport.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelativeComplete_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_zero_of_count_excess
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_eq_bot_of_unsupported

-- SL4TSecondLeviHighest.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_zero_of_no_compound
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_insert_simple
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_insert_compound
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raised_compound_to_simple
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_word_key
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_raising_maps_key
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_word_eq_currentWord
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondRadical_key_lowering_nilpotent

-- SL4TSecondLeviBlockRelations.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_raising
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_weight
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_nilpotent
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientRaising
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientLowering
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotient_currentRelations
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_raising
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_weight
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_lowering_sharp

-- SL4TMixedSecondLeviBlockBound.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviOrbit
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_weight
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_truncated
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviOrbit_bound

-- SL4TSecondLeviOrbitClosure.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentSpan_invariant_of_commutators
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviOrbit_otherCartan
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviClosure_map_eq_orbit

-- SL4TFiniteFiltrationRank.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.submodule_finrank_sup_eq
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.quotientImage_finrank_antitone
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.finiteFiltration_finrank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.finiteFiberFiltration_finrank_le

-- SL4TMixedSecondLeviFiltration.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.linearMap_natCast_mul
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelBlockParams_valid
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviMultiplicity_otherCartan
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviClosure_map_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountFiber
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherSecondLeviCountClosure_le_fiber
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviFiltration_rank_le

-- SL4TSecondLeviGeneration.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_on_radical
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_on_normal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_positive_inv
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_cyclic_eq_leviSpan

-- SL4TLeviCountGeneration.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_radicalWord_mem_count
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_allCountClosures_eq_spans
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLevi_allCountClosures_eq_cyclic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_word
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountClosure_map_eq_cyclic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountClosure_map_eq_secondCounts

-- SL4TRadicalCountFiltration.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountBox
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mem_radicalCountBox
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountFiber
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mem_radicalCountFiber
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.radicalCountPosition
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCounts_position
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSupportedCounts
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mem_radicalSupportedCounts
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_le_fiber
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountClosure_map_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.cyclic_eq_radicalCountClosures
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountFiltration_rank_le

-- SL4TMixedLabelRank.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedSecondSupportedCounts
-- Output: [propext]
#print axioms VOA.DeligneAudit.SL4T.mixedCountIndexParams
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCountIndexParams_injective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedCountIndexParams_mem_valid
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedNestedBlockBound_sum_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedCyclic_rank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_mixed_rank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank

