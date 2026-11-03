import VOA.DeligneAudit.SL4TMixedLabelBoundAudit
import VOA.DeligneAudit.SL4TRadicalCountSupport

/-!
The first Levi multiplicity evaluator, Cartan equivariance, and count support.

The labelled-mode evaluator has exactly the merged radical count layer as its range.
Independent permutation averaging gives a surjective evaluator from separately symmetric
mode polynomials onto the actual multiplicity space. Positive alphabet Cartan currents
intertwine multiplication by positional power sums. These power sums generate the separately
symmetric source and preserve every evaluated relation.

The adjacent-letter conversions absorb their errors at strictly greater Levi height and the
same radical depth, without quotienting out any mode degrees. Garland and these conversions
give the three complete-function source relations. Unsupported count multiplicities vanish
for all dominant labels, by propagating the zero-mode relation through the symmetric source.

Not proved here: Grassmannian descent. The source coefficient relations are not
identified with the images of the elementary-generator presentation's complete polynomials,
and the tensor product of its three Grassmannian quotients is not mapped to the actual
multiplicity space. `RadicalGrassmannianPresentation` is not proved. The second Levi
surjection and the assembly of `MixedLabelTruncatedRank` are also not proved here.

Each output comment below records the printed axiom list; an empty list means that the
declaration uses no axioms. Every declaration introduced by these extension modules is listed
below.
-/

-- SL4TRadicalConversionRelations.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountSpan_le_higher
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalConversionCounts
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_lower_summand
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_lower_term
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalConversion_zero_modes

-- SL4TRadicalModeEvaluation.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalModeSlot
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalModePolynomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_mem
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.modeList_of_length
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_range
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_surjective

-- SL4TRadicalSymmetricEvaluation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalColourProduct_perm
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSlotPermutation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_permute
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_rename
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricModes
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_orbitSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_symmetric_representative
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricMultiplicityEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricMultiplicityEvaluation_surjective

-- SL4TRadicalModePowerSums.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPositionModes
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPositionWord
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPowerSumWord_positions
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSlotColour
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSlotList
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSlotList_nodup
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalOperatorWord_eq_product
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeWord_eq_positionWord
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModePowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_powerSum_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_powerSum

-- SL4TRadicalCompleteRelations.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalZeroModeVector
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_first_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_mem_higher
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCompleteSource_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalZeroModeVector_mem_higher_of_unsupported

-- SL4TRadicalPowerSumKernel.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.linearEvaluation_relationAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPowerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPowerSumAlgebra_preserves_relations

-- SL4TRadicalPowerSumGeneration.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSlotEmbedding
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModePowerSum_eq_rename
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabet_symmetric_mem_powerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeOrbitSum_mem_powerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSymmetricModes_le_powerSumAlgebra

-- SL4TRadicalCountSupport.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_one
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_eq_zero_of_one
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_eq_bot_of_unsupported
