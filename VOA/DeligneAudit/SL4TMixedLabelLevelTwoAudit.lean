import VOA.DeligneAudit.SL4TMixedLabelPresentationAudit
import VOA.DeligneAudit.SL4TSecondLeviRelativeQuotient

/-!
Second Levi mode evaluation, relative complete-function relations, and symmetric descent.

The evaluator retains all mode degrees and all first Levi coefficient vectors.
Its image is the two-colour count span, summed over the Grassmannian base.
Independent permutation averaging gives a separately symmetric representative of every
image vector. The quotient is by the Levi closure of greater height at the same depth.
Both Cartans descend, with source symbols U - 2A - B and V + A - B.

The two relative complete-function families are expressed using the Newton coefficients
of the base power sums. The first family follows from corrected Garland. For the second,
letter conversion is proved with its source term retained; lower contractions have greater
height at the same depth. Summing against the base Newton coefficients then gives the
converted Garland vanishing. These statements apply at every base vector.

The base-saturated kernel is propagated using only the two retained Cartans. Independent
orbit sums prove that their positive power sums and the base coefficients generate every
separately symmetric polynomial. The finite relative relation ideal therefore lies in the
saturated kernel. Empty alphabets require no extra assumption: their finite relation windows
are empty. The resulting relative symmetric-function quotient has a surjective linear map
onto the actual second multiplicity, equivariant for both positive Cartans.

Main endpoints:
* radicalSecondLeviEvaluation_surjective and radicalSecondLeviEvaluation_cartan;
* radicalSecondLeviEvaluation_firstRelativeTail and
  radicalSecondLeviEvaluation_secondRelativeTail;
* radicalSecondLeviEvaluation_relative_mul;
* radicalSecondLeviRelativeIdeal_le_relations;
* radicalSecondLeviRelativeEvaluation_surjective and
  radicalSecondLeviRelativeEvaluation_cartan.

The relative quotient statements assume the local Weyl relations at arbitrary labels
(a,b,c) and nonnegative first Levi highest weights. No truncation or desired rank bound
is assumed. Individual tail statements require a positive count; the finite-window ideal
and descended surjection do not require positive counts.

Not proved here:
1. The identification of RadicalSecondLeviRelativeRing a b a d e1 e2 with MixedRing at
   supported parameters. This needs the elementary-generator map, identification of the
   base Newton coefficients with the complementary Grassmannian elementary coefficients,
   and generation/surjectivity. The Grassmannian model is unchanged.
2. The identification of the second Cartan source symbol with mixedPowerSum under that map.
   The source symbol is V + A - B; equality with the characteristic-alphabet power
   sum is not proved here.
3. The second blocks' highest-weight, sharp lowering, unsupported-count, and truncated
   generation statements, and the assembly of the two finite Levi filtrations using right
   exactness, mixedRingImage_bound, and mixedBlockBound_sum_all_valid.
MixedLabelTruncatedRank is not proved in this module. In particular, no surjection from
MixedRing is claimed by this audit.

Axiom check: every theorem inventoried here has exactly the standard three axioms
`[propext, Classical.choice, Quot.sound]`. No `sorry` is used.

The declaration inventory below includes definitions and abbreviations as well as theorems.
Every theorem is audited in its source file and again in this combined import environment.
-/

-- SL4TPositionModeEvaluation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeProduct
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeProduct_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModePowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_powerSum_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_cartan

-- SL4TSecondLeviCompleteRelations.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.completePolynomial_modeVectors
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_prod_C
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_firstComplete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelativeComplete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_relativeComplete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_firstRelativeTail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_firstRelativeTail

-- SL4TSecondLeviConversion.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_le_higher
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lower_summand
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lower_term
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_lowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_topSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_coefficient

-- SL4TSecondLeviEvaluation.lean
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.SecondLeviModeSlot
-- Axioms: []
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePositions
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePositions_nodup
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionOperator
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_range
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviCartanCharge
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionOperator_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePowerSum_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_cartan

-- SL4TSecondLeviKernel.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviBaseEmbedding
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_saturated_generators
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_symmetric_mul
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_relative_mul

-- SL4TSecondLeviMultiplicity.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherSecondLeviCountClosure
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientCartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricMultiplicityEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricMultiplicityEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_surjective

-- SL4TSecondLeviPowerSums.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPowerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_monomial
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviFirstAlphabet_mem_powerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSecondAlphabet_mem_powerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_mem_powerSumAlgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricModes_le_powerSumAlgebra

-- SL4TSecondLeviPresentation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviComplete_symmetric
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelativeGenerator
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelativeIdeal
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSaturatedRelationIdeal
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelationQuotientEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelationQuotientEvaluation_mk
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviRelationQuotientEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeIdeal_le_relations

-- SL4TSecondLeviRelativeQuotient.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModePowerSum_symmetric
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSourceCartanSymbol
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalSecondLeviRelativeRing
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_mk
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_cartan

-- SL4TSecondLeviRelativeRelations.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_secondComplete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_secondRelativeComplete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_correctedCoefficient
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_secondRelativeTail
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_secondRelativeTail

-- SL4TSecondLeviSymmetricEvaluation.lean
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSlotPermutation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviColourProduct_perm
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviPositionProduct_permute
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_rename
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviSymmetricModes
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeOrbitSum_mem
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_orbitSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_symmetric_representative

