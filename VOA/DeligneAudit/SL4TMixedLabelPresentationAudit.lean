import VOA.DeligneAudit.SL4TMixedLabelLevelOneAudit
import VOA.DeligneAudit.SL4TTwoCartanKernel
import VOA.DeligneAudit.SL4TRadicalLeviGarland

/-!
The Grassmannian presentation of the first Levi multiplicity spaces.

The finite-alphabet specialization identifies the complete-polynomial relations with
the Garland source vectors. The evaluator therefore descends through all three
Grassmannian quotients. The descended map is surjective and intertwines all positive
alphabet Cartan currents with multiplication by Grassmannian power sums.

The two retained Levi Cartan currents propagate relations through all power-sum
multipliers, provided the relations hold at every base vector. Corrected Garland
coefficients vanish at the entire first Levi Grassmannian image.

The second Levi multiplicity evaluator, its relative complete-function relations,
its mixed-ring descent, and the final truncated rank assembly are not proved here.

The fixed elementary-generator Grassmannian ring and its full complete-function tail are
used directly. No exact Grassmannian dimension
or annihilator calculation is required for this descent.

The remaining current-module construction must retain all degrees and every base
vector in the second Levi multiplicity; it requires identifying the two relative
complete-function families with the corrected Garland coefficients and the adjacent-letter
conversion, and applying `twoCartan_relationIdeal_le_kernel` to the actual evaluator. That
theorem is an abstract implication with explicit generation and Cartan hypotheses; it does
not supply the missing second Levi evaluator or establish its source relations.
The full conclusion `MixedLabelTruncatedRank` remains unproved here.

Two remarks: the first Levi image has nonzero positive Cartan
action, so the zero-positive-Cartan local Weyl theorem does not apply to each base
vector. Use `radicalGrassmannianAmbientEvaluation_garland` with its Newton factor.
Also, kernel stability under base multiplication is only available for saturated
relations; it must not be assumed for an arbitrary kernel vector.

Axiom check: every theorem of these files depends exactly on
`[propext, Classical.choice, Quot.sound]`. The complete declaration inventory and printed
axiom lists follow, grouped by file.
-/

-- SL4TCompletePolynomialSpecialization.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.elementarySpecialization
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.elementarySpecialization_elementary
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.elementaryProduct_coeff
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.finiteAlphabet_complete_relation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.elementarySpecialization_complete

-- SL4TRadicalCompleteEvaluation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.currentPower_coeff_modeVectors
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_prod
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalSingleAlphabetModes
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_alphabet_prod
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_complete
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_complete_eq_zero

-- SL4TRadicalGrassmannianDescent.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_val
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityRelationIdeal
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalMultiplicityRing
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalRelationQuotientEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalRelationQuotientEvaluation_mk
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalRelationQuotientEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_grassIdeal
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianFactor
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianFactor_mk
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianQuotientMap
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianEvaluation

-- SL4TRadicalGrassmannianPowerSums.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_map
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPositivePowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalElementaryModes_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianFactor_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianQuotientMap_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianQuotientMap_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianEvaluation_surjective
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianEvaluation_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianPresentation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_rank_le

-- SL4TTwoCartanKernel.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.baseSaturatedEvaluationKernel
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.baseSaturatedEvaluationKernel_base_mul
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoCartan_saturatedKernel_generators
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.multiplicationPreservingSubalgebra
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoCartan_saturatedKernel_mul
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoCartan_relationIdeal_le_kernel

-- SL4TRadicalLeviGarland.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.leviSimple_currentRelations
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalLeviPowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_cartan_difference
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_raising
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_lowering
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_garland

