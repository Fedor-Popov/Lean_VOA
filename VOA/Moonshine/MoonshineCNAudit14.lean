import VOA.Moonshine.MoonshineCNAudit13
import VOA.Moonshine.MoonshineCNBorcherdsAugmentation
import VOA.Moonshine.MoonshineCNBorcherdsGeneration
import VOA.Moonshine.MoonshineCNBorcherdsGeneratorWeights
import VOA.Moonshine.MoonshineCNBorcherdsLevi
import VOA.Moonshine.MoonshineCNBorcherdsParabolicAction
import VOA.Moonshine.MoonshineCNBorcherdsStringAction
import VOA.Moonshine.MoonshineCNBorcherdsStringSum
import VOA.Moonshine.MoonshineCNLieProjection
import VOA.Moonshine.MoonshineCNRelativeInduction
import VOA.Moonshine.MoonshineCNRelativePBW
import VOA.Moonshine.MoonshineCNVermaMultiplication

/-! Kernel dependency audit for the abstract structural and PBW results on the positive part of a
Borcherds algebra (generation, augmentation ideal, Verma multiplication). -/

#print axioms VOA.Moonshine.ConwayNorton.envelopingAlgebra_induction
#print axioms VOA.Moonshine.ConwayNorton.envelopingAugmentation
#print axioms VOA.Moonshine.ConwayNorton.envelopingGeneratorLeftIdeal
#print axioms VOA.Moonshine.ConwayNorton.enveloping_lieSpan_mem_generatorIdeal
#print axioms VOA.Moonshine.ConwayNorton.enveloping_sub_augmentation_mem
#print axioms VOA.Moonshine.ConwayNorton.enveloping_augmentationIdeal_eq
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGeneratorSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGeneratorSpace_lieSpan
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positive_augmentationIdeal_eq
#print axioms VOA.Moonshine.ConwayNorton.lieSpan_parabolic_bracket_mem
#print axioms VOA.Moonshine.ConwayNorton.lieSpan_parabolic_sum
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.lieSpan_genSpace_le_positive
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_parabolic_bracket_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePart_eq_lieSpan_genSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_weight_intersection
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorString_finrank
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceLeviSubmodule
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_equivariant
#print axioms VOA.Moonshine.ConwayNorton.borcherdsNegativeCone
#print axioms VOA.Moonshine.ConwayNorton.borcherdsLeviDegree
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpace_le_weightSpan
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpan_mono_predicate
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpan_le_of_supported
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpan_bracket_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.negativePart
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.leviPart
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.negativePart_le_parabolic
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.leviPart_le_parabolic
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.levi_normalizes_positive
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolic_normalizes_negative
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.levi_normalizes_negative
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.negativeParabolicIdeal
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolic_eq_levi_sup_negative
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.levi_negative_disjoint
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicNegativeSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolic_levi_negative_isCompl
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviProjectionLinear
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviProjection_residual
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviProjection_left
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviProjection_right
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicLeviProjection
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceParabolicRep
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceParabolicRep_levi
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceParabolicRep_negative
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_bracket_mem_of_strings
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_cartan_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_raising_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_lowering_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.realRoot_vector_eq_smul
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_levi_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_negative_bracket_simple
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_negative_bracket_string
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.negative_bracket_genSpace
#print axioms VOA.Moonshine.ConwayNorton.borcherdsStringIndex
#print axioms VOA.Moonshine.ConwayNorton.borcherdsStringDegree
#print axioms VOA.Moonshine.ConwayNorton.borcherdsStringDegree_injective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorString_le_genSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_eq_iSup_strings
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorStrings_independent
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceDirectSumMap
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceDirectSumMap_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceDirectSumEquiv
#print axioms VOA.Moonshine.ConwayNorton.leviProjectionOfComplement
#print axioms VOA.Moonshine.ConwayNorton.leviProjectionOfComplement_mem
#print axioms VOA.Moonshine.ConwayNorton.leviProjectionOfComplement_left
#print axioms VOA.Moonshine.ConwayNorton.leviProjectionOfComplement_right
#print axioms VOA.Moonshine.ConwayNorton.leviProjectionOfComplement_residual
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedSpace
#print axioms VOA.Moonshine.ConwayNorton.relativeTensorLeft
#print axioms VOA.Moonshine.ConwayNorton.relativeTensorLeft_tmul
#print axioms VOA.Moonshine.ConwayNorton.relativeBalancing_left_stable
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedLeft
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedLeft_mk
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedLeft_tmul
#print axioms VOA.Moonshine.ConwayNorton.relativeInduced_ext
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedAlgebra
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedRep
#print axioms VOA.Moonshine.ConwayNorton.relativeInduced_bottom_relation
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedRep_bottom
#print axioms VOA.Moonshine.ConwayNorton.relativePBWEvaluation
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates_mk
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates_bottom
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates_left
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWord
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWord_nil
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWord_cons
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_single
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_zero
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_low
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedRep_comm
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates_word
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_action_single
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_action
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_enveloping_action
#print axioms VOA.Moonshine.ConwayNorton.relativePBWCoordinates_wordMap
#print axioms VOA.Moonshine.ConwayNorton.relativeInducedWordMap_coordinates
#print axioms VOA.Moonshine.ConwayNorton.relativePBWEquiv
#print axioms VOA.Moonshine.ConwayNorton.relativeTrivialBalancing_eq_bot
#print axioms VOA.Moonshine.ConwayNorton.relativeTrivialInducedEquiv
#print axioms VOA.Moonshine.ConwayNorton.relativeTrivialInducedEquiv_rep
#print axioms VOA.Moonshine.ConwayNorton.relativeComplementBasis
#print axioms VOA.Moonshine.ConwayNorton.relativeVermaMultiplication
#print axioms VOA.Moonshine.ConwayNorton.relativeVermaMultiplication_action
#print axioms VOA.Moonshine.ConwayNorton.relativeVermaMultiplication_word
#print axioms VOA.Moonshine.ConwayNorton.relativeVermaMultiplication_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicVermaMultiplication
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicVermaMultiplication_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicVermaEquiv

#check @VOA.Moonshine.ConwayNorton.BorcherdsData.negativeParabolicIdeal
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceDirectSumEquiv
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_weight_intersection
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_levi_stable
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.positivePart_eq_lieSpan_genSpace
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.positive_augmentationIdeal_eq
#check @VOA.Moonshine.ConwayNorton.relativePBWEquiv
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicVermaMultiplication_bijective
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceParabolicRep
