import VOA.Moonshine.MoonshineCNAudit6
import VOA.Moonshine.MoonshineCNHyperbolicCentralScalar
import VOA.Moonshine.MoonshineCNHyperbolicMixedModes
import VOA.Moonshine.MoonshineCNHyperbolicModeGrading
import VOA.Moonshine.MoonshineCNHyperbolicPositiveCreation
import VOA.Moonshine.MoonshineCNHyperbolicSugawaraAdjoint
import VOA.Moonshine.MoonshineCNHyperbolicVirasoro
import VOA.Moonshine.MoonshineCNTensorLightCone
import VOA.Moonshine.MoonshineCNTensorLightConeKernels
import VOA.Moonshine.MoonshineCNTensorNegative
import VOA.Moonshine.MoonshineCNTensorPBWEquiv
import VOA.Moonshine.MoonshineCNTensorPBWMap
import VOA.Moonshine.MoonshineCNVnatLightCone
import VOA.Moonshine.MoonshineCNVnatSectorOperators

/-! Every new explicit declaration of this batch, with the cumulative previous audit. -/

#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_central_triangular_sum
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_central_sum
#print axioms VOA.Moonshine.ConwayNorton.hypLoweringDerivation_potential_constant
#print axioms VOA.Moonshine.ConwayNorton.hypPositiveSecondOrder_negativePotential
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_positive_negative_constant
#print axioms VOA.Moonshine.ConwayNorton.hypForm_separates_left
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_positive_oscillator_comm
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_zero_creation
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_zero_pderiv
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_zero_oscillator_comm
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_oscillator_comm
#print axioms VOA.Moonshine.ConwayNorton.hypLevel_eq_sugawara_eigenspace
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_mem_level
#print axioms VOA.Moonshine.ConwayNorton.hypSecondDerivative_creation
#print axioms VOA.Moonshine.ConwayNorton.hypPositiveSecondOrder_creation_sum
#print axioms VOA.Moonshine.ConwayNorton.hypPositiveSecondOrder_creation_a
#print axioms VOA.Moonshine.ConwayNorton.hypPositiveSecondOrder_creation_b
#print axioms VOA.Moonshine.ConwayNorton.hypPositiveSecondOrder_creation
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_positive_creation
#print axioms VOA.Moonshine.ConwayNorton.hypForm_sugawara_negative_adjoint
#print axioms VOA.Moonshine.ConwayNorton.hypForm_sugawara_zero_adjoint
#print axioms VOA.Moonshine.ConwayNorton.hypForm_sugawara_adjoint
#print axioms VOA.Moonshine.ConwayNorton.hypSugawaraVirasoroDefect
#print axioms VOA.Moonshine.ConwayNorton.hypSugawaraVirasoroDefect_commutes
#print axioms VOA.Moonshine.ConwayNorton.hypSugawaraVirasoroDefect_scalar
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_zero_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_vacuum_constant
#print axioms VOA.Moonshine.ConwayNorton.hypSugawaraVirasoroDefect_constant
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_virasoro
#print axioms VOA.Moonshine.ConwayNorton.hypTensorOneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypTensorOneFamily_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorOneFamily_zero
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_sorted_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_sorted_word
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypTensorBPositive
#print axioms VOA.Moonshine.ConwayNorton.hypTensorBPositive_isCompl
#print axioms VOA.Moonshine.ConwayNorton.hypTensorBPositive_word
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegativeSpurious
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_positive_le_spurious
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegativeSpurious_le_PBWMap_positive
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegativeSpurious_eq_PBWMap_positive
#print axioms VOA.Moonshine.ConwayNorton.hypTensor_lightConeSplit
#print axioms VOA.Moonshine.ConwayNorton.hypTensorOneFamily_eq_commonKernel
#print axioms VOA.Moonshine.ConwayNorton.hypTensor_lightConeSplit_oscillator
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap_involutive
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap_negative
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSwap_spurious
#print axioms VOA.Moonshine.ConwayNorton.hypTensor_lightConeSplit_swapped
#print axioms VOA.Moonshine.ConwayNorton.hypTensor_lightConeSplit_nonzero
#print axioms VOA.Moonshine.ConwayNorton.hypTensorCoordinates
#print axioms VOA.Moonshine.ConwayNorton.hypTensorCoordinates_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorCoordinates_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypTensorCoordinates_symm_single
#print axioms VOA.Moonshine.ConwayNorton.hypTensor_expansion
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSupported
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSupported_mem
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSupported_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSupported_mono
#print axioms VOA.Moonshine.ConwayNorton.hypTensorSupported_induction
#print axioms VOA.Moonshine.ConwayNorton.hypTensorFiltered
#print axioms VOA.Moonshine.ConwayNorton.hypTensorFiltered_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorFiltered_mono
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative_comm
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_coefficient_at_max
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_injective
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_monomial_mem_range
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_surjective
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative_leading
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative_filtered
#print axioms VOA.Moonshine.ConwayNorton.hypTensorNegative_word_leading
#print axioms VOA.Moonshine.ConwayNorton.hypTensorWordOperator
#print axioms VOA.Moonshine.ConwayNorton.hypTensorWordOperator_apply
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypTensorPBWMap_leading
#print axioms VOA.Moonshine.ConwayNorton.nearVirasoroNegative_comm
#print axioms VOA.Moonshine.ConwayNorton.vnatHypNegative
#print axioms VOA.Moonshine.ConwayNorton.vnatHypTensor_lightConeSplit
#print axioms VOA.Moonshine.ConwayNorton.vnatHypMode
#print axioms VOA.Moonshine.ConwayNorton.vnatHypMode_negative
#print axioms VOA.Moonshine.ConwayNorton.vnatHypMode_virasoro
#print axioms VOA.Moonshine.ConwayNorton.vnatHypForm
#print axioms VOA.Moonshine.ConwayNorton.vnatHypForm_symm
#print axioms VOA.Moonshine.ConwayNorton.vnatHypForm_adjoint
#print axioms VOA.Moonshine.ConwayNorton.vnatHypForm_coefficient
#print axioms VOA.Moonshine.ConwayNorton.vnatHypForm_nondegenerate
#print axioms VOA.Moonshine.ConwayNorton.vnatHypMode_lightConeSplit

