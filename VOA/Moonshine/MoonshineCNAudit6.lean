import VOA.Moonshine.MoonshineCNAudit5
import VOA.Moonshine.MoonshineCNHyperbolicNegativeModes
import VOA.Moonshine.MoonshineCNHyperbolicNegativeVirasoro
import VOA.Moonshine.MoonshineCNHyperbolicOneFamily
import VOA.Moonshine.MoonshineCNHyperbolicFiltration
import VOA.Moonshine.MoonshineCNHyperbolicFilteredWords
import VOA.Moonshine.MoonshineCNHyperbolicPBWMap
import VOA.Moonshine.MoonshineCNHyperbolicPBWEquiv
import VOA.Moonshine.MoonshineCNHyperbolicPBWCoordinates
import VOA.Moonshine.MoonshineCNHyperbolicLightCone
import VOA.Moonshine.MoonshineCNHyperbolicSwap

/-! # Audit of the concrete hyperbolic light-cone splitting

All new explicit declarations are audited, including the coordinate and
filtration lemmas. This audit does not assert a tensor-sector StringModule
or the V♮ no-ghost identification.
-/

#print axioms VOA.Moonshine.ConwayNorton.hypNegativeWordOperator
#print axioms VOA.Moonshine.ConwayNorton.hypNegativeWordOperator_apply
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_monomial_of_support
#print axioms VOA.Moonshine.ConwayNorton.hypAExponent_add
#print axioms VOA.Moonshine.ConwayNorton.hypBExponent_add
#print axioms VOA.Moonshine.ConwayNorton.hypAExponent_bEmbedding
#print axioms VOA.Moonshine.ConwayNorton.hypBExponent_bEmbedding
#print axioms VOA.Moonshine.ConwayNorton.hypAExponent_of_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypBExponent_of_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_sorted_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_sorted_word
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_coefficient_at_max
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_injective
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_monomial_mem_range
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_surjective
#print axioms VOA.Moonshine.ConwayNorton.hypPBWEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypBPositive
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_eq_countZero
#print axioms VOA.Moonshine.ConwayNorton.hypBPositive_isCompl
#print axioms VOA.Moonshine.ConwayNorton.hypBPositive_of_homogeneous
#print axioms VOA.Moonshine.ConwayNorton.hypNegativeSpurious
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_positive_le_spurious
#print axioms VOA.Moonshine.ConwayNorton.hypNegativeSpurious_le_PBWMap_positive
#print axioms VOA.Moonshine.ConwayNorton.hypNegativeSpurious_eq_PBWMap_positive
#print axioms VOA.Moonshine.ConwayNorton.hypFock_lightConeSplit
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_eq_commonKernel
#print axioms VOA.Moonshine.ConwayNorton.hypFock_lightConeSplit_oscillator
#print axioms VOA.Moonshine.ConwayNorton.hypAExponent
#print axioms VOA.Moonshine.ConwayNorton.hypBExponent
#print axioms VOA.Moonshine.ConwayNorton.hypCanonicalBWord
#print axioms VOA.Moonshine.ConwayNorton.hypCanonicalBWord_sorted
#print axioms VOA.Moonshine.ConwayNorton.hypBWordMonomial_exponent
#print axioms VOA.Moonshine.ConwayNorton.hypExponent_split
#print axioms VOA.Moonshine.ConwayNorton.hypAExponent_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypCanonicalBWord_factorization
#print axioms VOA.Moonshine.ConwayNorton.hypCanonicalBWord_degrees
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypPBWMap_leading
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_X
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_involutive
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_raising
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_negativePotential
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_negativeMode
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypSwapPolynomial_spurious
#print axioms VOA.Moonshine.ConwayNorton.hypFock_lightConeSplit_swapped
#print axioms VOA.Moonshine.ConwayNorton.hypFock_lightConeSplit_nonzero
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_mem_iff
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_coeff
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_iff_pderiv
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_iff_oscillator
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_eq_range
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_constant_mem
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_form
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamilyEval
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamilyAugmentation
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamilyEval_surjective
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_radical_iff
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamilyQuotientEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamilyQuotientEquiv_mk
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_decomposition
#print axioms VOA.Moonshine.ConwayNorton.hypBCountWeight
#print axioms VOA.Moonshine.ConwayNorton.hypBLevelWeight
#print axioms VOA.Moonshine.ConwayNorton.hypBHomogeneous
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered_mem
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered_of_count_lt
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered_of_homogeneous
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered_mono
#print axioms VOA.Moonshine.ConwayNorton.hypBHomogeneous_monomial
#print axioms VOA.Moonshine.ConwayNorton.hypBHomogeneous_mul
#print axioms VOA.Moonshine.ConwayNorton.hypBHomogeneous_X
#print axioms VOA.Moonshine.ConwayNorton.hypRaisingDerivation_preserves_bCount
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_leading_filtered
#print axioms VOA.Moonshine.ConwayNorton.hypNegativePotential_pderiv_b
#print axioms VOA.Moonshine.ConwayNorton.hypNegativePotential_pderiv_a
#print axioms VOA.Moonshine.ConwayNorton.hypNegativePotential_pderiv
#print axioms VOA.Moonshine.ConwayNorton.hypRaisingDerivation_pderiv_comm
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_pderiv
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_oscillator_comm
#print axioms VOA.Moonshine.ConwayNorton.hypBFiltered_mul_b
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_filtered
#print axioms VOA.Moonshine.ConwayNorton.hypBWordMonomial
#print axioms VOA.Moonshine.ConwayNorton.hypBWordMonomial_homogeneous
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_word_leading
#print axioms VOA.Moonshine.ConwayNorton.hypOneFamily_bHomogeneous_zero
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_word_leading_oneFamily
#print axioms VOA.Moonshine.ConwayNorton.hypNegativePotential_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.hypRaisingDerivation_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.hypNegativeVirasoroDefect_commutes
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_comm
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_straightening
#print axioms VOA.Moonshine.ConwayNorton.hypSugawara_negative_nonempty_straightening

