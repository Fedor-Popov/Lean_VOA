import VOA.Moonshine.MoonshineCNAudit11
import VOA.Moonshine.MoonshineCNDressingAdjoint
import VOA.Moonshine.MoonshineCNChargedAdjoint
import VOA.Moonshine.MoonshineCNCurrentAdjoint
import VOA.Moonshine.MoonshineCNTensorGeneratorAdjoint
import VOA.Moonshine.MoonshineCNBorcherdsRoots
import VOA.Moonshine.MoonshineCNBorcherdsData
import VOA.Moonshine.MoonshineCNBorcherdsSl2
import VOA.Moonshine.MoonshineCNBorcherdsParabolic

/-! Kernel dependency audit for the generator adjoints and abstract Lie-theoretic preliminaries. -/

#print axioms VOA.Moonshine.ConwayNorton.directionOscillator_dressingField_apply
#print axioms VOA.Moonshine.ConwayNorton.creationVariable_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.creationCoefficient_succ_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.dressingField_vacuum_constantCoeff
#print axioms VOA.Moonshine.ConwayNorton.uForm_dressingField_vacuum
#print axioms VOA.Moonshine.ConwayNorton.uForm_dressingField_adjoint
#print axioms VOA.Moonshine.ConwayNorton.latForm_canonicalChargedField_state
#print axioms VOA.Moonshine.ConwayNorton.latForm_canonicalChargedField_adjoint
#print axioms VOA.Moonshine.ConwayNorton.latForm_frameStateField_charge_adjoint
#print axioms VOA.Moonshine.ConwayNorton.latForm_frameCurrent_state
#print axioms VOA.Moonshine.ConwayNorton.latForm_frameCurrent_adjoint
#print axioms VOA.Moonshine.ConwayNorton.frameStateField_currentState
#print axioms VOA.Moonshine.ConwayNorton.latForm_frameStateField_current_adjoint
#print axioms VOA.Moonshine.ConwayNorton.frameStateField_generated_by_charges_currents
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_latticeGenerator_mode
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_vnatGenerator_mode
#print axioms VOA.Moonshine.ConwayNorton.bilinearTensor_lTensor_adjoint
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_chargeGenerator_adjoint
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_currentGenerator_adjoint
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_vnatGenerator_fhl
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRealRoot
#print axioms VOA.Moonshine.ConwayNorton.borcherdsImaginaryRoot
#print axioms VOA.Moonshine.ConwayNorton.borcherdsPositiveCone
#print axioms VOA.Moonshine.ConwayNorton.borcherdsPositiveRoot
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRootSupport
#print axioms VOA.Moonshine.ConwayNorton.borcherdsSimpleRoot
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRootHeight
#print axioms VOA.Moonshine.ConwayNorton.borcherdsWeightVector
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanPairing
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCasimirScalar
#print axioms VOA.Moonshine.ConwayNorton.borcherdsPositiveCone_add
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRootSupport_neg
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRootSupport_axis
#print axioms VOA.Moonshine.ConwayNorton.borcherdsSimpleRoot_sub_not_positive
#print axioms VOA.Moonshine.ConwayNorton.borcherdsPositiveRoot_add_simple
#print axioms VOA.Moonshine.ConwayNorton.borcherdsPositiveCone_height_finite
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCasimirScalar_eq
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCasimirScalar_zero_iff
#print axioms VOA.Moonshine.ConwayNorton.borcherdsSimpleGenerators
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.GAction
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weight_eq_bot_of_not_supported
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartan_mem_weight_zero
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.bracket_eq_form_smul_cartan
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.exists_normalized_real_pair
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.real_sl2_relations
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.simple_lowering_vanishes
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.real_sl2_triple
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.simple_cartan_weight
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.adReal_pow_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.adReal_pow_simple_vanishes
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.real_lowering_string
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.adReal_pow_injective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorString
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorString_le_weight
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorStringMap
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorStringEquiv
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_le_positive
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorStringMap_equivariant
#print axioms VOA.Moonshine.ConwayNorton.borcherdsParabolicDegree_add
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpan
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.weightSpan_bracket
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePart
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicPart
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positive_parabolic_isCompl
