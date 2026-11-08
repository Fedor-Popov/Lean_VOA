import VOA.Moonshine.MoonshineCNAudit16
import VOA.Moonshine.MoonshineCNEnvelopingEmbedding
import VOA.Moonshine.MoonshineCNBorcherdsCartanWeights
import VOA.Moonshine.MoonshineCNBorcherdsVermaWeights
import VOA.Moonshine.MoonshineCNInducedVectorMap
import VOA.Moonshine.MoonshineCNBorcherdsResolution
import VOA.Moonshine.MoonshineCNBorcherdsTensorEnveloping
import VOA.Moonshine.MoonshineCNBorcherdsFreeLie
import VOA.Moonshine.MoonshineCNMonsterCartanAction
import VOA.Moonshine.MoonshineCNMonsterBorcherdsData

/-! Kernel dependency audit for the length-one resolution of the trivial module by generalized
Verma modules, the isomorphism of the tensor algebra on U with the enveloping algebra of the
positive part, freeness of the positive part on U, the Cartan action on the Monster Lie algebra,
and the Monster Lie algebra as Borcherds data under its simple-root generation hypothesis. -/

#print axioms VOA.Moonshine.ConwayNorton.envelopingEmbedding_injective
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanPairing_weight_add
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanPairing_weight_zero
#print axioms VOA.Moonshine.ConwayNorton.borcherdsWeightCharacter_injective
#print axioms VOA.Moonshine.ConwayNorton.ker_le_iSup_inf_of_graded
#print axioms VOA.Moonshine.ConwayNorton.trivialInducedSpace
#print axioms VOA.Moonshine.ConwayNorton.trivialInduced_mk_mul_eq_zero
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorTensorMap
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorTensorMap_tmul
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap_mk
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap_equivariant
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap_bottom
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap_verma
#print axioms VOA.Moonshine.ConwayNorton.inducedVectorMap_verma_generator
#print axioms VOA.Moonshine.ConwayNorton.generatorMultiplication_injective_of_inducedVectorMap
#print axioms VOA.Moonshine.ConwayNorton.trivialInduced_action_bottom_injective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsAdmissible.submodule_eq_bot_of_casimir_zero
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration_succ
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration_le_succ
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration_mono
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration_mul
#print axioms VOA.Moonshine.ConwayNorton.tensorDegreeFiltration_exhaustive
#print axioms VOA.Moonshine.ConwayNorton.envelopingAugmentation_generatorMultiplication
#print axioms VOA.Moonshine.ConwayNorton.tensorGeneratorRangeEquiv
#print axioms VOA.Moonshine.ConwayNorton.tensorGeneratorToEnveloping_injective_of_multiplication
#print axioms VOA.Moonshine.ConwayNorton.envelopingMap
#print axioms VOA.Moonshine.ConwayNorton.tensorGeneratorMap
#print axioms VOA.Moonshine.ConwayNorton.tensorGeneratorToEnveloping_natural
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap_of
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorLinear
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap_linear
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap_surjective
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap_injective
#print axioms VOA.Moonshine.ConwayNorton.freeLieInducedMap
#print axioms VOA.Moonshine.ConwayNorton.freeLieGeneratorMap_natural
#print axioms VOA.Moonshine.ConwayNorton.frameWordState_single_oscillator
#print axioms VOA.Moonshine.ConwayNorton.lorentzianFrame_coordinate_zero
#print axioms VOA.Moonshine.ConwayNorton.lorentzianFrame_coordinate_one
#print axioms VOA.Moonshine.ConwayNorton.lorentzianFrameCurrent_zeroMode
#print axioms VOA.Moonshine.ConwayNorton.latStateGen_add_smul
#print axioms VOA.Moonshine.ConwayNorton.lorentzianHyperbolicCurrent_zeroMode
#print axioms VOA.Moonshine.ConwayNorton.lorentzianZero_eq_vector
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_zeroBasis_zeroMode
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_zeroWeight_zeroProduct
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_zeroSector_bracket
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_zeroMomentum_bracket
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_apply_zero
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_apply_one
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentumEquiv
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_add
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_neg
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_zero
#print axioms VOA.Moonshine.ConwayNorton.borcherdsMomentum_eq_zero_iff
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight_zero
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight_isInternal
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsRootEquiv
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight_finite
#print axioms VOA.Moonshine.ConwayNorton.borcherdsRootSupport_of_product
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight_support
#print axioms VOA.Moonshine.ConwayNorton.vnat_finrank_zero
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsWeight_real_finrank
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanCoordinates
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanCoordinates_injective
#print axioms VOA.Moonshine.ConwayNorton.borcherdsCartanCoordinates_surjective
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap_mem
#print axioms VOA.Moonshine.ConwayNorton.monsterLieZeroMomentumEquiv_cartan
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap_injective
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap_range
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap_action
#print axioms VOA.Moonshine.ConwayNorton.monsterLieCartanMap_form
#print axioms VOA.Moonshine.ConwayNorton.MonsterLieSimpleRootGeneration
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsData
#print axioms VOA.Moonshine.ConwayNorton.monsterLieLinearAction
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAut_fixes_real
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBorcherdsAction
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_generatorString_finrank
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_generatorVermaResolution_shortExact
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_positiveTensorEnveloping_bijective
#print axioms VOA.Moonshine.ConwayNorton.monsterLie_positivePartFreeLie_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.mem_cartanEigenspace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartan_bracket_eq_zero
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartan_action_commute
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_action
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_iSupIndep
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_eq_bot_of_span
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_span_maps
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_span_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanAdmissible
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanAdmissible_weightSpace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartanEigenspace_kernel_graded
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartan_mem_parabolic
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.cartan_mem_levi
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.inducedPositive_enveloping_stable
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.inducedSpace_eq_top_of_bottom
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.inducedCartanEigenspace_span
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.bottom_mem_cartanEigenspace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.parabolicTrivialRep
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialBottom_mem_cartanEigenspace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialVerma_cartanEigenspace_span
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialVermaAdmissible
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBottom_mem_of_strings
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBottom_mem_cartanEigenspace
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBottom_mem_positive_span
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVerma_cartanEigenspace_span
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaAdmissible
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVerma_weight_eq_bot
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpaceParabolicRep_sub_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaResolution
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaResolution_equivariant
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBottom_raising
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.genSpace_raising_pow_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorBottom_raising_pow
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVerma_casimir_bottom
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVerma_casimir_eq_zero
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVerma_firstLine_bottom
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaResolution_firstLine
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaResolution_injective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGeneratorMultiplication_injective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGeneratorMultiplication_shortExact
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialVermaAugmentation
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialVermaAugmentation_verma
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.trivialVermaAugmentation_surjective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.generatorVermaResolution_shortExact
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTensorGeneratorToEnveloping_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTensorEnvelopingEquiv
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTensorEnvelopingEquiv_generator
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePart_action_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartAction
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGenerator_action_mem
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTensorEnvelopingEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positiveGeneratorBasis
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartFreeLie_bijective
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartFreeLieEquiv
#print axioms VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartFreeLieEquiv_equivariant

open VOA.Moonshine.ConwayNorton in
example {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g) (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot) (hf : f ∈ D.weightSpace (-borcherdsRealRoot))
    (hef : D.form e f = 1) :
    Function.Injective (D.generatorVermaResolution e f he hf hef) ∧
      Function.Exact (D.generatorVermaResolution e f he hf hef) D.trivialVermaAugmentation ∧
      Function.Surjective D.trivialVermaAugmentation :=
  D.generatorVermaResolution_shortExact e f he hf hef

attribute [local instance] VOA.Moonshine.ConwayNorton.monsterPhysicalAddCommGroup

open VOA.Moonshine.ConwayNorton in
example (h : monsterLieMomentum 0) (β : lorentzianLattice.carrier) (x : monsterLieAlgebra)
    (hx : x ∈ monsterLieMomentum β) :
    ⁅(h : monsterLieAlgebra), x⁆ =
      (monsterLieZeroMomentumEquiv h 0 * (β 0 : ℂ) + monsterLieZeroMomentumEquiv h 1 * (β 1 : ℂ)) •
        x :=
  monsterLie_zeroMomentum_bracket h β x hx

#check @VOA.Moonshine.ConwayNorton.monsterLieBorcherdsData
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.positiveTensorEnvelopingEquiv_equivariant
#check @VOA.Moonshine.ConwayNorton.BorcherdsData.positivePartFreeLieEquiv_equivariant
