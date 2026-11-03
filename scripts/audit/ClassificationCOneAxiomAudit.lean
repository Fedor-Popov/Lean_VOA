import VOA.Modules.LogTensorArCoefficientFormula
import VOA.Modules.LogTensorArCoordinates
import VOA.Modules.LogTensorPzPointTransport
import VOA.Modules.LogTensorBalancing
import VOA.Modules.LogTensorArBranchEquiv
import VOA.Modules.LogTensorArDualPairing
import VOA.Modules.LogTensorPzPointEvaluation
import VOA.Modules.LogTensorArEquiv
import VOA.Modules.LogModuleCategory
import VOA.Modules.LogModuleC1Dual
import VOA.Modules.LogModuleC1Parts
import VOA.Modules.LogTensorUniformLog
import VOA.Modules.LogTensorTwist
import VOA.Modules.LogModuleC1Graded
import VOA.Modules.LogTensorUniformNil
import VOA.Modules.LogModuleC1Cofinite
import VOA.Modules.LogTensorPzHomFinite
import VOA.Modules.LogTensorContraL0Exp
import VOA.Modules.LogTensorPzMaximal
import VOA.Modules.LogTensorPzReconstruction
import VOA.Modules.LogTensorPzEvaluation
import VOA.Modules.LogTensorContraNilModes
import VOA.Classification.COne.MainConverse
import VOA.Classification.COne.MainUnconditional
import VOA.Classification.COne.MainBeyl
import VOA.Classification
import VOA.Huang
import VOA.Huang.LiConverseMain
import VOA.Huang.GenusOneCloseMain
import VOA.Huang.HuangODEIterPoint
import VOA.Huang.HuangODEContra
import VOA.Classification.COne.AssociativityFinal
import VOA.Classification.COne.CommutativityFinal
import VOA.Huang.ModuleC2Main
import VOA.Classification.COne.MainHuang
import VOA.Classification.COne.MainVerlinde
import VOA.Classification.COne.MainTannakian
import VOA.Classification.COne.ConversePlus
import VOA.Classification.COne.MainSerreStark
import VOA.Classification.COne.PlusC2Final
import VOA.Classification.COne.PlusUnitaryFinal
import VOA.Classification.COne.MainDeligne
import VOA.Classification.COne.MainCurrent
import VOA.Classification.COne.SerreStarkQExpHeadline
import VOA.Huang.AndersonMooreHeadline
import VOA.Classification.COne.SerreStarkQExpAwayHeadline
import VOA.Classification.COne.MainVerlindeEigen
import VOA.Classification.COne.SerreStarkLevelMain
import VOA.Classification.COne.DistinctResiduals
import VOA.Huang.PentagonCloseMain
import VOA.Huang.HexagonCloseResidual
import VOA.Huang.VerlindeTransportHeadline
import VOA.Huang.FivePointSepMain
import VOA.Huang.GenusOneWardHeadline
import VOA.Huang.GenusTwoPointSepEnergyWard
import VOA.Huang.BraidRibbonRealization
import VOA.Classification.COne.PlusSplitSessionNine
import VOA.Classification.COne.PlusSplitOmegaECharacters
import VOA.Classification.COne.MainVerlindeProved
import VOA.Classification.COne.MainHuangProved
import VOA.Huang.HKLExtCFT
import VOA.Huang.HKLLocInput
import VOA.Huang.HKLNiceMain
import VOA.Core.CoreFixCommutative
import VOA.Modules.CoreFixFusion
import VOA.Modules.CoreFixUnitary
import VOA.Classification.COne.OrbRat3Eval
import VOA.Classification.COne.OrbRat3Inner
import VOA.Classification.COne.OrbRat3Outer5
import VOA.Classification.COne.OrbRat3Residual
import VOA.Classification.COne.OrbRat3Module
import VOA.Classification.COne.OrbRat3Telescope
import VOA.Classification.COne.OrbRat4Skew
import VOA.Classification.COne.OrbRat4Cert
import VOA.Classification.COne.OrbRat4Normal
import VOA.Classification.COne.OrbRat4N0
import VOA.Classification.COne.OrbRat4N1
import VOA.Classification.COne.OrbRat4N2
import VOA.Classification.COne.OrbRat4N3
import VOA.Classification.COne.OrbRat4N4
import VOA.Classification.COne.OrbRat4Outer
import VOA.Classification.COne.OrbRat4Telescope
import VOA.Classification.COne.OrbRat5Char
import VOA.Classification.COne.OrbRat5Reduce
import VOA.Classification.COne.OrbRat5UCert
import VOA.Classification.COne.OrbRat5UJ
import VOA.Classification.COne.OrbRat5Low
import VOA.Classification.COne.OrbRat5Wt
import VOA.Classification.COne.OrbRat5Four
import VOA.Classification.COne.OrbRat6Lift
import VOA.Classification.COne.OrbRat6Sl2
import VOA.Classification.COne.OrbRat6Mult
import VOA.Classification.COne.OrbRat6Phi
import VOA.Classification.COne.OrbRat6V2
import VOA.Classification.COne.OrbRat6Top
import VOA.Classification.COne.OrbRat6Nine
import VOA.Classification.COne.OrbRat6Sigma
import VOA.Classification.COne.OrbRat6Twist
import VOA.Classification.COne.OrbRat6Sep
import VOA.Classification.COne.OrbRat6Cert
import VOA.Classification.COne.OrbRat6Heis
import VOA.Classification.COne.OrbRat7Assembly
import VOA.Classification.COne.OrbRat8Frame
import VOA.Classification.COne.OrbRat8Vir
import VOA.Classification.COne.OrbSpanGlue
import VOA.Classification.COne.OrbSpanUnitary
import VOA.Classification.COne.OrbSpanFock
import VOA.Classification.COne.OrbSpanLattice
import VOA.Classification.COne.OrbSpanConverse
import VOA.Classification.COne.OrbSpanTetra
import VOA.Classification.COne.OrbSpanMain
import VOA.Classification.COne.OrbPrimInvariant
import VOA.Classification.COne.OrbPrimGlue
import VOA.Classification.COne.OrbPrimUnitary
import VOA.Classification.COne.OrbPrimSpectrum
import VOA.Classification.COne.OrbPrimMain
import VOA.Classification.COne.OrbPrimMultiplet
import VOA.Classification.COne.OrbPrimTop
import VOA.Classification.COne.OrbPrimBinary
import VOA.Classification.COne.OrbPrimSix
import VOA.Classification.COne.OrbPrimEquiv
import VOA.Classification.COne.OrbB2Assembly
import VOA.Classification.COne.OrbC2hFinal
import VOA.Classification.COne.OrbOctaInvariant
import VOA.Classification.COne.OrbOctaGlue
import VOA.Classification.COne.OrbOctaSpan
import VOA.Classification.COne.OrbOctaMain
import VOA.Classification.COne.OrbA4Assembly
import VOA.Classification.COne.OrbXuBinary
import VOA.Classification.COne.OrbXuSpan
import VOA.Classification.COne.OrbXuRelations
import VOA.Classification.COne.OrbZhuTower
import VOA.Classification.COne.OrbZhuGraded
import VOA.Classification.COne.OrbZhuBound
import VOA.Classification.COne.OrbZhuSixteen
import VOA.Classification.COne.OrbZhuParity
import VOA.Classification.COne.OrbOddVir
import VOA.Classification.COne.OrbOddCert
import VOA.Classification.COne.OrbOddData1
import VOA.Classification.COne.OrbOddData2
import VOA.Classification.COne.OrbOddData3
import VOA.Classification.COne.OrbOddData4
import VOA.Classification.COne.OrbOddData5
import VOA.Classification.COne.OrbOddData6
import VOA.Classification.COne.OrbOddData7
import VOA.Classification.COne.OrbOddData8
import VOA.Classification.COne.OrbOddData9
import VOA.Classification.COne.OrbOddData10
import VOA.Classification.COne.OrbOddData11
import VOA.Classification.COne.OrbOddData12
import VOA.Classification.COne.OrbOddData13
import VOA.Classification.COne.OrbOddData14
import VOA.Classification.COne.OrbOddData15
import VOA.Classification.COne.OrbOddData16
import VOA.Classification.COne.OrbOddZhu
import VOA.Classification.COne.OrbOddChain
import VOA.Classification.COne.OrbOddPrim
import VOA.Classification.COne.OrbOddUV
import VOA.Classification.COne.OrbOddReduce
import VOA.Classification.COne.OrbOctaRCFinal
import VOA.Classification.COne.MainConverseB2
import VOA.Classification.COne.OrbB5Pairing
import VOA.Classification.COne.OrbB5Tetra
import VOA.Classification.COne.OrbB5Vacuum
import VOA.Classification.COne.OrbB5Main
import VOA.Classification.COne.OrbOctaZSpan
import VOA.Classification.COne.OrbOctaZPolynomial
import VOA.Classification.COne.OrbOctaZCandidate
import VOA.Classification.COne.OrbOctaZVacuum
import VOA.Classification.COne.OrbSglCws
import VOA.Classification.COne.OrbSglCwsDefs
import VOA.Classification.COne.OrbSglCwsSound
import VOA.Classification.COne.OrbSglData
import VOA.Classification.COne.OrbSglFock
import VOA.Classification.COne.OrbSglMain
import VOA.Classification.COne.OrbSglPrim
import VOA.Classification.COne.OrbSglSkE0
import VOA.Classification.COne.OrbSglSkE1
import VOA.Classification.COne.OrbSglSkE10
import VOA.Classification.COne.OrbSglSkE11
import VOA.Classification.COne.OrbSglSkE12
import VOA.Classification.COne.OrbSglSkE2
import VOA.Classification.COne.OrbSglSkE3
import VOA.Classification.COne.OrbSglSkE4
import VOA.Classification.COne.OrbSglSkE5
import VOA.Classification.COne.OrbSglSkE6
import VOA.Classification.COne.OrbSglSkE7
import VOA.Classification.COne.OrbSglSkE8
import VOA.Classification.COne.OrbSglSkE9
import VOA.Classification.COne.OrbSglSkJ0
import VOA.Classification.COne.OrbSglSkJ1
import VOA.Classification.COne.OrbSglSkJ10
import VOA.Classification.COne.OrbSglSkJ11
import VOA.Classification.COne.OrbSglSkJ12
import VOA.Classification.COne.OrbSglSkJ2
import VOA.Classification.COne.OrbSglSkJ3
import VOA.Classification.COne.OrbSglSkJ4
import VOA.Classification.COne.OrbSglSkJ5
import VOA.Classification.COne.OrbSglSkJ6
import VOA.Classification.COne.OrbSglSkJ7
import VOA.Classification.COne.OrbSglSkJ8
import VOA.Classification.COne.OrbSglSkJ9
import VOA.Classification.COne.OrbSglSkew
import VOA.Classification.COne.OrbSglTransport
import VOA.Classification.COne.OrbSglValues
import VOA.Classification.COne.OrbSglWords
import VOA.Classification.COne.OrbA4Rational
import VOA.Classification.COne.OrbSglSkE0a
import VOA.Classification.COne.OrbSglSkE1a
import VOA.Classification.COne.OrbSglSkJ0a
import VOA.Classification.COne.OrbSglSkSplit
import VOA.Classification.COne.OrbTopZhu
import VOA.Classification.COne.OrbOctaZCFinal
import VOA.Classification.COne.OrbMcRaeCover
import VOA.Classification.COne.OrbMcRaeMain
import VOA.Classification.COne.OrbIcoMain
import VOA.Classification.COne.OrbOctaZDFinal
import VOA.Classification.COne.McRaeM1Main
import VOA.Classification.COne.McRaeM2Swap
import VOA.Classification.COne.McRaeM2Exact

-- Gannon–Rayhaun c = 1 classification (VOA/Classification/COne) and the Huang track (VOA/Huang).
#print axioms VOA.Classification.COne.gannonRayhaun_current_final
#print axioms VOA.Classification.COne.virC1DegenerateCharacters_holds
#print axioms VOA.Classification.COne.virC1RadicalLevelBound_holds
#print axioms VOA.Classification.COne.gannonRayhaun_current_vir_free
#print axioms VOA.Classification.COne.gannonRayhaun_of_inputs
#print axioms VOA.Classification.COne.gannonRayhaun_main
#print axioms VOA.Classification.COne.iEnumeration
#print axioms VOA.Classification.COne.V2m_nice
#print axioms VOA.Classification.COne.V2m_stronglyRational
#print axioms VOA.Classification.COne.V2m_isSimple
#print axioms VOA.Classification.COne.V2m_c2Cofinite
#print axioms VOA.Classification.COne.V2m_admissiblyRational
#print axioms VOA.Classification.COne.existsUnique_weight_ne_zero
#print axioms VOA.Classification.COne.tannakian_squeeze
#print axioms VOA.Classification.COne.theta_weight_nonneg
#print axioms VOA.Classification.COne.FiniteRotation.classification
#print axioms VOA.Classification.COne.WeilGalois.thetaGaloisLaw
#print axioms VOA.Classification.COne.WeilGalois.weilKernelLaw
#print axioms VOA.Classification.COne.WeilGalois.gaussG_one
#print axioms VOA.Classification.COne.heisLatticeReconstruction
#print axioms VOA.Classification.COne.iDongMason_of_modData
#print axioms VOA.Classification.COne.heisCommutantTrivial_of_modData
#print axioms VOA.Classification.COne.virLocalCompositionSeries
#print axioms VOA.Classification.COne.exists_c1_singular
#print axioms VOA.Classification.COne.gapQExpansion
#print axioms VOA.Classification.COne.gapThetaReduction
#print axioms VOA.Classification.COne.V2Plus_iso_V8
#print axioms VOA.Classification.COne.orbifold_cyclic_iso
#print axioms VOA.Classification.COne.orbifold_dihedral_iso
#print axioms VOA.Classification.COne.aut_V2m_classify
#print axioms VOA.Classification.COne.gannonRayhaunDistinct_of_residuals
#print axioms VOA.Classification.COne.V2mPlus_one_nice
#print axioms VOA.Classification.COne.inCOneList_iff_exists_label
#print axioms VOA.Classification.COne.iSerreStark_of_theoremA
#print axioms VOA.Classification.COne.kac_determinant_eval
#print axioms VOA.Classification.COne.LatMod.latticeModule_iso_iff
#print axioms VOA.Huang.LatFus.fusionRule_latticeModule
#print axioms VOA.Classification.COne.exists_A5_subgroup
#print axioms VOA.Classification.COne.gannonRayhaun_current_huang
#print axioms VOA.Huang.IModDataReduced.iModData_of_reduced_inputs
#print axioms VOA.Huang.LWBottomRecovery.allBottomRecovers
#print axioms VOA.Huang.CardyPositivity.vacColumn_mem_K
#print axioms VOA.Classification.COne.gannonRayhaunDistinct
#print axioms VOA.Classification.COne.card_mul_finrank_orbifold
#print axioms VOA.Classification.COne.trace_charU
#print axioms VOA.Classification.COne.gannonRayhaun_current_verlinde
#print axioms VOA.Huang.VerlindeReduction.huangSInput_of_verlinde
#print axioms VOA.Huang.AndersonMoore.dlmRationalityInput_of_andersonMoore
#print axioms VOA.Huang.CongruenceGaloisSplit.iCongruenceGalois_of_split
#print axioms VOA.Classification.COne.gannonRayhaun_current_tannakian
#print axioms VOA.Huang.Tannakian.iTannakian_of_inputs
#print axioms VOA.Classification.COne.nice_of_hasCOneLabel_plus_of_factsGe2
#print axioms VOA.Classification.COne.gannonRayhaun_current_fusion
#print axioms VOA.Huang.VerlindeFusion.verlindeInput_of_fusion
#print axioms VOA.Huang.FusionTop.fusionRule_le_finrank_fzSpace
#print axioms VOA.Huang.VerlindeFusion.famFusion_vac
#print axioms VOA.Classification.COne.gannonRayhaun_current_fiber
#print axioms VOA.Huang.TensorCat.deligneTannakian_of_fiberFunctor
#print axioms VOA.Huang.TensorCat.symDim_simple_nat
#print axioms VOA.Huang.TensorCat.isZero_extPow_of_lt
#print axioms VOA.Classification.COne.gannonRayhaun_current_hecke
#print axioms VOA.Classification.COne.gannonRayhaun_current_ss24
#print axioms VOA.Classification.COne.SSHecke.iSerreStark24_of_boundedCoeff_of_squareClass
#print axioms VOA.Classification.COne.SSHecke.boundedCoeff_of_theoremA
#print axioms VOA.Classification.COne.SSHecke.squareClass_of_theoremA
#print axioms VOA.Classification.COne.gannonRayhaun_current_recon
#print axioms VOA.Huang.TensorCat.fiberFunctorReconstruction
#print axioms VOA.Classification.COne.gannonRayhaun_current_levelBox
#print axioms VOA.Classification.COne.SSHecke.levelBox_of_theoremA
#print axioms VOA.Classification.COne.SSHecke.squareClass_of_boundedCoeff_of_levelBox
#print axioms VOA.Huang.HuangODEContra.huangODEInput_of_moduleC2Input'
#print axioms VOA.Huang.HuangODEContra.contragredient_isIrreducible
#print axioms VOA.Classification.COne.v2mPlusC2CofiniteFactGe2_holds
#print axioms VOA.Classification.COne.V2mPlus_c2Cofinite
#print axioms VOA.Classification.COne.nice_of_hasCOneLabel_plus_of_rational_pseudoUnitary
#print axioms VOA.Huang.BuhlSpanning.moduleC2Input_holds
#print axioms VOA.Huang.ModuleC2.huangODEInput_holds
#print axioms VOA.Huang.ModuleC2.finiteDimensional_fusion_of_nice
#print axioms VOA.Classification.COne.v2mPlusPseudoUnitaryFactGe2_holds
#print axioms VOA.Classification.COne.V2mPlus_pseudoUnitary
#print axioms VOA.Classification.COne.nice_of_hasCOneLabel_plus_of_rational
#print axioms VOA.Classification.COne.gannonRayhaun_current_deligne
#print axioms VOA.Huang.TensorCat.DeligneFiber.deligneTannakian_holds
#print axioms VOA.Huang.TensorCat.DeligneFiber.symmetricFiberFunctorExists_holds
#print axioms VOA.Classification.COne.gannonRayhaun_latest
#print axioms VOA.Classification.COne.SSHecke.serreStarkLevelBox24
#print axioms VOA.Classification.COne.gannonRayhaun_qExp
#print axioms VOA.Classification.COne.SSHecke.boundedCoeff24_of_qExpPrinciple24
#print axioms VOA.Classification.COne.gannonRayhaun_latest_am
#print axioms VOA.Huang.AndersonMoore.andersonMooreInput_holds
#print axioms VOA.Classification.COne.gannonRayhaun_qExpAway
#print axioms VOA.Classification.COne.gannonRayhaun_latest_away
#print axioms VOA.Classification.COne.SSHecke.boundedCoeff24_of_away
#print axioms VOA.Huang.HuangODEIterPoint.productODEAtIterPoint_holds
#print axioms VOA.Huang.HuangODEIterPoint.prod_frobenius_expansion_holds
#print axioms VOA.Classification.COne.ABDWeakAdmissible.abdWeakIsAdmissible
#print axioms VOA.Classification.COne.AdmissibleOrdinary.dlmSimpleAdmissibleOrdinary_of_c2Cofinite
#print axioms VOA.Huang.PzTensorHatBridge.HLZ544_holds
#print axioms VOA.Huang.GenusOne.insertionSBlockCovariance_of_irreducible
#print axioms VOA.Huang.GenusOne.hasSum_trace_of_irreducible
#print axioms VOA.Huang.AssocConverse.productChannelFaithful_of_irredundant
#print axioms VOA.Huang.BraidingSkew.fusionRule_swap
#print axioms VOA.Huang.LiConverse.rawZhuBimoduleLaws
#print axioms VOA.Huang.LiRegular.scalarTopExtension_of_admissiblyRational
#print axioms VOA.Huang.FusionProduct.fusionProduct_factor
#print axioms VOA.Huang.TensorCat.tensorBifunctor
#print axioms VOA.Huang.GenusOne.Close.insertionSClosure_of_inputs
#print axioms VOA.Huang.LiRegular.insertionTopSurjectivity_of_stronglyRational
#print axioms VOA.Classification.COne.gannonRayhaun_eigen
#print axioms VOA.Huang.VerlindeVacuum.vacuumFusionInput
#print axioms VOA.Huang.VerlindeRho.squareBracketReflectionInput
#print axioms VOA.Huang.ATransform.fusionRule_atrans_eq
#print axioms VOA.Huang.TensorCat.monoidalCategoryOfStronglyRational_pbw
#print axioms VOA.Huang.TensorCat.HexagonClose.braidedCategory_stronglyRational_pbw
#print axioms VOA.Huang.TensorCat.HexagonClose.hexagonInput_pbw
#print axioms VOA.Huang.VerlindeTransport.genusZeroTransferInput_pbw
#print axioms VOA.Huang.VerlindeTransport.fusionEigenInput_of_genusOne
#print axioms VOA.Classification.COne.gannonRayhaun_genusOne
#print axioms VOA.Huang.FivePointSep.fivePointCoefficientGrowth_pbw
#print axioms VOA.Huang.GenusOneWard.productQSummable_holds
#print axioms VOA.Huang.GenusOneWard.rawCuspCoordinateCollection_holds
#print axioms VOA.Huang.GenusTwoPoint.Separate.normalizedSquareConjugation_holds
#print axioms VOA.Huang.TensorCat.BraidRibbon.twist_balance
#print axioms VOA.Classification.COne.PlusFiniteLength.cyclicFiniteLength_of_c2Cofinite
#print axioms VOA.Classification.COne.V2mPlus_cyclicFiniteLengthFactGe2
#print axioms VOA.finrank_zhu_le_finrank_c2Quotient
#print axioms VOA.Classification.COne.v2mPlusZhuDimensionBound_holds
#print axioms VOA.Classification.COne.PlusZhuNormalForms.zhu_mul_comm
#print axioms VOA.Classification.COne.rationality_of_twistedOmegaECharacters_cyclicLifts
#print axioms VOA.Classification.COne.gannonRayhaun_verlinde
#print axioms VOA.Classification.COne.huangVerlindeFusionInput_holds
#print axioms VOA.Huang.GenusOneG1f.fusionEigenInput_holds
#print axioms VOA.Classification.COne.gannonRayhaun_huang
#print axioms VOA.Huang.HuangModularity.huangRepInput_holds
#print axioms VOA.Huang.HuangRigid.rightRigid_ordinary
#print axioms VOA.Huang.HuangRigid.vacuumChannelTransportInput_holds
#print axioms VOA.Classification.COne.gannonRayhaun_hkl_two
#print axioms VOA.Huang.HKLExt.hklCFTTypeInput_holds
#print axioms VOA.Classification.COne.gannonRayhaun_hkl_rational
#print axioms VOA.Huang.HKLLoc.hklLocalityInput_holds
#print axioms VOA.Huang.DLNBridge.dln_inputs_of_NS_twist
#print axioms VOA.Huang.DLNBridge.dln_inputs_of_contracts
#print axioms VOA.Huang.DLNBridge.characterCovariance_of_zhu
#print axioms VOA.Huang.DLNBridge.zhuGaloisWord_of_twist
#print axioms VOA.Classification.COne.SSHecke.qExpPrinciple24Away_two_of_slash_and_sturmMatching
#print axioms VOA.Classification.COne.SSHecke.fullLevelWeightTwoJetSeparation_sturm
#print axioms VOA.Huang.DLNLifting.matrixDLNLifting_of_relativeCommutator
#print axioms VOA.Huang.DLNLifting.det_pow_twelve
#print axioms VOA.Huang.DLNLifting.gamma_twelve_le_commutator
#print axioms VOA.Huang.DLNLifting.zhuCongruence_of_relativeCommutatorSome
#print axioms VOA.Huang.DLNLifting.relativeCommutator_finiteIndex
#print axioms VOA.Huang.DLNLifting.relativeCommutatorCongruenceSome_iff_centralCongruenceSL2
#print axioms VOA.Huang.DLNBridge.dln_inputs_of_coreResiduals
#print axioms VOA.Huang.NSCongruence.mixedTwistIdentity_holds
#print axioms VOA.Huang.NSCongruence.mixedTMove_holds
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_coreResiduals
#print axioms VOA.Huang.DLNBridge.zhuProjectiveCongruence_of_NSKernel
#print axioms VOA.Classification.COne.SSHecke.fullLevelWeightOneSlash24_of_thetaFourier
#print axioms VOA.Classification.COne.SSHecke.qExpPrinciple24Away_two_of_thetaFourier_and_sturmMatching
#print axioms VOA.Huang.DLNBridge.dln_inputs_of_nonzeroResiduals
#print axioms VOA.Huang.NSCongruence.mixedBaseSMove_holds
#print axioms VOA.Huang.NSCongruence.mixedZeroIndicatorValue_holds
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_nonzeroResiduals
#print axioms VOA.Classification.COne.SSHecke.weightOneThetaFourier24
#print axioms VOA.Classification.COne.SSHecke.fullLevelWeightOneSlash24
#print axioms VOA.Classification.COne.SSHecke.qExpPrinciple24Away_two_of_sturmMatching
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_nonzeroSMove
#print axioms VOA.Huang.NSCongruence.mixedSCyclotomic_iff_dimensions
#print axioms VOA.Classification.COne.SSHecke.qExpPrinciple24Away_two_of_eventualProductSpan
#print axioms VOA.Classification.COne.SSHecke.exists_int_lattice_of_restriction_mem_products
#print axioms VOA.Huang.ZhuRep.zhuModularRepresentationInput_holds
#print axioms VOA.Huang.ZhuRep.zhuGaloisTwistInput_of_NS
#print axioms VOA.Huang.ZhuRep.dln_inputs_of_categorical
#print axioms VOA.Huang.ZhuRep.star_S_eq_of_balancing
#print axioms VOA.Huang.NSCongruence.mixedUnitSMove_holds
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_sameSignOffDiagonal
#print axioms VOA.Huang.NSGalois.dln_inputs_of_core
#print axioms VOA.Huang.NSGalois.galois_signed
#print axioms VOA.Huang.NSGalois.exists_ringEquiv_pow
#print axioms VOA.Huang.NSGalois.nsGaloisTwistAll_of_core
#print axioms VOA.Huang.NSCongruence.mixedNonzeroSMove_of_diagrams
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_mixedDiagrams
#print axioms VOA.Huang.NSCongruence.mixed_indicator_one_two_value
#print axioms VOA.Huang.NSGaloisCore.dln_inputs_of_SMove_lifting
#print axioms VOA.Huang.NSGaloisCore.nsGaloisTwistAll_of_SMove
#print axioms VOA.Huang.NSGaloisCore.galoisTwistCore_of_SMove_lift
#print axioms VOA.Huang.NSCongruence.mixedFusionMoment_holds
#print axioms VOA.Huang.NSCongruence.inverseTwoBlockTrace_diagonal
#print axioms VOA.Huang.DLNBeyl.reduction_surjective
#print axioms VOA.Huang.DLNBeyl.sl_crt_bijective
#print axioms VOA.Huang.DLNBeyl.matrixDLNLifting_of_local
#print axioms VOA.Huang.DLNBeyl.relativeCommutatorCongruence_of_beyl
#print axioms VOA.Huang.NSCongruence.inverseTwoBlockTrace
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_forward_exchange
#print axioms VOA.Huang.NSCongruence.mixedTwoBlockTraceFormula_holds
#print axioms VOA.Huang.NSCongruence.forwardTwoBlockTrace
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_mugerExchange
#print axioms VOA.Classification.COne.gannonRayhaun_hkl_dim
#print axioms VOA.Huang.HKLRational.hklRationalInput_of_dim
#print axioms VOA.Huang.HKLRational.hklActionAssocInput_holds
#print axioms VOA.Huang.HKLRational.exists_linear_retraction_of_frobenius
#print axioms VOA.Huang.HKLRational.assoc_series_eq
#print axioms VOA.Classification.COne.gannonRayhaun_hkl_final
#print axioms VOA.Huang.HKLRational.hklRationalInput_holds
#print axioms VOA.Huang.HKLRational.hklFrobeniusDimInput_holds
#print axioms VOA.Huang.HKLRational.twistPivotal_trL_id_frobenius
#print axioms VOA.Huang.NSCongruence.mixedMugerExchange_iff_loopTranspose
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_loopTranspose
#print axioms VOA.Huang.NSCongruence.mixedScalarLoopTranspose_holds
#print axioms VOA.Huang.NSCongruence.mixedLoopTranspose_of_simple_dual_products
#print axioms VOA.Huang.NSCongruence.mixedLoopTranspose_iff_twistChannelCancellation
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_of_twistChannelCancellation
#print axioms VOA.Huang.DLNSchur.schurTrivial_SL_two
#print axioms VOA.Huang.DLNSchur.twoPowerInflation_one
#print axioms VOA.Huang.DLNSchur.matrixDLNLifting_of_remaining
#print axioms VOA.Classification.COne.gannonRayhaun_hkl_qexp
#print axioms VOA.Classification.COne.SSHecke.qExpPrinciple24Away_two
#print axioms VOA.Classification.COne.SSHecke.fullLevel_coeff_awaySat
#print axioms VOA.Classification.COne.SSHecke.serreStarkBoundedCoeff24_holds
#print axioms VOA.Huang.DLNSchur.commutator_SL_primePower_eq_top
#print axioms VOA.Huang.DLNSchur.matrixDLNLifting_of_rootRelations
#print axioms VOA.Huang.DLNSchur.largePrimeRootRelations_iff_gaussLowerRelations
#print axioms VOA.Huang.DLNSchur.lower_five_mod_twentyFive_not_bruhat
#print axioms VOA.Classification.COne.gannonRayhaun_beyl
#print axioms VOA.Classification.COne.gannonRayhaun_beyl_fine
#print axioms VOA.Huang.NSGaloisCore.dln_inputs_of_beyl
#print axioms VOA.Huang.DLNBridge.nsProjectiveKernelAll_holds
#print axioms VOA.Huang.NSCongruence.mixedNonzeroSMove_holds
#print axioms VOA.Huang.NSCongruence.mixedTwistChannelCancellation_holds
#print axioms VOA.Huang.DLNSchur.largePrimeGaussLowerRelations_iff_generator_and_boundary
#print axioms VOA.Huang.DLNSchur.torusDefect_square_primePower
#print axioms VOA.Huang.DLNSchur.schurTrivial_SL_prime_mod_four_one
#print axioms VOA.Huang.DLNSchur.largePrimeRootRelations_iff_mod_four_three_and_higher_boundary
#print axioms VOA.Classification.COne.gannonRayhaun_beyl_large
#print axioms VOA.Huang.DLNSchur.threePowerSchur
#print axioms VOA.Huang.DLNSchur.twoPowerInflationFromTwo_holds
#print axioms VOA.Huang.DLNSchur.twoPowerInflation_holds
#print axioms VOA.Huang.DLNSchur.oddPrimePowerSchur_iff_largePrimeGaussLowerRelations
#print axioms VOA.Classification.COne.gannonRayhaun_forward
#print axioms VOA.Huang.DLNSchur.largePrimeGaussLowerRelations
#print axioms VOA.Huang.DLNSchur.schurTrivial_SL_primePower_large
#print axioms VOA.Classification.COne.OrbRat.V2mPlus_stronglyFinite
#print axioms VOA.Classification.COne.OrbRat.admissiblyRational_iff_resonantWholeSplitting
#print axioms VOA.Classification.COne.OrbRat.gannonRayhaunConverse_of_orbifoldRational
#print axioms VOA.Classification.COne.OrbPos2.exceptionalOrbifoldPositiveWeightsFact_of_drx_li
#print axioms VOA.Classification.COne.OrbPos2.innerEnergy_gap
#print axioms VOA.Classification.COne.OrbPos3.exceptionalOrbifoldPositiveWeightsFact_of_drx_untwist
#print axioms VOA.Classification.COne.OrbPos.exceptionalOrbifoldPositiveWeightsFact_of_residuals
#print axioms VOA.Classification.COne.PlusRatSign.V2mPlus_stronglyRational_prime
#print axioms VOA.Classification.COne.PlusRatSign.V2mPlus_admissiblyRational_two
#print axioms VOA.Classification.COne.rationality_of_remainingAfterVacuumSign
#print axioms VOA.Classification.COne.OrbPos4.no_integral_gluing_shift
#print axioms VOA.Classification.COne.PlusRat2.V2mPlus_stronglyRational_four
#print axioms VOA.Classification.COne.PlusRat2.vacuum_sign_both_all
#print axioms VOA.Classification.COne.PlusRat2Dual.pairSplit_swap
#print axioms VOA.Classification.COne.OrbPos5.latticeShiftedTwistedModule
#print axioms VOA.Classification.COne.OrbPos7.latticeShiftedTwistedModule
#print axioms VOA.Classification.COne.OrbPos7.shiftedJacobi
#print axioms VOA.Classification.COne.OrbPos7.latticeShiftedTwistedModule_energyRealization
#print axioms VOA.Classification.COne.OrbPos6.chargedProductFormula
#print axioms VOA.Classification.COne.OrbPos8.exceptionalOrbifoldPositiveWeightsFact_of_drx
#print axioms VOA.Classification.COne.OrbPos8.inner_twisted_weight_gap
#print axioms VOA.Classification.COne.OrbPos8.finite_order_twisted_lowest_matches_constructed
#print axioms VOA.Classification.COne.OrbPos9.exceptionalExtensionAlgebraExists
#print axioms VOA.Classification.COne.OrbPos9.exceptionalOrbifoldPositiveWeightsFact_of_simple_targets_twisted
#print axioms VOA.Classification.COne.PlusRat3.V2mPlus_stronglyRational_six
#print axioms VOA.Classification.COne.PlusRat3.V2mPlus_stronglyRational_eight
#print axioms VOA.Classification.COne.PlusRat3.pairSplitting_charged_gap_one_both
#print axioms VOA.Classification.COne.OrbPos10.exceptionalFreeSimpleTargets
#print axioms VOA.Classification.COne.OrbPos10.exceptionalOrbifoldPositiveWeightsFact_of_simpleActionTwisted
#print axioms VOA.Classification.COne.OrbPos11.exceptionalOrbifoldPositiveWeightsFact_of_projections_jacobi
#print axioms VOA.Classification.COne.OrbPos12.exceptionalOrbifoldPositiveWeightsFact_of_projections_awayFixed
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_nine
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_ten
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_twelve
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_fourteen
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_fifteen
#print axioms VOA.Classification.COne.PlusRat4.pairSplitting_charged_gap_two
#print axioms VOA.Classification.COne.OrbC2b.klein_iso_plus_four
#print axioms VOA.Classification.COne.OrbC2b.klein_stronglyRational
#print axioms VOA.Classification.COne.OrbC2b.solvableExceptionalOrbifoldC2Fact_of_tower
#print axioms VOA.Classification.COne.OrbC2.solvableExceptionalOrbifoldC2Fact_iff_movingPairs
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_of_not_four_dvd
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_upTo100
#print axioms VOA.Classification.COne.rationality_of_twistedKernel
#print axioms VOA.Classification.COne.OrbC2d.tetrahedralConjugacy
#print axioms VOA.Classification.COne.OrbC2d.octahedralConjugacy
#print axioms VOA.Classification.COne.v2mPlusRationalFactGe2_holds
#print axioms VOA.Classification.COne.V2mPlus_stronglyRational_all
#print axioms VOA.Classification.COne.V2mPlus_nice
#print axioms VOA.Classification.COne.gannonRayhaunConverse_of_exceptional
#print axioms VOA.Classification.COne.twistedKernelPairs_holds
#print axioms VOA.Classification.COne.OrbRat2.gannonRayhaunConverse_of_cyclic
#print axioms VOA.Classification.COne.OrbRat2.cubicModel_admissiblyRational_of_reduced
#print axioms VOA.Classification.COne.OrbRat2.admissiblyRational_of_charTable_pairs
#print axioms VOA.Classification.COne.OrbC2f.plus_cubic_tetra_iso
#print axioms VOA.Classification.COne.OrbC2Fix.tetra_c2Cofinite_of_dongJiang_corrected
#print axioms VOA.Classification.COne.OrbC2g.printedLeading_twenty_eq_thirteenth
#print axioms VOA.PreVertexAlgebra.exists_isCommutativeVA_not_trivial
#print axioms VOA.VertexOperatorAlgebra.old_isCommutative_iff_trivial
#print axioms VOA.fusionCoeffFHL_eq_fusionRule
#print axioms VOA.fusionCoeffFHL_adjoint_self
#print axioms VOA.fusionCoeff_ne_fusionCoeffFHL
#print axioms VOA.unitaryVOADL_trivial
#print axioms VOA.old_unitary_isEmpty
#print axioms VOA.Classification.COne.OrbRat3.telescope_V8
#print axioms VOA.Classification.COne.OrbRat3.outer_5
#print axioms VOA.Classification.COne.OrbRat3.cubicVacuumTelescope_of_zhu
#print axioms VOA.Classification.COne.OrbRat3.cubic_pair_one_zero_of_zhu
#print axioms VOA.Classification.COne.OrbRat3.cubicModel_admissiblyRational_of_zhu
#print axioms VOA.Classification.COne.OrbRat3.cubicSign
#print axioms VOA.Classification.COne.OrbRat3.actU_sound
#print axioms VOA.Classification.COne.OrbRat4.v8OuterCertificates_holds
#print axioms VOA.Classification.COne.OrbRat4.telescope_V8_holds
#print axioms VOA.Classification.COne.OrbRat4.cubicVacuumTelescope_of_zhu
#print axioms VOA.Classification.COne.OrbRat4.cubic_pair_one_zero_of_zhu
#print axioms VOA.Classification.COne.OrbRat4.cubicModel_admissiblyRational_of_zhu
#print axioms VOA.Classification.COne.OrbRat4.cubicModelRationalOfC2_of_zhu
#print axioms VOA.Classification.COne.OrbRat4.bucket_eq_of_eval
#print axioms VOA.Classification.COne.OrbRat5.cubicZhuCharacterTable_iff
#print axioms VOA.Classification.COne.OrbRat5.cubicDoubledPair_four
#print axioms VOA.Classification.COne.OrbRat5.cubicZhuCharacterTable_of_remaining
#print axioms VOA.Classification.COne.OrbRat5.cubic_five_characters
#print axioms VOA.Classification.COne.OrbRat5.exists_character_of_top_line
#print axioms VOA.Classification.COne.OrbRat5.U_eight_J
#print axioms VOA.Classification.COne.OrbRat5.eigen_line
#print axioms VOA.Classification.COne.OrbRat6.cubicDoubledPair_nine_four
#print axioms VOA.Classification.COne.OrbRat6.cubicTwistedDoubledPairs_holds
#print axioms VOA.Classification.COne.OrbRat6.cubicZhuCharacterTable_holds
#print axioms VOA.Classification.COne.OrbRat6.heisenbergTopSeparation
#print axioms VOA.Classification.COne.OrbRat6.sig_conj
#print axioms VOA.Classification.COne.OrbRat6.iotaW_hom
#print axioms VOA.Classification.COne.OrbRat6.phi_mode
#print axioms VOA.Classification.COne.OrbRat7.cubicVacuumTelescope_of_dim
#print axioms VOA.Classification.COne.OrbRat7.cubicModelRationalOfC2_of_dim
#print axioms VOA.Classification.COne.OrbRat8.pairSplit_of_topCyclicVanishing
#print axioms VOA.Classification.COne.OrbRat8.cubic_singular_eq_zero
#print axioms VOA.Classification.COne.OrbRat8.cubic_low_transfer
#print axioms VOA.Classification.COne.OrbRat8.cubicNonVacuumPairs_of_residuals
#print axioms VOA.Classification.COne.OrbRat8.cubicModelRationalOfC2_of_residuals
#print axioms VOA.Classification.COne.OrbRat8.cert_S
#print axioms VOA.Classification.COne.OrbSpan.tetrahedralVirasoroSpan_iff_primaryReduction
#print axioms VOA.Classification.COne.OrbSpan.tetra_c2Cofinite_of_primaryReduction
#print axioms VOA.Classification.COne.OrbSpan.latticeVirUnitary
#print axioms VOA.Classification.COne.OrbSpan.v2VirUnitary_holds
#print axioms VOA.Classification.COne.OrbSpan.virPrimaryDecomp_orbifold
#print axioms VOA.Classification.COne.OrbSpan.tetraPrimaryDecomp
#print axioms VOA.Classification.COne.OrbSpan.dongJiangVirasoroSpan_iff_primary
#print axioms VOA.Classification.COne.OrbPrim.tetraPrimaryReduction_holds
#print axioms VOA.Classification.COne.OrbPrim.tetrahedralVirasoroSpan_holds
#print axioms VOA.Classification.COne.OrbPrim.tetra_c2Cofinite_of_relations
#print axioms VOA.Classification.COne.OrbPrim.mem_adjoin_of_isA4Inv
#print axioms VOA.Classification.COne.OrbPrim.finrank_prim_V2_sq
#print axioms VOA.Classification.COne.OrbPrim.finrank_prim_le_of_unitary
#print axioms VOA.Classification.COne.OrbPrim.T2_equivariant
#print axioms VOA.Classification.COne.OrbPrim.six_T2
#print axioms VOA.Classification.COne.OrbB2.solvableExceptionalOrbifoldC2Fact_of_two_inputs
#print axioms VOA.Classification.COne.OrbC2h.not_cubicSeedRemainders
#print axioms VOA.Classification.COne.OrbC2h.cubicSeedRemaindersCorrected
#print axioms VOA.Classification.COne.OrbC2h.tetrahedralModeDecomposition
#print axioms VOA.Classification.COne.OrbC2h.tetrahedralDongJiangRelations
#print axioms VOA.Classification.COne.OrbC2h.weight20_probe
#print axioms VOA.Classification.COne.OrbC2h.weight22_probe
#print axioms VOA.Classification.COne.OrbB2.solvableExceptionalOrbifoldC2Fact_of_involution
#print axioms VOA.Classification.COne.OrbOcta.octaConformalTowerSpan_holds
#print axioms VOA.Classification.COne.OrbOcta.octahedralConformalNilpotent_iff_c2
#print axioms VOA.Classification.COne.OrbOcta.involutionMovingPairSpan_of_octahedralConformalNilpotent
#print axioms VOA.Classification.COne.OrbOcta.octahedralConformalNilpotent_of_quadratic
#print axioms VOA.Classification.COne.OrbOcta.mem_span_evenMon
#print axioms VOA.Classification.COne.OrbA4.tetra_c2Cofinite_holds
#print axioms VOA.Classification.COne.OrbA4.cubicModel_c2Cofinite_holds
#print axioms VOA.Classification.COne.OrbA4.solvableExceptionalOrbifoldC2Fact_of_octaNilpotent
#print axioms VOA.Classification.COne.OrbA4.cubicModel_admissiblyRational_of_residuals
#print axioms VOA.Classification.COne.OrbXu.xuBinaryChannelIdentities_holds
#print axioms VOA.Classification.COne.OrbXu.binary_channels_nonzero
#print axioms VOA.Classification.COne.OrbXu.klein_relation
#print axioms VOA.Classification.COne.OrbXu.orbifold_twoTowers_iff_primary
#print axioms VOA.Classification.COne.OrbXu.xuIcosahedralPoissonRelations_iff_primaryAndSymbols
#print axioms VOA.Classification.COne.OrbXu.icosa_c2_of_primaryAndSymbols
#print axioms VOA.Classification.COne.OrbZhu.cubicZhuDimensionBound_of_annihilator
#print axioms VOA.Classification.COne.OrbZhu.cubicModel_admissiblyRational_of_oddRelation
#print axioms VOA.Classification.COne.OrbZhu.tetraSixteenTruncation_holds
#print axioms VOA.Classification.COne.OrbZhu.finrank_A_le_of_towers
#print axioms VOA.Classification.COne.OrbZhu.q13_omega_eq_zero
#print axioms VOA.Classification.COne.OrbOdd.tetra_uv_zhu
#print axioms VOA.Classification.COne.OrbOdd.tetraOddAnnihilator_of_singleValues
#print axioms VOA.Classification.COne.OrbOdd.cubicZhuDimensionBound_of_singleValues
#print axioms VOA.Classification.COne.OrbOdd.chain_main
#print axioms VOA.Classification.COne.OrbOdd.odd_prim
#print axioms VOA.Classification.COne.solvableExceptionalOrbifoldC2Fact_holds
#print axioms VOA.Classification.COne.OrbOcta.octahedralConformalNilpotent_holds
#print axioms VOA.Classification.COne.OrbOcta.involutionMovingPairSpan_holds
#print axioms VOA.Classification.COne.OrbOctaRC.conformal_power25_zero
#print axioms VOA.Classification.COne.gannonRayhaunConverse_of_B3_B4_B5
#print axioms VOA.Classification.COne.OrbB5.tetra_pseudoUnitary
#print axioms VOA.Classification.COne.OrbB5.tetrahedral_orbifold_pseudoUnitary
#print axioms VOA.Classification.COne.OrbB5.exceptionalOrbifoldPositiveWeightsFact_of_octa_icosa
#print axioms VOA.Classification.COne.OrbB5.exceptionalOrbifoldPositiveWeightsFact_iff_octa_icosa
#print axioms VOA.Classification.COne.OrbOctaZ.octa_zhu_finite
#print axioms VOA.Classification.COne.OrbOctaZ.octa_pseudoUnitary_of_zhu_fiber
#print axioms VOA.Classification.COne.OrbOctaZ.finrank_le_121_of_zhu_fiber
#print axioms VOA.Classification.COne.OrbOctaZ.vacuum_of_lowest_zero
#print axioms VOA.Classification.COne.OrbSgl.tetraOddSingleValues_holds
#print axioms VOA.Classification.COne.OrbSgl.tetraOddAnnihilator_holds
#print axioms VOA.Classification.COne.OrbSgl.cubicZhuDimensionBound_holds
#print axioms VOA.Classification.COne.OrbSgl.nine_smul_wsP
#print axioms VOA.Classification.COne.OrbA4.cubicModel_admissiblyRational_of_topCyclic
#print axioms VOA.Classification.COne.OrbTop.cubicModel_zhuAlgEquiv
#print axioms VOA.Classification.COne.OrbTop.cubicModel_zhuSemisimple
#print axioms VOA.Classification.COne.OrbTop.cubicModel_stronglyFinite
#print axioms VOA.Classification.COne.OrbTop.cubicModel_admissiblyRational_iff_resonant
#print axioms VOA.Classification.COne.OrbTop.cubicModel_admissiblyRational_of_zhuCriterion
#print axioms VOA.Classification.COne.OrbOctaZC.OctahedralConformalZhuRelation_holds
#print axioms VOA.Classification.COne.OrbOctaZC.q24_seed_one
#print axioms VOA.Classification.COne.OrbOctaZC.octa_zhu_finrank_le_124
#print axioms VOA.Classification.COne.OrbOctaZC.vacuumFiber_iff_three_Q24
#print axioms VOA.Classification.COne.OrbOctaZC.octa_pseudoUnitary_of_three_Q24
#print axioms VOA.Classification.COne.OrbMcRae.admissiblyRational_of_mcRaeCover
#print axioms VOA.Classification.COne.OrbMcRae.mcRaeCoverFact_iff_admissiblyRational
#print axioms VOA.Classification.COne.OrbMcRae.mcRaeCoverFact_of_huang_unimodular
#print axioms VOA.Classification.COne.OrbMcRae.zhuSemisimpleRationalityFact_iff_mcRaeCategorical
#print axioms VOA.Classification.COne.OrbMcRae.cubicModel_admissiblyRational_iff_mcRaeCover
#print axioms VOA.Classification.COne.OrbMcRae.gannonRayhaunConverse_of_mcRaeCategorical
#print axioms VOA.Classification.COne.OrbIco.icosaPrimaryReduction_holds
#print axioms VOA.Classification.COne.OrbIco.icosa_twoTowers_holds
#print axioms VOA.Classification.COne.OrbIco.icosahedralConjugacy
#print axioms VOA.Classification.COne.OrbIco.icoInvariantSpan
#print axioms VOA.Classification.COne.OrbIco.xuIcosahedralPoissonRelations_of_symbols
#print axioms VOA.Classification.COne.OrbIco.icosa_c2_of_symbols
#print axioms VOA.Classification.COne.OrbOctaZD.OctahedralVacuumFiber_holds
#print axioms VOA.Classification.COne.OrbOctaZD.octa_pseudoUnitary_holds
#print axioms VOA.Classification.COne.OrbOctaZD.octa_zhu_finrank_le_121
#print axioms VOA.Classification.COne.OrbOctaZD.exceptionalOrbifoldPositiveWeightsFact_of_icosa
#print axioms VOA.Classification.COne.McRaeM1.huangCoverFact_of_c2
#print axioms VOA.Classification.COne.McRaeM1.mcRaeCoverFact_of_unimodularSocle
#print axioms VOA.Classification.COne.McRaeM1.admissiblyRational_of_unimodularSocle
#print axioms VOA.Classification.COne.McRaeM1.cubicModel_admissiblyRational_of_unimodularSocle
#print axioms VOA.Classification.COne.McRaeM2.unimodularSocleFact_iff_admissiblyRational
#print axioms VOA.C2Rigid.unimodularSocleFact_of_coverDualLit
#print axioms VOA.C2Rigid.coverDualLit_iff_admissiblyRational
#print axioms VOA.C2Rigid.iota_bijective
#print axioms VOA.C2Rigid.injHull_of_cover

#print axioms VOA.LogVModule.mode_mem_weight

#print axioms VOA.LogVModule.toGW

#print axioms VOA.LogTensor.Contra.L1_locallyNilpotent

#print axioms VOA.LogTensor.Contra.L0nil_locallyNilpotent

#print axioms VOA.LogTensor.Contra.nilExp

#print axioms VOA.LogTensor.Contra.L0nil_comm_mode

#print axioms VOA.LogTensor.Contra.nilExpHom

#print axioms VOA.LogTensor.Pz.evaluateOne_injective

#print axioms VOA.LogTensor.Pz.logCoeff_eq_defect_pow

#print axioms VOA.LogTensor.Pz.CompatibleSpace.weakModule

#print axioms VOA.LogTensor.Pz.maximalWeakModule

#print axioms VOA.Classification.COne.OrbIcoV.neutralProbe_Xico_ne_zero

#print axioms VOA.Classification.COne.OrbIcoV.measurement_determinant_ne_zero

#print axioms VOA.Classification.COne.OrbIcoV.vacuum_null_equation

#print axioms VOA.Classification.COne.OrbIcoV.sixth_null_equation

#print axioms VOA.Classification.COne.OrbIcoZ.s13_zero

#print axioms VOA.Classification.COne.OrbIcoZ.self_top_nonzero

#print axioms VOA.Classification.COne.OrbIcoZ.self_top_Zhu_nonzero

#print axioms VOA.Classification.COne.OrbIcoZ.low_mode67

#print axioms VOA.C2Rigid.LocalInjective.extend_one

#print axioms VOA.C2Rigid.LocalInjective.extend_submodule

#print axioms VOA.Classification.COne.OrbIcoV.canonical_weight74_remainder

#print axioms VOA.Classification.COne.OrbIcoV.canonical_weight76_remainder

#print axioms VOA.LogTensor.Contra.L0exp

#print axioms VOA.LogTensor.Contra.L0exp_add

#print axioms VOA.LogTensor.Contra.oppositeCoordinate

#print axioms VOA.C2Rigid.LocalInjective.embed_of_essential_submodule

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_of_essential_embedding

#print axioms VOA.C2Rigid.LocalInjective.exists_atom_le

#print axioms VOA.C2Rigid.LocalInjective.socle_essential_weak

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_of_socle_embedding

#print axioms VOA.Classification.COne.OrbIcoZ.icoVacuumFiber_holds

#print axioms VOA.Classification.COne.OrbIcoZ.ico_vacuum_of_lowest_zero

#print axioms VOA.LogTensor.Pz.compatibleLogModes_isLogIntertwining

#print axioms VOA.LogTensor.Pz.reconstruction_injective

#print axioms VOA.LogTensor.Pz.finiteDimensional_compatibleMaps_of_c2Cofinite

#print axioms VOA.LogTensor.Pz.finiteDimensional_maximalHomSpace_of_c2Cofinite

#print axioms VOA.C2Rigid.LocalInjective.modeMap_fg_of_finGen

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_socle_of_finite_hom

#print axioms VOA.Classification.COne.OrbIcoV.s13_leading_coefficient

#print axioms VOA.Classification.COne.OrbIcoV.vacuum_channel_positive_rigidity

#print axioms VOA.Classification.COne.OrbIcoV.sixth_channel_positive_rigidity

#print axioms VOA.C2Rigid.LocalInjective.simple_of_weak_irreducible

#print axioms VOA.C2Rigid.LocalInjective.canonical_simple_coverage

#print axioms VOA.C2Rigid.LocalInjective.canonical_simple_finGen

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_socle_of_canonical_hom

#print axioms VOA.C2Rigid.Restriction.finiteLength_restricted_submodule

#print axioms VOA.C2Rigid.LocalInjective.finite_injective_embedding

#print axioms VOA.LogTensor.Pz.finiteDimensional_maximalHomSpace_from_simple

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_maximal_of_finitePhi

#print axioms VOA.C2Rigid.LocalInjective.finiteLength_maximal_of_semisimpleZhu

#print axioms VOA.C2Rigid.LocalInjective.maximalLogModule

#print axioms VOA.C2Rigid.LocalInjective.tensorModule

#print axioms VOA.C2Rigid.LocalInjective.tensorIntertwiner

#print axioms VOA.C2Rigid.LocalInjective.tensorIntertwiner_ne_zero

#print axioms VOA.LogTensor.ModuleC2.quotient_exact

#print axioms VOA.LogTensor.ModuleC2.cofinite_of_exact

#print axioms VOA.LogTensor.ModuleC2.cofinite_of_finiteLength

#print axioms VOA.LogTensor.ModuleC2.cofinite_of_finGen

#print axioms VOA.LogTensor.ModuleC2.C1_cofinite_of_finiteLength

#print axioms VOA.LogTensor.ModuleC2.C1_cofinite_of_finGen

#print axioms VOA.LogTensor.Contra.L0nil_isNilpotent_of_finGen

#print axioms VOA.LogTensor.ModuleC2.weightProj_mem_C1
#print axioms VOA.LogTensor.ModuleC2.exists_finite_C1_weights
#print axioms VOA.LogTensor.ModuleC2.C1_generalized_weight_cutoff
#print axioms VOA.LogTensor.Pz.CompatibleMap.toMaximalHom
#print axioms VOA.LogTensor.precompose
#print axioms VOA.Classification.COne.OrbIcoV.family_fock_image_bound
#print axioms VOA.Classification.COne.OrbIcoV.vacuum_fock_image_bound
#print axioms VOA.Classification.COne.OrbIcoV.vacuum_ward_sequence_unique
#print axioms VOA.Classification.COne.OrbIcoV.sixth_ward_sequence_unique
#print axioms VOA.Classification.COne.OrbIcoV.vacuumState_positive
#print axioms VOA.Classification.COne.OrbIcoV.sixthState_positive
#print axioms VOA.C2Rigid.LocalInjective.tensorFactor_comp_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensorPostcompose_injective
#print axioms VOA.C2Rigid.LocalInjective.tensorRepresentingEquiv
#print axioms VOA.C2Rigid.LocalInjective.tensorMap_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensorMap_identity
#print axioms VOA.C2Rigid.LocalInjective.tensorMap_composition

#print axioms VOA.Classification.COne.OrbIcoZ.icosahedral_standardIso
#print axioms VOA.Classification.COne.OrbIcoZ.icosahedral_pseudoUnitary_of_standard

#print axioms VOA.LogTensor.Contra.hom_L0nil
#print axioms VOA.LogTensor.Contra.hom_L0exp
#print axioms VOA.LogTensor.Contra.twistHom
#print axioms VOA.LogTensor.Contra.twist_natural
#print axioms VOA.LogTensor.vacuumIntertwinerEquiv
#print axioms VOA.C2Rigid.LocalInjective.tensorLeftUnitEquiv
#print axioms VOA.C2Rigid.LocalInjective.tensorLeftUnit_hom_inv
#print axioms VOA.C2Rigid.LocalInjective.tensorLeftUnit_inv_hom

#print axioms VOA.LogTensor.uniform_log_degree_of_jordan
#print axioms VOA.LogTensor.uniform_log_degree_of_finGen
#print axioms VOA.C2Rigid.LocalInjective.tensorModule_finiteLength
#print axioms VOA.C2Rigid.LocalInjective.tensorModule_finGen
#print axioms VOA.C2Rigid.LocalInjective.tensorModule_C2_cofinite
#print axioms VOA.C2Rigid.LocalInjective.tensorModule_C1_cutoff
#print axioms VOA.C2Rigid.LocalInjective.tensorModule_uniformJordan

#print axioms VOA.Classification.COne.OrbIcoZ.candidate_lowest_root
#print axioms VOA.Classification.COne.OrbIcoZ.ico_lowest_zero_or_positive
#print axioms VOA.Classification.COne.OrbIcoZ.ico_pseudoUnitary_holds
#print axioms VOA.Classification.COne.OrbIcoZ.icosahedral_orbifold_pseudoUnitary
#print axioms VOA.Classification.COne.OrbIcoZ.exceptionalOrbifoldPositiveWeightsFact_holds
#print axioms VOA.Classification.COne.gannonRayhaunConverse_of_B3_B4
#print axioms VOA.LogTensor.omega_postcompose
#print axioms VOA.LogTensor.omega_precompose
#print axioms VOA.LogTensor.ModuleC2.c1Part_eq_inf
#print axioms VOA.LogTensor.ModuleC2.c1Part_generalized_cutoff
#print axioms VOA.Huang.LogHuangODEModes.logCoefficient_isJacobi
#print axioms VOA.Huang.LogHuangODEModes.prod_slot1
#print axioms VOA.Huang.LogHuangODEModes.prod_slot2
#print axioms VOA.Huang.LogHuangODEModes.prod_slot3
#print axioms VOA.C2Rigid.LocalInjective.tensorRightUnit_inv_hom
#print axioms VOA.C2Rigid.LocalInjective.tensorRightUnitEquiv
#print axioms VOA.C2Rigid.LocalInjective.tensorBraid_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensorBraid_inverse_comp
#print axioms VOA.C2Rigid.LocalInjective.tensorBraidEquiv

#print axioms VOA.LogTensor.ModuleC2.finiteLength_of_finGen
#print axioms VOA.LogTensor.ModuleC2.component_mem_dualC1
#print axioms VOA.LogTensor.ModuleC2.dualC1_generalized_cutoff

#print axioms VOA.Classification.COne.OrbIcoW.coeff_jetMul
#print axioms VOA.Classification.COne.OrbIcoW.coefficients_unique_across_pivot
#print axioms VOA.Classification.COne.OrbIcoW.jet_coefficients_unique

#print axioms VOA.Huang.LogHuangODEProduct.theta_iter_mem_coupled
#print axioms VOA.Huang.LogHuangODEProduct.ratFuchsian_of_coupled_fg
#print axioms VOA.Huang.LogHuangODEProduct.exists_C1Graded
#print axioms VOA.Huang.LogHuangODEProduct.exists_DualC1Graded
#print axioms VOA.Huang.LogHuangODEProduct.QT_LogLm1
#print axioms VOA.Huang.LogHuangODEProduct.summable_log_product_homogeneous
#print axioms VOA.Huang.LogHuangODEProduct.summable_log_product
#print axioms VOA.Huang.LogHuangODEProduct.summable_log_product_series

#print axioms VOA.LogTensor.LogModuleCat.finiteDimensional_hom
#print axioms VOA.LogTensor.LogModuleCat.hom_ext

#print axioms VOA.Huang.LogHuangODEIterate.QI_LogLm1
#print axioms VOA.Huang.LogHuangODEIterate.exists_joint_fg
#print axioms VOA.Huang.LogHuangODEIterate.summable_log_iterate_homogeneous
#print axioms VOA.Huang.LogHuangODEIterate.summable_log_iterate
#print axioms VOA.Huang.LogHuangODEIterate.summable_log_iterate_series

#print axioms VOA.Classification.COne.OrbIcoW.coefficientJets_correct
#print axioms VOA.Classification.COne.OrbIcoW.jet_recurrence_holds
#print axioms VOA.Classification.COne.OrbIcoW.jet_pivot_holds
#print axioms VOA.Classification.COne.OrbIcoW.vac37_value
#print axioms VOA.Classification.COne.OrbIcoW.vac38_value
#print axioms VOA.Classification.COne.OrbIcoW.self19_value
#print axioms VOA.Classification.COne.OrbIcoW.self20_value
#print axioms VOA.Classification.COne.OrbIcoW.endpoint_values_positive
#print axioms VOA.Huang.LogHuangODEConvergence.summable_log_product_twoVar
#print axioms VOA.Huang.LogHuangODEConvergence.summable_log_iterate_twoVar

#print axioms VOA.LogTensor.Ar.modes_zero_isJacobi
#print axioms VOA.LogTensor.Ar.transform
#print axioms VOA.LogTensor.Ar.transform_logZero
#print axioms VOA.LogTensor.Ar.transformMap_injective
#print axioms VOA.LogTensor.Ar.transformMap_surjective
#print axioms VOA.LogTensor.Ar.transformEquiv
#print axioms VOA.LogTensor.Ar.finiteDimensional_transform_target
#print axioms VOA.LogTensor.Ar.transformEquiv_of_finiteLength

-- Actual logarithmic tensor and Ward specialization endpoints.
#print axioms VOA.Classification.COne.OrbIcoW.widthH_jetApprox
#print axioms VOA.Classification.COne.OrbIcoW.widthAt_jetApprox
#print axioms VOA.Classification.COne.OrbIcoW.JetApproxAlong.cancel_pivot
#print axioms VOA.Classification.COne.OrbIcoW.widthSequence_jetApprox
#print axioms VOA.Classification.COne.OrbIcoW.widthSequence_tendsto
#print axioms VOA.Classification.COne.OrbIcoW.genericSymbolCoefficient_jetApprox
#print axioms VOA.Classification.COne.OrbIcoW.genericSymbolCoefficient_tendsto
#print axioms VOA.Classification.COne.OrbIcoW.generic_vac37_tendsto
#print axioms VOA.Classification.COne.OrbIcoW.generic_vac38_tendsto
#print axioms VOA.Classification.COne.OrbIcoW.generic_self19_tendsto
#print axioms VOA.Classification.COne.OrbIcoW.generic_self20_tendsto
#print axioms VOA.LogTensor.Ar.transform_natural
#print axioms VOA.LogTensor.Ar.transformBranch_logZero
#print axioms VOA.LogTensor.Ar.transformBranchEquiv_of_finGen
#print axioms VOA.LogTensor.Ar.pair_contra_L0nil
#print axioms VOA.LogTensor.Ar.pair_contra_nilExp
#print axioms VOA.LogTensor.Ar.pair_contra_L0exp
#print axioms VOA.LogTensor.Ar.pair_contra_twist
#print axioms VOA.LogTensor.Ar.transposeLog_twistHom
#print axioms VOA.LogTensor.SelfDual.formMap_pair
#print axioms VOA.LogTensor.SelfDual.formEquiv
#print axioms VOA.LogTensor.SelfDual.formHom
#print axioms VOA.LogTensor.SelfDual.formInverseHom
#print axioms VOA.LogTensor.Pz.finiteLength_of_finGen
#print axioms VOA.LogTensor.Pz.finGen_contraLog_of_finGen
#print axioms VOA.LogTensor.Pz.evaluatePoint_homogeneous
#print axioms VOA.LogTensor.Pz.evaluatePoint_zero
#print axioms VOA.LogTensor.Pz.evaluatePoint_logShift
#print axioms VOA.LogTensor.Pz.evaluatePoint_injective
#print axioms VOA.C2Rigid.LocalInjective.evaluationIntertwinerOfForm
#print axioms VOA.C2Rigid.LocalInjective.evaluationIntertwinerOfForm_pair
#print axioms VOA.C2Rigid.LocalInjective.evaluationIntertwinerOfForm_ne_zero
#print axioms VOA.C2Rigid.LocalInjective.logModuleIntertwiner_natural
#print axioms VOA.C2Rigid.LocalInjective.rightUnitIntertwiner_natural
#print axioms VOA.C2Rigid.LocalInjective.evaluationIntertwiner_dinatural
#print axioms VOA.C2Rigid.LocalInjective.tensorEvaluationHom
#print axioms VOA.C2Rigid.LocalInjective.tensorEvaluation_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensorEvaluationHom_ne_zero
#print axioms VOA.C2Rigid.LocalInjective.tensorEvaluation_dinatural
#print axioms VOA.Huang.LogAssocExpansion.log_product_fullCoset_hasLogExp_all
#print axioms VOA.Huang.LogAssocExpansion.spectrumCosetSeeds_spec
#print axioms VOA.Huang.LogAssocExpansion.exists_spectrumCoset_weight
#print axioms VOA.Huang.LogAssocExpansion.spectrumCoset_weight_unique
#print axioms VOA.Huang.LogAssocExpansion.log_product_spectrum_hasLogExp

#print axioms VOA.Classification.COne.OrbIcoW.nonrealNhdsOne_neBot
#print axioms VOA.Classification.COne.OrbIcoW.square_tendsto_nonreal
#print axioms VOA.Classification.COne.OrbIcoW.genericSymbolCoefficient_square_tendsto
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap_mode
#print axioms VOA.Classification.COne.OrbIcoV.actualLevelState_zero_iff_fock
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap_zero_iff_fock
#print axioms VOA.Classification.COne.OrbIcoV.actualLevelState_grading
#print axioms VOA.Classification.COne.OrbIcoV.actualProbe_levelState
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap_positive_ward
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap_positive_above
#print axioms VOA.Classification.COne.OrbIcoV.actualFiberMap_ward_ground_zero
#print axioms VOA.Classification.COne.OrbIcoV.finiteWard_ground_injective
#print axioms VOA.Classification.COne.OrbIcoV.sixthProjection_below
#print axioms VOA.Classification.COne.OrbIcoV.sixthState_ground
#print axioms VOA.Classification.COne.OrbIcoV.vacuumState_ground
#print axioms VOA.Classification.COne.OrbIcoV.actualProbe_fiber
#print axioms VOA.LogTensor.omega_zero_twice
#print axioms VOA.LogTensor.omega_zero_twice_twist
#print axioms VOA.LogTensor.omega_zero_twice_balancing
#print axioms VOA.C2Rigid.LocalInjective.tensorDoubleSwap_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensor_twist_balancing
#print axioms VOA.C2Rigid.LocalInjective.tensor_weight_le_zeroMode_span
#print axioms VOA.C2Rigid.LocalInjective.tensor_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.tensor_homogeneousZeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.tensor_allMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.tensor_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.tensor_linearMap_ext_homogeneous
#print axioms VOA.LogTensor.Pz.nilExp_logShift
#print axioms VOA.LogTensor.Pz.nilExp_logShift_operator
#print axioms VOA.LogTensor.Pz.nilExp_logShift_all
#print axioms VOA.LogTensor.Pz.evaluatePoint_L0exp
#print axioms VOA.Huang.LogAssocExpansion.tsum_spectrumCosets
#print axioms VOA.Huang.LogAssocExpansion.completedLogProduct_eq_spectrum
#print axioms VOA.Huang.LogAssocExpansion.completedLogProduct_hasLogExp
#print axioms VOA.Huang.LogAssocCoefficients.coefficient
#print axioms VOA.Huang.LogAssocCoefficients.coefficient_homogeneous

#print axioms VOA.Classification.COne.OrbIcoV.exists_generic_finite_kernel
#print axioms VOA.Classification.COne.OrbIcoV.exists_specialized_finite_Fock
#print axioms VOA.Classification.COne.OrbIcoV.exists_specialized_vacuum_Xu
#print axioms VOA.Classification.COne.OrbIcoV.exists_specialized_self_Xu
#print axioms VOA.LogTensor.Ar.transform_logShift_pair
#print axioms VOA.LogTensor.Ar.transformBranch_logShift_pair
#print axioms VOA.LogTensor.LogModuleCat.tensorBifunctor
#print axioms VOA.LogTensor.LogModuleCat.leftUnitIso
#print axioms VOA.LogTensor.LogModuleCat.rightUnitIso
#print axioms VOA.LogTensor.LogModuleCat.swapIso

#print axioms VOA.Classification.COne.OrbIcoV.vacuumCoefficient37_exact
#print axioms VOA.Classification.COne.OrbIcoV.vacuumCoefficient38_exact
#print axioms VOA.Classification.COne.OrbIcoV.sixthCoefficient37_exact
#print axioms VOA.Classification.COne.OrbIcoV.sixthCoefficient38_exact
#print axioms VOA.Classification.COne.OrbIcoV.actualCoefficientCompatibility_holds
#print axioms VOA.Classification.COne.OrbIcoV.icoSymbolRelations_holds
#print axioms VOA.Classification.COne.xuIcosahedralPoissonRelations_holds
#print axioms VOA.Classification.COne.icosahedral_c2Cofinite_holds
#print axioms VOA.Classification.COne.gannonRayhaunConverse_of_B3
#print axioms VOA.Classification.COne.gannonRayhaun_classification
#print axioms VOA.Classification.COne.gannonRayhaunConverse_holds
#print axioms VOA.Classification.COne.finiteV2OrbifoldRationalOfC2
#print axioms VOA.Classification.COne.twistedJacobiBridgeAll_holds
#print axioms VOA.Classification.COne.McRaeO5b.twistedJacobiBridge_holds
#print axioms VOA.Classification.COne.McRaeO7.gannonRayhaunConverse_of_bridge
#print axioms VOA.LogTensor.LogModuleCat.logarithmicMonoidalCategory
#print axioms VOA.LogTensor.LogModuleCat.logarithmicBraidedCategory
#print axioms VOA.Huang.SchurWeyl.dlmSchurWeyl_holds
#print axioms VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite_pbw

#print axioms VOA.LogTensor.Ar.functional_logPolynomial_eval
#print axioms VOA.LogTensor.Ar.transformBranch_coefficient_pair
#print axioms VOA.LogTensor.Ar.transformBranch_modes
#print axioms VOA.LogTensor.Ar.isLogIntertwining_modes
#print axioms VOA.Huang.LogAssocCoefficientCompatibility.supportedAt_comp_mode
#print axioms VOA.Huang.LogAssocCoefficientCompatibility.eq_zero_of_supportedAt_bot
#print axioms VOA.Huang.LogAssocCoefficientCompatibility.exists_comp_mode_vanish
#print axioms VOA.Huang.LogAssocCoefficientCompatibility.restrictedDual_supportedAt
#print axioms VOA.Huang.LogAssocCoefficientCompatibility.exists_nat_truncation
#print axioms VOA.Huang.LogGenusOne.zeroModePiece_nil_commutator
#print axioms VOA.Huang.LogGenusOne.logModeTrace_succ
#print axioms VOA.Huang.LogGenusOne.logModeTrace_factorial
#print axioms VOA.Huang.LogGenusOne.logModeTrace_zero_of_jordan
#print axioms VOA.Huang.LogGenusOne.logModeTrace_no_higher_of_source_eigen
#print axioms VOA.Huang.LogAssocCoefficients.exists_coefficient_bounds
#print axioms VOA.Huang.LogAssocCoefficients.exists_restrictedDual_coefficient_bounds
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.fullCoset_assoc_right
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.spectrum_assoc_right
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_coproduct_homogeneous
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_coproduct
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.exists_comp_mode_vanish_below
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_mem_span
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_rho_stable
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_tau_stable
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_truncated
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_truncated
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.fullCoset_assoc_left
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.spectrum_assoc_left
#print axioms VOA.Huang.LogAssocCoefficients.outerModes_weight
#print axioms VOA.Huang.LogAssocCoefficients.outerModes_truncated
#print axioms VOA.Huang.LogAssocCoefficients.outerModes_pair
#print axioms VOA.Huang.LogAssocOutsideJacobi.fullCoset_commutator
#print axioms VOA.Huang.LogAssocOutsideJacobi.spectrum_commutator
#print axioms VOA.Huang.LogAssocCoefficientL0.tau_conformal
#print axioms VOA.Huang.LogAssocCoefficientL0.dualL0_commute_firstNil
#print axioms VOA.Huang.LogAssocCoefficientL0.dualL0_commute_secondNil
#print axioms VOA.Huang.LogAssocCoefficientL0.firstNil_isNilpotent_of_finGen
#print axioms VOA.Huang.LogAssocCoefficientL0.secondNil_isNilpotent_of_finGen
#print axioms VOA.Huang.LogAssocCoefficientL0.prodCoeff_LogLm1_left
#print axioms VOA.Huang.LogAssocCoefficientL0.prodSeries_LogLm1_left
#print axioms VOA.Huang.LogAssocCoefficientL0.hasDerivAt_prodFun_log
#print axioms VOA.Huang.LogAssocCoefficientL0.finite_log_successor_cancel
#print axioms VOA.Huang.LogAssocCoefficientL0.hasDerivAt_fullNatProduct
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_assoc_left_homogeneous
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.compatible_of_homogeneous
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_zero_f
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_compatible
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_le_regular
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_compatible
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientCompatibleSpace
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_le_maximal
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficient_mem_maximal
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientWeakModule
#print axioms VOA.Huang.LogAssocOutsideJacobi.logCoeff_spectrum_commutator
#print axioms VOA.Huang.LogAssocOutsideJacobi.coefficient_commutator_homogeneous
#print axioms VOA.Huang.LogAssocCoefficientL0.hasDerivAt_fullCoset
#print axioms VOA.Huang.LogAssocCoefficientL0.hasDerivAt_spectrum
#print axioms VOA.Huang.LogAssocCoefficientL0.spectrum_Lm1_eq
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficient_Lm1_left
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficient_L0_Ward
#print axioms VOA.Huang.LogAssocCoefficientL0.exists_coefficient_L0_bound
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficient_mem_maxGenEigenspace
#print axioms VOA.Huang.LogAssocCoefficientL0.compatible_L0_coe
#print axioms VOA.Huang.LogAssocCoefficientL0.compatible_mem_maxGenEigenspace
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficientWeakModule_mem_maxGenEigenspace
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficient_mem_maximal_weight
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.compatibleSpaceInclusionHom
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpanHom
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpanHom_injective
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_finiteLength
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientSpan_finGen
#print axioms VOA.Huang.LogAssocCoefficientCoproduct.coefficientLogModule
#print axioms VOA.Huang.LogAssocCoefficients.coefficientOuterModes_weight
#print axioms VOA.Huang.LogAssocCoefficients.coefficientOuterModes_truncated
#print axioms VOA.Huang.LogAssocCoefficients.coefficientOuterModes_pair
#print axioms VOA.Huang.LogAssocOutsideJacobi.rho_convolution
#print axioms VOA.Huang.LogAssocOutsideJacobi.coefficient_shift_vanish
#print axioms VOA.Huang.LogAssocOutsideJacobi.coefficient_commutator_homogeneous_rho
#print axioms VOA.Huang.LogAssocOutsideJacobi.coefficient_outside_borcherds_homogeneous
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterModes_weight
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterModes_truncated
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterModes_pair
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterLogModes_zero
#print axioms VOA.Huang.LogAssocExpansion.completedLogIterate_eq_lowerSpectrum
#print axioms VOA.Huang.LogAssocExpansion.completedLogIterate_hasLogExp
#print axioms VOA.Huang.LogAssocExpansion.log_iterate_spectrum_hasLogExp
#print axioms VOA.Huang.LogAssocTensorOuterModes.pair_tensor_mode_coefficient
#print axioms VOA.Huang.LogAssocCoefficientL0.tensorIntertwiner_factorial_pair
#print axioms VOA.Huang.LogAssocCoefficientL0.coefficientDefect_pow_zero
#print axioms VOA.Huang.LogAssocCoefficientL0.tensorIntertwiner_pair_coefficient
#print axioms VOA.Huang.LogAssocExpansion.tsum_lowerSpectrum
#print axioms VOA.Huang.LogAssocExpansion.log_iterate_lowerCoset_hasLogExp
#print axioms VOA.Huang.LogGenusOne.trace_mul_nilExp
#print axioms VOA.Huang.LogGenusOne.weightL0Exp_coe
#print axioms VOA.Huang.LogGenusOne.trace_weightL0Exp
#print axioms VOA.Huang.LogGenusOne.moduleZeroModePiece_commute_nil
#print axioms VOA.Huang.LogGenusOne.moduleTraceTerm_eq
#print axioms VOA.Huang.LogAssocExpansion.logCoeff_iterateSpectrum
#print axioms VOA.Huang.LogAssocTensorOuterModes.outsideCoeff_borcherds
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterModes_isJacobi
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterIntertwiner
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterIntertwiner_zero
#print axioms VOA.C2Rigid.LocalInjective.tensorValuesOn_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.leftTriple_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.rightTriple_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.leftTriple_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.rightTriple_linearMap_ext
#print axioms VOA.Huang.LogAssocTensorCoefficientMatching.tensorOuterModes_innerPair
#print axioms VOA.Huang.LogAssocTensorCoefficientMatching.completedLogProduct_eq_canonical_iterate_supported
#print axioms VOA.Huang.LogAssocTensorCoefficientMatching.completedLogProduct_eq_canonical_iterate
#print axioms VOA.C2Rigid.LocalInjective.weakEnd_injective_of_surjective
#print axioms VOA.C2Rigid.LocalInjective.weakCycle_bijective
#print axioms VOA.Huang.LogGenusOne.logOMod_mem_generalized_weight
#print axioms VOA.Huang.LogGenusOne.logOMod_commute_nil
#print axioms VOA.Huang.LogGenusOne.actualTraceData
#print axioms VOA.Huang.LogGenusOne.actualTrace_isCyclicBlock
#print axioms VOA.Huang.LogGenusOne.moduleZeroModeLinear_homogeneous
#print axioms VOA.Huang.LogAssocCoefficientL0.tensorIntertwiner_logShift_pair_coefficient
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterFactor
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterFactor_comp_intertwiner
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterFactor_unique
#print axioms VOA.C2Rigid.LocalInjective.tensorAssociatorHom
#print axioms VOA.C2Rigid.LocalInjective.tensorAssociatorHom_comp_intertwiner
#print axioms VOA.C2Rigid.LocalInjective.tensorAssociatorHom_apply
#print axioms VOA.C2Rigid.LocalInjective.tensorAssociatorHom_nested
#print axioms VOA.Huang.LogGenusOne.trace_mul_nilpow
#print axioms VOA.Huang.LogGenusOne.scalarTracePolynomial_eq_constant
#print axioms VOA.Huang.LogGenusOne.actualTraceData_nilpotentPiece
#print axioms VOA.Huang.LogGenusOne.moduleZeroModeLinear_commute_nil
#print axioms VOA.Huang.LogGenusOne.actualTrace_polynomial_eq_constant
#print axioms VOA.Huang.LogAssocTensorOuterModes.coefficient_postcompose
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterIntertwiner_postcompose
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterFactor_postcompose
#print axioms VOA.Huang.LogAssocTensorOuterModes.coefficient_precompose_third
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterIntertwiner_precompose_third
#print axioms VOA.Huang.LogAssocTensorOuterModes.tensorOuterFactor_precompose_third
#print axioms VOA.Huang.LogAssocTensorCoefficientMatching.completedLogProduct_eq_canonical_iterate_shift
#print axioms VOA.Huang.LogAssocTensorCoefficientMatching.completedLogProduct_eq_canonical_iterate_three_two_one
#print axioms VOA.C2Rigid.LocalInjective.leftFour_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.leftFour_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.midLeftFour_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.midLeftFour_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.middleFour_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.middleFour_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.midRightFour_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.midRightFour_linearMap_ext
#print axioms VOA.C2Rigid.LocalInjective.rightFour_zeroMode_span_eq_top
#print axioms VOA.C2Rigid.LocalInjective.rightFour_linearMap_ext
