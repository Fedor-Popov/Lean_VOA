import VOA.Core.RankOneTransfer
import VOA.Core.ScreeningKernel
import VOA.Core.SesqFormTransport
import VOA.Core.TensorFieldLift
import VOA.Core.InternalGradingOperator
import VOA.Core.WeightCommutatorField
import VOA.Examples.AffineSl2GoodFiltration
import VOA.Examples.AffineSl2GradedUnitarityLow
import VOA.Examples.AffineSl2HarmonicNorm
import VOA.Examples.InverseDSPositivityTransfer
import VOA.Examples.InverseDSGradedUnitarityTransfer
import VOA.Examples.InverseDSPiLattice
import VOA.Examples.InverseDSPiHeisenberg
import VOA.Examples.InverseDSPiExponential
import VOA.Examples.InverseDSPiTransverse
import VOA.Examples.InverseDSPiNegativeExponential
import VOA.Examples.InverseDSPiGrading
import VOA.Examples.InverseDSParameters
import VOA.Examples.AffineSl2VacuumEvaluation
import VOA.Examples.AffineSl2CurrentRealization
import VOA.Examples.AffineSl2CurrentOPEBridge
import VOA.Examples.InverseDSSimpleQuotientGate
import VOA.Examples.InverseDSHalfLatticeScreening
import VOA.Examples.InverseDSScreeningCoset
import VOA.Examples.InverseDSScreeningCartan
import VOA.Examples.InverseDSScreeningRaising
import VOA.Examples.InverseDSScreeningTensor
import VOA.Examples.InverseDSScreeningLowering
import VOA.Examples.InverseDSLeeYangWardClosure
import VOA.Examples.LogarithmicHeterotypicJet
import VOA.Examples.InverseDSLeeYangIntertwinerDescent
import VOA.Examples.InverseDSLeeYangFockBoundary
import VOA.Examples.InverseDSLeeYangFockExponential
import VOA.Examples.InverseDSLeeYangFockVirasoro
import VOA.Examples.InverseDSLeeYangFockWard
import VOA.Examples.ScreenedReesInterface
import VOA.Examples.InverseDSLeeYangHeterotypicLocality
import VOA.Examples.InverseDSLeeYangSectorSugawaraBridge
import VOA.Examples.InverseDSLeeYangFullFockWard
import VOA.Examples.InverseDSLeeYangConcreteDescent
import VOA.Examples.InverseDSLeeYangTargetNull
import VOA.Examples.InverseDSLeeYangBPZ
import VOA.Examples.InverseDSLeeYangPBWClosure
import VOA.Examples.InverseDSLeeYangMaximalSubmodule
import VOA.Examples.InverseDSVirasoroVerma

-- Axiom probes for the p=3 rank-one transfer and affine inverse-DS infrastructure.
#print axioms VOA.Screening.screening_commute_of_zeroProduct_eq_translation

#print axioms VOA.rankOneRemainder_completedSquare
#print axioms VOA.rankOneRemainder_posSemidef
#print axioms VOA.rankOneRemainder_mulVec_eq_zero_iff
#print axioms VOA.rankOneRemainder_ker

#print axioms VOA.SesqForm.pullback_signedForm
#print axioms VOA.SesqForm.isPosOn_pullback
#print axioms VOA.SesqForm.isPosOn_signedForm_of_eq_pullback

#print axioms VOA.AffineVOA.CorrectedR.mode_piece_mem_piece_add
#print axioms VOA.AffineVOA.CorrectedR.correctedAffineRWeightPiece_one_two
#print axioms VOA.AffineVOA.CorrectedR.correctedAffineRWeightPiece_two_two
#print axioms VOA.AffineVOA.CorrectedR.correctedAffineRFlag_modeCompatible
#print axioms VOA.AffineVOA.CorrectedR.correctedAffineRQuotientFlag_modeCompatible

#print axioms VOA.AffineVOA.GradedUnitarityLow.canonicalForm85_currentState
#print axioms VOA.AffineVOA.GradedUnitarityLow.simpleCanonicalBilin85_nondegenerate
#print axioms VOA.AffineVOA.GradedUnitarityLow.compactCurrentSignedForm85_eq_canonical
#print axioms VOA.AffineVOA.GradedUnitarityLow.compactCurrentSignedForm85_positive
#print axioms VOA.AffineVOA.GradedUnitarityLow.simpleCorrectedGoodFiltration85

#print axioms VOA.InverseDS.MetricComparison.map_affinePiece_eq_range_inf
#print axioms VOA.InverseDS.MetricComparison.signedPositivity_on_affinePiece
#print axioms VOA.InverseDS.MetricComparison.signedPositivity_on_affinePiece_of_strict



#print axioms VOA.InverseDS.SesqForm.ext
#print axioms VOA.InverseDS.SesqForm.isPosOn_mono
#print axioms VOA.InverseDS.LinearMap.BilinForm.nondegenerate_restrict_of_eq_pullback
#print axioms VOA.InverseDS.GradedIsometricEmbedding.weightMap_injective
#print axioms VOA.InverseDS.GradedIsometricEmbedding.gradedForm_eq_pullback
#print axioms VOA.InverseDS.GradedIsometricEmbedding.gradedSesq_eq_pullback
#print axioms VOA.InverseDS.GradedIsometricEmbedding.gradedUnitaryAt_of_ambient
#print axioms VOA.InverseDS.GradedIsometricEmbedding.gradedUnitary_of_ambient

#print axioms VOA.AffineVOA.HarmonicNorm.H0_eHarmonic
#print axioms VOA.AffineVOA.HarmonicNorm.F1_eHarmonic_succ
#print axioms VOA.AffineVOA.HarmonicNorm.form_J_negOne_left
#print axioms VOA.AffineVOA.HarmonicNorm.form_fHarmonic_eHarmonic
#print axioms VOA.AffineVOA.HarmonicNorm.signed_compactHarmonicDiagonal_real_pos
#print axioms VOA.AffineVOA.HarmonicNorm.canonical_signed_compactHarmonicDiagonal85_eq_and_pos

#print axioms VOA.InverseDSPi.piLattice_even
#print axioms VOA.InverseDSPi.piLattice_not_posDef
#print axioms VOA.InverseDSPi.etaCharge_injective
#print axioms VOA.InverseDSPi.piChargeOperatorShadow_mode_neg_one_vacuum
#print axioms VOA.InverseDSPi.piChargeOperatorShadow_on_chargeLine

#print axioms VOA.InverseDSPi.directionOsc_comm
#print axioms VOA.InverseDSPi.complexHyperbolicDirection_pairing
#print axioms VOA.InverseDSPi.etaOsc_xiOsc_comm
#print axioms VOA.InverseDSPi.directionCreate_vacuum
#print axioms VOA.InverseDSPi.xiZeroMode_piFockState

#print axioms VOA.InverseDSPi.etaDress_isField
#print axioms VOA.InverseDSPi.etaDress_comm
#print axioms VOA.InverseDSPi.etaExponentialField_isField
#print axioms VOA.InverseDSPi.etaExponentialField_vacuum
#print axioms VOA.InverseDSPi.etaExponentialField_local
#print axioms VOA.InverseDSPi.etaCurrentField_local_exponential

#print axioms VOA.InverseDSPi.xiOsc_zero
#print axioms VOA.InverseDSPi.xiCurrentField_neg_one_comm_exponential_piFockState
#print axioms VOA.InverseDSPi.xiCurrentField_comm_exponential_piFockState_of_ne
#print axioms VOA.InverseDSPi.xiCurrentField_comm_exponential
#print axioms VOA.InverseDSPi.xiCurrentField_local_exponential

#print axioms VOA.InverseDSPi.etaNegativeExponentialField_isField
#print axioms VOA.InverseDSPi.etaNegativeExponentialField_mode_neg_one_vacuum
#print axioms VOA.InverseDSPi.piWeightGrading_isInternal
#print axioms VOA.InverseDSPi.etaExponentialField_graded
#print axioms VOA.InverseDSPi.etaNegativeExponentialField_graded
-- #print axioms VOA.InverseDS.BoundaryPiWall.charge_neutrality  -- reports a strict subset of the base axioms; recorded in HANDOFF.md
-- #print axioms VOA.InverseDS.BoundaryPiWall.source_singular_diamond  -- reports a strict subset of the base axioms; recorded in HANDOFF.md
-- #print axioms VOA.InverseDS.BoundaryPiWall.glueCharge_eq_horizontalWeight  -- reports a strict subset of the base axioms; recorded in HANDOFF.md
-- #print axioms VOA.InverseDS.BoundaryPiWall.reverse_charge_shift  -- reports a strict subset of the base axioms; recorded in HANDOFF.md
#print axioms VOA.InverseDS.WallJets.StrictWardJet.derived
#print axioms VOA.InverseDS.WallJets.IsChainMapJet.derived
#print axioms VOA.InverseDS.WallJets.bocksteinOnCohomology
#print axioms VOA.InverseDS.WallJets.differentialJet_cycle_eq_eps_bockstein
#print axioms VOA.InverseDS.WallJets.LogarithmicHeterotypicJet.derivedWard
#print axioms VOA.InverseDS.WallJets.LogarithmicHeterotypicJet.derivedChainMap
#print axioms VOA.InverseDS.WallJets.LogarithmicHeterotypicJet.secondaryResidue_isChainMap
#print axioms VOA.InverseDSPi.piCentralCharge_eq
#print axioms VOA.InverseDSPi.affineSugawaraCentralCharge_boundary85
#print axioms VOA.AffineVOA.VacuumCurrentRealization.eval_J
#print axioms VOA.AffineVOA.AffineCurrentData.toVacuumCurrentRealization_current
#print axioms VOA.AffineVOA.AffineCurrentFieldData.loopMode_comm
#print axioms VOA.AffineVOA.AffineCurrentFieldData.eval_vacuumRho
#print axioms VOA.InverseDS.AffineEvaluation.evalMaxQuotient_injective
#print axioms VOA.InverseDS.HalfLattice.K85Prop21ScreeningData.simpleQuotientEval_injective
#print axioms VOA.InverseDS.HalfLattice.K85Prop21ScreeningData.range_simpleQuotientEval_eq_ker_screening
#print axioms VOA.InverseDS.ScreeningCoset.nuExponentialHalfField_isHeterotypicField
#print axioms VOA.InverseDS.ScreeningCoset.piNuHalfResidue_zero_of_odd_label
#print axioms VOA.InverseDS.ScreeningCoset.hCurrent_intertwines_nuExponential
#print axioms VOA.InverseDS.ScreeningCoset.raisingCurrent_intertwines_nuExponential
#print axioms VOA.InverseDS.ScreeningTensor.fullScreeningResidue_tmul
#print axioms VOA.InverseDS.ScreeningTensor.fullScreening_intertwines_h
#print axioms VOA.InverseDS.ScreeningTensor.fullScreening_intertwines_e
#print axioms VOA.InverseDS.ScreeningLowering.negEta_nu_pairing_k85
#print axioms VOA.InverseDS.ScreeningLowering.k85_lowering_coefficients
#print axioms VOA.InverseDS.LeeYangWardClosure.homBracket_comm
#print axioms VOA.InverseDS.LeeYangWardClosure.primaryWard_all_of_five
#print axioms VOA.InverseDS.LeeYangWardClosure.k85VirasoroIntertwinerWard_of_five
#print axioms VOA.InverseDS.LeeYangWardClosure.K85VirasoroScreeningFiveModeData.toScreeningFieldData
#print axioms VOA.InverseDS.LeeYangIntertwinerDescent.respectsNullSubmodules_iff_factors
#print axioms VOA.InverseDS.LeeYangIntertwinerDescent.fieldRespectsNullSubmodules_iff_factors
#print axioms VOA.InverseDS.LeeYangIntertwinerDescent.quotientField_isHeterotypicField
#print axioms VOA.InverseDS.LeeYangIntertwinerDescent.k85Ward_quotient
#print axioms VOA.InverseDS.LeeYangIntertwinerDescent.K85ScreeningDescentData.toQuotientScreeningFieldData
#print axioms VOA.InverseDS.LeeYangFockBoundary.leeYang_backgroundSquare
#print axioms VOA.InverseDS.LeeYangFockBoundary.leeYang_halfNorm_solutions
#print axioms VOA.InverseDS.LeeYangFockBoundary.leeYang_halfNorm_not_integral
#print axioms VOA.InverseDS.LeeYangFockBoundary.K85FockCosetCoefficientData.toScreeningFieldData
#print axioms VOA.ScreenedRees.felderQuotientMap_mkQ
#print axioms VOA.ScreenedRees.exactFiltrationLayerMap_mkQ
-- #print axioms VOA.ScreenedRees.descendedMap_invariant_under_boundaryChange  -- reports a strict subset of the base axioms; recorded in HANDOFF.md
#print axioms VOA.ScreenedRees.isPosOn_of_metricTransport


#print axioms VOA.TensorFieldLift.local_firstField
#print axioms VOA.TensorFieldLift.local_firstField_secondField
#print axioms VOA.TensorFieldLift.dcovariant_firstField
#print axioms VOA.TensorFieldLift.nprod_firstField
#print axioms VOA.TensorFieldLift.nprod_firstField_secondField_apply
#print axioms VOA.grading_le_eigenspace_internalWeightOperatorZ
#print axioms VOA.internalWeightOperatorZ_comm_of_maps
#print axioms VOA.WeightCommutatorField.nprod
#print axioms VOA.InverseDS.LeeYangFockExponential.k85FockCharge_sq
#print axioms VOA.InverseDS.LeeYangFockExponential.k85FockField_isHeterotypicField
#print axioms VOA.InverseDS.LeeYangFockVirasoro.k85SourceL_isLeeYang
#print axioms VOA.InverseDS.LeeYangFockVirasoro.k85TargetL_isLeeYang
#print axioms VOA.InverseDS.LeeYangFockWard.alphaMode_comm_EEC
#print axioms VOA.InverseDS.LeeYangFockWard.k85FockField_primaryWard_negOne
#print axioms VOA.InverseDS.LeeYangFockWard.k85FockField_primaryWard_zero

-- Recovered inverse-DS completion modules: composite Wick identities, full Ward descent,
-- and the full half-lattice carrier.
#print axioms VOA.InverseDS.LeeYangHeterotypicLocality.currentNprodEECBracket_secondDifference
#print axioms VOA.InverseDS.LeeYangSectorSugawaraBridge.quarter_nprod_sectorCurrentDist
#print axioms VOA.InverseDS.LeeYangFullFockWard.k85FockField_primaryWard_negTwo
#print axioms VOA.InverseDS.LeeYangFullFockWard.k85FockField_primaryWard_one
#print axioms VOA.InverseDS.LeeYangFullFockWard.k85FockField_primaryWard_two
#print axioms VOA.InverseDS.LeeYangFullFockWard.k85FockField_primaryWard_all
#print axioms VOA.InverseDS.LeeYangConcreteDescent.k85FockField_respects_canonicalNulls
#print axioms VOA.InverseDS.LeeYangTargetNull.k85TargetSingularTwo_L1
#print axioms VOA.InverseDS.LeeYangTargetNull.k85TargetSingularThree_L2
#print axioms VOA.InverseDS.LeeYangTargetNull.k85BPZ_iff_integerEEC
#print axioms VOA.InverseDS.LeeYangBPZ.k85EEC_sourceSingular_negOne
#print axioms VOA.InverseDS.LeeYangBPZ.k85BPZ_iff_natNormalForm
#print axioms VOA.InverseDS.LeeYangPBWClosure.k85PBWNumerator_two_mem
#print axioms VOA.InverseDS.LeeYangPBWClosure.k85EEC_nat_all_mem_iff_PBW_remainder_addTwo
#print axioms VOA.InverseDS.LeeYangMaximalSubmodule.submodule_eq_of_le_of_isGradedBy_of_quotientCharacter
#print axioms VOA.InverseDS.LeeYangMaximalSubmodule.k85TargetCandidateNull_eq_of_quotientCharacter
#print axioms VOA.InverseDS.LeeYangMaximalSubmodule.k85PBWNumerator_all_mem_of_quotientCharacter

-- Weighted outer-Wick residue cancellation and its source/target commutator reductions.

-- Newly integrated weighted `e-f` and general-Verma infrastructure.
#print axioms VOA.InverseDS.VirasoroVerma.verma_acts_central
#print axioms VOA.InverseDS.VirasoroVerma.verma_cyclic
#print axioms VOA.InverseDS.VirasoroVerma.negWord_mem_sortedSpan
#print axioms VOA.InverseDS.VirasoroVerma.LeeYangTwoSingularBasisTheorem

-- Pi derivative inverse: weighted source support, shear regrouping, and moment reduction.

-- Quadratic screening residue: generic two-cut reduction, closed OPE criterion, and K85 pair.

-- Differentiated half-Newton identities and the transport-form screening reduction.
