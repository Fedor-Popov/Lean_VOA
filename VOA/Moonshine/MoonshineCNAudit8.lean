import VOA.Moonshine.MoonshineCNAudit7
import VOA.Moonshine.MoonshineCNVnatSectorGrading
import VOA.Moonshine.MoonshineCNVnatSectorLaws
import VOA.Moonshine.MoonshineCNVnatStringModule
import VOA.Moonshine.MoonshineCNVnatFormAction
import VOA.Moonshine.MoonshineCNVnatSectorAction
import VOA.Moonshine.MoonshineCNVnatSectorEvaluation
import VOA.Moonshine.MoonshineCNVnatLongitudinalQuotient
import VOA.Moonshine.MoonshineCNStringComparison
import VOA.Moonshine.MoonshineCNVnatNoGhost
import VOA.Moonshine.MoonshineCNVnatZeroWeight
import VOA.Moonshine.MoonshineCNVnatZeroQuotient
import VOA.Moonshine.MoonshineCNVnatNoGhostConsequences

/-! Kernel dependency audit of the concrete moonshine no-ghost isometries. -/

#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_tmul
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_energy
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_top
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_isInternal
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_eq_eigenspace
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_negative
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_pairRange
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_finiteDimensional
#print axioms VOA.Moonshine.ConwayNorton.vnatHypLongitudinal
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_mode
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_oscillator
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_orthogonal
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorWeight_nondegenerate
#print axioms VOA.Moonshine.ConwayNorton.vnatHypLongitudinal_comm
#print axioms VOA.Moonshine.ConwayNorton.vnatHypLongitudinal_mixed
#print axioms VOA.Moonshine.ConwayNorton.vnatHypLongitudinal_adjoint
#print axioms VOA.Moonshine.ConwayNorton.vnatStringModule
#print axioms VOA.Moonshine.ConwayNorton.vnatNonzeroMomentum_cast
#print axioms VOA.Moonshine.ConwayNorton.stringSectorFamily
#print axioms VOA.Moonshine.ConwayNorton.stringSector
#print axioms VOA.Moonshine.ConwayNorton.stringSector_lightConeSplit
#print axioms VOA.Moonshine.ConwayNorton.stringSector_charge
#print axioms VOA.Moonshine.ConwayNorton.vnatAut_comm_power
#print axioms VOA.Moonshine.ConwayNorton.vnatAutPullbackForm
#print axioms VOA.Moonshine.ConwayNorton.vnatAutPullbackForm_fhl
#print axioms VOA.Moonshine.ConwayNorton.vnatAut_preserves_natForm
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction_tmul
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction_weight
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction_mode
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction_longitudinal
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorAction_isometry
#print axioms VOA.Moonshine.ConwayNorton.vnatStringGroupAction
#print axioms VOA.Moonshine.ConwayNorton.stringSectorAction
#print axioms VOA.Moonshine.ConwayNorton.hypTensorOneFamily_induction
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorEval
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorEval_tmul
#print axioms VOA.Moonshine.ConwayNorton.hypLevel_constantCoeff_eq_zero
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorEval_weight
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorEval_oneFamily_form
#print axioms VOA.Moonshine.ConwayNorton.vnatMatterVacuumTensor_mem
#print axioms VOA.Moonshine.ConwayNorton.vnatSectorEval_action
#print axioms VOA.Moonshine.ConwayNorton.vnatStringWeightAddCommGroup
#print axioms VOA.Moonshine.ConwayNorton.vnatStringSliceAddCommGroup
#print axioms VOA.Moonshine.ConwayNorton.vnatStringModule_kVacuum
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumEvaluation
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumEvaluation_surjective
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumEvaluation_radical
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumEvaluation_ker
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuum_augmentation
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumQuotientEquiv
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumQuotientEquiv_mk
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumQuotientEquiv_isometry
#print axioms VOA.Moonshine.ConwayNorton.vnatKVacuumQuotientEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.StringModule.physicalKQuotientEquiv
#print axioms VOA.Moonshine.ConwayNorton.StringModule.physicalKQuotientEquiv_isometry
#print axioms VOA.Moonshine.ConwayNorton.StringGroupAction.physicalKQuotientEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.stringSectorWeightAddCommGroup
#print axioms VOA.Moonshine.ConwayNorton.stringSectorSliceAddCommGroup
#print axioms VOA.Moonshine.ConwayNorton.stringSectorTransverseMatterEquiv
#print axioms VOA.Moonshine.ConwayNorton.stringSectorNoGhostEquiv
#print axioms VOA.Moonshine.ConwayNorton.stringSectorNoGhostEquiv_isometry
#print axioms VOA.Moonshine.ConwayNorton.stringSectorNoGhostEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.hypWeightOne_exponent
#print axioms VOA.Moonshine.ConwayNorton.hypLevel_one_span
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroBasisVector
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroBasisVector_mem
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeight_span
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroBasisVector_physical
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeight_physical
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightMap
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightCoordinates
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightMap_coordinates
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightMap_single
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightMap_surjective
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightEquiv
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroBasisVector_form
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroWeightEquiv_isometry
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroPhysicalEquiv
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroPhysicalRadical
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroNoGhostEquiv
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroNoGhostEquiv_mk
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroNoGhostEquiv_isometry
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroSectorAction_trivial
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroNoGhostEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.stringSector_weight_split
#print axioms VOA.Moonshine.ConwayNorton.stringSectorNoGhost_finrank
#print axioms VOA.Moonshine.ConwayNorton.vnatZeroNoGhost_finrank
