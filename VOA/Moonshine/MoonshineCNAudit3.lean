import VOA.Moonshine.MoonshineCNAudit2
import VOA.Moonshine.MoonshineCNTraceBounds
import VOA.Moonshine.MoonshineCNStatement
import VOA.Moonshine.MoonshineCNTensorFields
import VOA.Moonshine.MoonshineCNTensorConformal
import VOA.Moonshine.MoonshineCNTensorGrading
import VOA.Moonshine.MoonshineCNTensorRealization
import VOA.Moonshine.MoonshineCNTensorMomentum
import VOA.Moonshine.MoonshineCNFockAdjoint
import VOA.Moonshine.MoonshineCNLatticeForm
import VOA.Moonshine.MoonshineCNTensorForm
import VOA.Moonshine.MoonshineCNTensorNondegenerate

/-! Axiom audit of the statement interface, matter near-VOA, and bilinear forms. -/

namespace VOA.Moonshine.ConwayNorton

#print axioms finiteOrderTrace_norm_le
#print axioms gradedAutTrace_norm_le
#print axioms mckayThompson_coeff_norm_le
#print axioms cuspInfty
#print axioms qPar
#print axioms mckayThompsonFun
#print axioms SendsInftyTo
#print axioms HasCuspValue
#print axioms IsOtherCusp
#print axioms IsNormalizedHauptmodul
#print axioms IsGenusZero
#print axioms gamma0GL
#print axioms gamma1GL
#print axioms IsMoonshineGroup
#print axioms ConwayNortonFor
#print axioms ConwayNortonConjecture
#print axioms ConwayNortonVia
#print axioms ConwayNortonGammaOne
#print axioms heckePoint_im_pos
#print axioms heckePoint
#print axioms CompletelyReplicable
#print axioms RationalTraces
#print axioms qSeriesFun
#print axioms ReplicableFamily
#print axioms mckayThompsonFun_one
#print axioms mckayThompsonFun_eq_qSeriesFun
#print axioms mckayThompsonReplicableFamily
#print axioms mckayThompson_replicableFamily_exists
#print axioms nearField_isField
#print axioms nearFirstField
#print axioms nearSecondField
#print axioms nearNormalProduct_congr
#print axioms nearTensorFieldBilinear
#print axioms nearTensorField
#print axioms nearTensorField_tmul
#print axioms nearTensorField_tmul_apply
#print axioms nearTensorField_isField
#print axioms nearTensorField_local_tmul
#print axioms nearTensorField_local
#print axioms nearField_vacuum_neg
#print axioms nearField_vacuum_zero
#print axioms nearTensorField_creation
#print axioms nearTensorField_first_vacuum
#print axioms nearTensorField_second_vacuum
#print axioms nearTensorField_vacuum
#print axioms nearVirasoroMode
#print axioms nearTensorConformalVector
#print axioms nearTensorField_conformal
#print axioms nearTensorField_conformal_mode
#print axioms nearTensorOperator_commutator
#print axioms nearTensorField_virasoro
#print axioms nearTensorField_translation
#print axioms tensorFinsum_mem
#print axioms nearTensorGrading
#print axioms nearTensorGrading_tmul
#print axioms nearTensorGrading_induction
#print axioms nearTensorGrading_top
#print axioms nearTensorGrading_energy
#print axioms nearTensorGrading_isInternal
#print axioms nearTensorCoefficient
#print axioms nearTensorGrading_mode
#print axioms nearTensorVOA
#print axioms moonshineMatterSpace
#print axioms moonshineMatterNearVOA
#print axioms moonshineMatterNearVOA_centralCharge
#print axioms moonshineMatterNearVOA_conformalVector
#print axioms moonshineMatterNearVOA_tmul_field
#print axioms lorentzianChargeLabel
#print axioms lorentzianChargeLabel_injective
#print axioms lorentzianChargeDiagonal
#print axioms lorentzianChargeDiagonal_single
#print axioms lorentzianLatticeMomentumOperator
#print axioms lorentzianLatticeMomentumOperator_eigen
#print axioms moonshineMatterMomentum
#print axioms moonshineMatterMomentum_tmul
#print axioms moonshineMatterMomentum_eigen
#print axioms moonshineMatterMomentum_isInternal
#print axioms moonshineMatterMomentum_mode
#print axioms uForm_sugawaraTerm_adjoint
#print axioms uForm_virasoro_adjoint
#print axioms uForm_frameOscillator_adjoint
#print axioms NearInvariantForm
#print axioms frameLatticeForm_virasoro_state
#print axioms frameLatticeForm_virasoro_adjoint
#print axioms lorentzianBilinearForm
#print axioms lorentzianBilinearForm_symmetric
#print axioms lorentzianBilinearForm_nondegenerate
#print axioms lorentzianBilinearForm_normalized
#print axioms lorentzianBilinearForm_virasoro_adjoint
#print axioms lorentzianInvariantForm
#print axioms nearTensorForm_virasoro_adjoint
#print axioms nearTensorInvariantForm
#print axioms moonshineMatterForm
#print axioms moonshineMatterForm_symmetric
#print axioms moonshineMatterForm_normalized
#print axioms moonshineMatterForm_virasoro_adjoint
#print axioms moonshineMatterInvariantForm
#print axioms LorentzianOscillatorMonomial
#print axioms lorentzianStateBasis
#print axioms lorentzianStateBasis_apply
#print axioms lorentzianStateBasis_pair
#print axioms moonshineMatterCoefficient
#print axioms moonshineMatterForm_coefficient
#print axioms moonshineForm_nondegenerate
#print axioms moonshineMatterForm_nondegenerate

end VOA.Moonshine.ConwayNorton
