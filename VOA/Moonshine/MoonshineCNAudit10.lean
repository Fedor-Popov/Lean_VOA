import VOA.Moonshine.MoonshineCNAudit9
import VOA.Moonshine.MoonshineCNPhysicalLie
import VOA.Moonshine.MoonshineCNPhysicalMaps
import VOA.Moonshine.MoonshineCNMonsterLie
import VOA.Moonshine.MoonshineCNMonsterGrading
import VOA.Moonshine.MoonshineCNSectorFrame
import VOA.Moonshine.MoonshineCNMatterSectorEquiv
import VOA.Moonshine.MoonshineCNMomentumReversal

/-! Kernel dependency audit of the physical Lie algebra, momentum grading, sector frame,
Aut(V♮) action, and momentum-reversal normalization. -/

#print axioms VOA.NearVOA.primaryWeightOne
#print axioms VOA.NearVOA.primary_zeroMode_closed
#print axioms VOA.NearVOA.primaryZeroProduct
#print axioms VOA.NearVOA.primarySpurious
#print axioms VOA.NearVOA.negativeVirasoro_mem_spurious
#print axioms VOA.NearVOA.primarySpurious_right
#print axioms VOA.NearVOA.primarySpurious_left
#print axioms VOA.NearVOA.primary_zeroMode_self_spurious
#print axioms VOA.NearVOA.primary_zeroMode_leibniz
#print axioms VOA.NearVOA.primaryLieQuotient
#print axioms VOA.NearVOA.primaryLieBracket
#print axioms VOA.NearVOA.primaryQuotient_mk_bracket
#print axioms VOA.NearVOA.primaryLieRing
#print axioms VOA.NearVOA.primaryLieAlgebra
#print axioms VOA.NearVOA.primarySpurious_map
#print axioms VOA.NearVOA.primaryLinearMap
#print axioms VOA.NearVOA.primaryQuotientMap
#print axioms VOA.NearVOA.primaryQuotientMap_mk
#print axioms VOA.NearVOA.primaryQuotientLieEquiv
#print axioms VOA.Moonshine.ConwayNorton.monsterPhysicalAddCommGroup
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAlgebra
#print axioms VOA.Moonshine.ConwayNorton.monsterLieRing
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAlgebraComplex
#print axioms VOA.Moonshine.ConwayNorton.monsterLieProjection
#print axioms VOA.Moonshine.ConwayNorton.monsterLieProjection_ker
#print axioms VOA.Moonshine.ConwayNorton.monsterLieProjection_bracket
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentum
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentum_bracket
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterAut
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterAut_field
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterAut_virasoro
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterAut_momentum
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAutomorphismGroup
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAut
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAut_mk
#print axioms VOA.Moonshine.ConwayNorton.monsterLieAut_momentum
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterConformal_momentum
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterVirasoro_momentum
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumDecomposition
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumComponent
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumComponent_mem
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumComponent_of_mem
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumComponent_of_mem_ne
#print axioms VOA.Moonshine.ConwayNorton.matterMomentumComponent_virasoro
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentumComponent
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentumComponent_mem
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentumComponent_of_mem
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentumComponent_of_mem_ne
#print axioms VOA.Moonshine.ConwayNorton.monsterLieMomentum_isInternal
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianFrameForward
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianFrameBackward
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianFrame_forward_backward
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianFrame_backward_forward
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianFrameEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianPolynomialEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianPolynomial_X_zero
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianPolynomial_X_one
#print axioms VOA.Moonshine.ConwayNorton.lorentzianSectorFockEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianSectorEquiv
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianSectorEquiv_apply
#print axioms VOA.Moonshine.ConwayNorton.lorentzianHeisenberg_zeroMode
#print axioms VOA.Moonshine.ConwayNorton.hypLorentzianSector_zeroCharges
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorMap
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorInverse
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorMap_tmul
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorInverse_tmul
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorMap_mem
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSector_leftInverse
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSector_rightInverse
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorEquiv
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorEquiv_tmul
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSectorEquiv_equivariant
#print axioms VOA.Moonshine.ConwayNorton.sigmaN_sugawaraTerm
#print axioms VOA.Moonshine.ConwayNorton.sigmaN_virasoro
#print axioms VOA.Moonshine.ConwayNorton.lorentzianReversal_frameOscillator
#print axioms VOA.Moonshine.ConwayNorton.lorentzianReversal_virasoro
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal_tmul
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal_involutive
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal_momentum
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal_virasoro
#print axioms VOA.Moonshine.ConwayNorton.lorentzianReversal_form
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterReversal_sector_pairing
