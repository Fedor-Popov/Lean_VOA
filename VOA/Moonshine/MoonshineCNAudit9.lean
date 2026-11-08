import VOA.Moonshine.MoonshineCNAudit8
import VOA.Moonshine.MoonshineCNNearGoddard
import VOA.Moonshine.MoonshineCNNearTranslation
import VOA.Moonshine.MoonshineCNNearNthProduct
import VOA.Moonshine.MoonshineCNNearIterate
import VOA.Moonshine.MoonshineCNNearBorcherds
import VOA.Moonshine.MoonshineCNNearSkew
import VOA.Moonshine.MoonshineCNNearConsequences
import VOA.Moonshine.MoonshineCNNearMatterIdentities
import VOA.Moonshine.MoonshineCNSectorFormConvention

/-! Kernel dependency audit of the near-VOA mode identities and sector form convention. -/

#print axioms VOA.NearVOA.smul
#print axioms VOA.NearVOA.smul_def
#print axioms VOA.NearVOA.L
#print axioms VOA.NearVOA.L_def
#print axioms VOA.NearVOA.T
#print axioms VOA.NearVOA.smul_neg_one_vacuum
#print axioms VOA.NearVOA.smul_vacuum_eq_zero
#print axioms VOA.NearVOA.localε_one
#print axioms VOA.NearVOA.Y_apply_vacuum_eq_zero
#print axioms VOA.NearVOA.Y_apply_vacuum_zero
#print axioms VOA.NearVOA.goddardDifference
#print axioms VOA.NearVOA.goddardDifference_apply
#print axioms VOA.NearVOA.goddard_pointwiseε
#print axioms VOA.NearVOA.goddard_uniqueness
#print axioms VOA.NearVOA.dong_fields

#print axioms VOA.NearVOA.Y_Tr
#print axioms VOA.NearVOA.mode_Y_Tr
#print axioms VOA.NearVOA.L_neg_one_vacuum
#print axioms VOA.NearVOA.creation_pow
#print axioms VOA.NearVOA.L_neg_one_smul_vacuum
#print axioms VOA.NearVOA.isField_Y
#print axioms VOA.NearVOA.Y_omega_neg_one
#print axioms VOA.NearVOA.cCoeff_zero_omega
#print axioms VOA.NearVOA.translation_covariance
#print axioms VOA.NearVOA.L_comm_Ycoeff
#print axioms VOA.NearVOA.L_comm_mode
#print axioms VOA.NearVOA.L_neg_one_deriv
#print axioms VOA.NearVOA.Y_Tpow
#print axioms VOA.NearVOA.smul_T_apply
#print axioms VOA.NearVOA.smul_Tpow
#print axioms VOA.NearVOA.smul_Tpow_neg_one

#print axioms VOA.NearVOA.commT_bracketDistε
#print axioms VOA.NearVOA.L_comm_cCoeffε
#print axioms VOA.NearVOA.applyVec_bracketDistε_quadrant
#print axioms VOA.NearVOA.cCoeff_apply_vacuumε
#print axioms VOA.NearVOA.cCoeff_vacuum_negε
#print axioms VOA.NearVOA.cCoeff_vacuum_baseε
#print axioms VOA.NearVOA.cCoeff_vacuum_eqε
#print axioms VOA.NearVOA.nth_product
#print axioms VOA.NearVOA.modeBracketε
#print axioms VOA.NearVOA.modeBracketε_apply
#print axioms VOA.NearVOA.modeBracketε_eq
#print axioms VOA.NearVOA.bracket_deltaSum
#print axioms VOA.NearVOA.mode_bracket_opeε
#print axioms VOA.NearVOA.commutator_bound
#print axioms VOA.NearVOA.mode_commutator
#print axioms VOA.NearVOA.mode_iterate_nonneg_choose
#print axioms VOA.NearVOA.mode_iterate_nonneg
#print axioms VOA.NearVOA.mode_iterate_borcherds_nonneg

#print axioms VOA.NearVOA.dcov_Y
#print axioms VOA.NearVOA.vacuum_recursion_eq
#print axioms VOA.NearVOA.deriv_pow_Y_vacuum_neg
#print axioms VOA.NearVOA.assoc_neg
#print axioms VOA.NearVOA.assoc_neg_mode_expand
#print axioms VOA.NearVOA.mode_iterate_neg
#print axioms VOA.NearVOA.mode_iterate

#print axioms VOA.NearVOA.smul_zero_right
#print axioms VOA.NearVOA.smul_zero_left
#print axioms VOA.NearVOA.borcherdsIterateSum
#print axioms VOA.NearVOA.borcherdsForwardSum
#print axioms VOA.NearVOA.borcherdsReverseSum
#print axioms VOA.NearVOA.borcherdsProductSum
#print axioms VOA.NearVOA.borcherdsIterateSum_fin
#print axioms VOA.NearVOA.borcherdsForwardSum_fin
#print axioms VOA.NearVOA.borcherdsReverseSum_fin
#print axioms VOA.NearVOA.borcherdsForwardSum_fin'
#print axioms VOA.NearVOA.borcherdsReverseSum_fin'
#print axioms VOA.NearVOA.borcherdsIterateSum_rec
#print axioms VOA.NearVOA.borcherdsForwardSum_rec
#print axioms VOA.NearVOA.borcherdsReverseSum_rec
#print axioms VOA.NearVOA.borcherdsProductSum_rec
#print axioms VOA.NearVOA.borcherdsIterateSum_zero
#print axioms VOA.NearVOA.borcherdsProductSum_as_finsum
#print axioms VOA.NearVOA.borcherds_base
#print axioms VOA.NearVOA.borcherds_boundary
#print axioms VOA.NearVOA.borcherds
#print axioms VOA.NearVOA.jacobi

#print axioms VOA.NearVOA.smul_eq_skew

#print axioms VOA.NearVOA.mode_commutator_lie
#print axioms VOA.NearVOA.mode_commutator_apply
#print axioms VOA.NearVOA.zeroMode_derivation
#print axioms VOA.NearVOA.primary_comm
#print axioms VOA.NearVOA.spurious
#print axioms VOA.NearVOA.primary_zeroMode_commutes
#print axioms VOA.NearVOA.zeroMode_preserves_spurious
#print axioms VOA.NearVOA.skew_zero

#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_commutator
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_jacobi
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_skew
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_zeroMode_derivation
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_primary_comm
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_zeroMode_preserves_spurious
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatter_skew_zero
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_commutator
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_jacobi
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_skew
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_zeroMode_derivation
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_primary_comm
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_zeroMode_preserves_spurious
#print axioms VOA.Moonshine.ConwayNorton.lorentzian_skew_zero

#print axioms VOA.Moonshine.ConwayNorton.lorentzianForm_momentum_orthogonal
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_momentum_orthogonal
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_same_momentum_zero
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_opposite_ground
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterSector_no_same_momentum_isometry

