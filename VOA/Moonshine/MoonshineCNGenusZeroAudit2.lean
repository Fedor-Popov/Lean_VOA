/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroAudit
import VOA.Moonshine.MoonshineCNGenusZeroPartner
import VOA.Moonshine.MoonshineCNGenusZeroLocal
import VOA.Moonshine.MoonshineCNGenusZeroOverlap
import VOA.Moonshine.MoonshineCNGenusZeroODE
import VOA.Moonshine.MoonshineCNGenusZeroBoundary
import VOA.Moonshine.MoonshineCNGenusZeroFamilies
import VOA.Moonshine.MoonshineCNGenusZeroExtension
import VOA.Moonshine.MoonshineCNGenusZeroClassification
import VOA.Moonshine.MoonshineCNGenusZeroMoebius
import VOA.Moonshine.MoonshineCNGenusZeroPropertyP
import VOA.Moonshine.MoonshineCNGenusZeroCritical
import VOA.Moonshine.MoonshineCNGenusZeroGroup

/-!
# Axiom audit for the files of the genus-zero theorem, second batch (FP side)

One `#print axioms` line per public theorem of `MoonshineCNGenusZero{Partner, Local, Overlap, ODE,
Boundary, Families, Extension, Classification, Moebius, PropertyP, Critical, Group}` (partner
uniqueness and pairing on connected domains, local symmetries are real Möbius maps, property P,
and the stabiliser of `∞`; blueprint `Notes/moonshine/MOON_M8_LEAN.md`).
Imports the first-batch audit `MoonshineCNGenusZeroAudit`. Expected output for every line:
`[propext, Classical.choice, Quot.sound]`.
-/

open VOA.Moonshine.ConwayNorton

-- MoonshineCNGenusZeroPartner
#print axioms affC_apply
#print axioms affC_re
#print axioms affC_im
#print axioms affC_affC
#print axioms affC_one_zero
#print axioms affC_inv_affC
#print axioms affC_affC_inv
#print axioms differentiable_affC
#print axioms continuous_affC
#print axioms affC_im_pos
#print axioms norm_affC_sub_le
#print axioms heckeDil_pos
#print axioms heckeDil_eq_zpow
#print axioms heckeAffine_im_pos
#print axioms heckeAffine_some_coe
#print axioms heckeAffine_none_coe
#print axioms qSeriesExt_coe
#print axioms qSeriesExt_of_im_pos
#print axioms differentiableOn_qSeriesExt
#print axioms qSeriesExt_add_intCast
#print axioms topHeight_pos
#print axioms exists_int_of_qSeriesExt_eq
#print axioms heckeAffine_pairing_coe
#print axioms heckeAffine_pairing
#print axioms exists_heckeAffine_partner
#print axioms exists_iterate_heckeAffine_partner
#print axioms heckeAffine_eq_of_frequently_eq
-- MoonshineCNGenusZeroLocal
#print axioms exists_localSymmetry_of_deriv_ne_zero
#print axioms not_lt_of_intValued_aux
#print axioms eq_of_continuousOn_intValued
#print axioms exists_int_eq_add_of_top
#print axioms exists_affC_eqOn_of_top
-- MoonshineCNGenusZeroOverlap
#print axioms im_pos_of_mem_ball
#print axioms zpow_ne_pow_of_prime_ne
#print axioms exists_intertwining_of_relations
#print axioms exists_intertwining_of_not_realAffine
-- MoonshineCNGenusZeroODE
#print axioms exists_real_of_tendsto_ofReal
#print axioms exists_real_linear_ode
-- MoonshineCNGenusZeroBoundary
#print axioms eq_of_comp_eq_of_mapsTo_compact
#print axioms norm_affC_sub_affC
#print axioms injOn_affC_comp
#print axioms qSeriesExt_exists_ne
#print axioms false_of_halfDisc_symmetry
-- MoonshineCNGenusZeroFamilies
#print axioms sub_ofReal_mem_slitPlane
#print axioms sub_ofReal_ne_zero
#print axioms exists_const_of_hasDerivAt_zero
#print axioms hasDerivAt_of_differentiableOn
#print axioms eqOn_power_of_ode
#print axioms eqOn_log_of_ode
#print axioms eqOn_exp_of_ode
#print axioms eqOn_affine_of_ode
#print axioms eqOn_explicit_of_real_linear_ode
-- MoonshineCNGenusZeroExtension
#print axioms forall_im_pos_and_eq_of_local
-- MoonshineCNGenusZeroClassification
#print axioms norm_qSeriesExt_le
#print axioms le_norm_qSeriesExt
#print axioms lt_norm_qSeriesExt_of_le_im
#print axioms false_of_exp_family
#print axioms false_of_log_family
#print axioms exists_int_of_affine_family
#print axioms ofReal_mul_exp_cpow
#print axioms ofReal_mul_I_cpow
#print axioms im_mul_exp_ofReal_mul_I
#print axioms im_mul_exp_pos_of_power_into
#print axioms abs_le_one_of_sin_pos
#print axioms exists_pos_real_of_mul_into
#print axioms exists_neg_real_of_mul_inv_into
#print axioms im_power_family_vertical
#print axioms false_of_power_family_of_pos_of_lt_one
#print axioms sin_nonneg_endpoints
#print axioms exists_tendsto_power_family_of_neg
#print axioms false_of_power_family_of_neg_of_gt_neg_one
#print axioms power_family_cases
-- MoonshineCNGenusZeroMoebius
#print axioms coe_glOfDetOne_smul
#print axioms glOfDetOne_mem_symmetryGroup_of
#print axioms isMoebiusSymmetryOn_of_affine
#print axioms isMoebiusSymmetryOn_of_inv
#print axioms deriv_eq_of_eqOn_nhds
#print axioms isMoebiusSymmetryOn_of_localSymmetry
-- MoonshineCNGenusZeroPropertyP
#print axioms moebius_denom_ne_zero
#print axioms exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero
#print axioms exists_mem_symmetryGroup_smul_eq_of_not_both_critical
-- MoonshineCNGenusZeroCritical
#print axioms not_eventually_eq_qSeriesExt
#print axioms eventually_deriv_qSeriesExt_ne_zero
#print axioms abs_le_sq_add_one
#print axioms exists_bound_entries_of_smul_eq
#print axioms exists_mem_symmetryGroup_smul_eq
-- MoonshineCNGenusZeroGroup
#print axioms exists_int_smul_eq_add_of_lowerLeft_eq_zero
