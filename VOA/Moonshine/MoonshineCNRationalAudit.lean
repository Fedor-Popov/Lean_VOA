/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNRationalSchur
import VOA.Moonshine.MoonshineCNRationalRamanujan
import VOA.Moonshine.MoonshineCNRationalTraces
import VOA.Moonshine.MoonshineCNRationalGriess

/-!
# Axiom audit: rationality of `Aut V♮` on `V♮₂`, conditional on the commutant of `Gmat`

One `#print axioms` per public declaration of `MoonshineCNRationalSchur`,
`MoonshineCNRationalRamanujan`, `MoonshineCNRationalTraces` and `MoonshineCNRationalGriess`.

Headline statements:
* `ConwayNorton.rationalTraces : RationalTraces` — no hypotheses.
* `MonsterAction.autVnat_rational_of_commutant (hcomm : GmatCommutantScalar)`.
* `MonsterAction.autVnat_mulEquiv_liftable_of_commutant (hcomm) : AutVnat ≃* liftableSubgroup`.
* `MonsterAction.autVnat_mulEquiv_autO_of_commutant_of_Gmat (hcomm)
  (hGmat : Generated.Gmat = AutO)`.

`#print axioms` does not report explicit hypotheses: the last three are conditional on the named
input `GmatCommutantScalar` (and `Generated.Gmat = AutO` for the last one).
-/

open VOA.Moonshine VOA.Moonshine.MonsterAction VOA.Moonshine.MonsterGriess

-- The named input, printed in full.
#print VOA.Moonshine.MonsterAction.GmatCommutantScalar

-- Headline statements.
#check @VOA.Moonshine.ConwayNorton.rationalTraces
#check @VOA.Moonshine.MonsterAction.autVnat_rational_of_commutant
#check @VOA.Moonshine.MonsterAction.autVnat_mulEquiv_liftable_of_commutant
#check @VOA.Moonshine.MonsterAction.autVnat_mulEquiv_autO_of_commutant_of_Gmat

/-! ## Schur span formula and descent -/
#print axioms VOA.Moonshine.Rationality.groupAverage_commute
#print axioms VOA.Moonshine.Rationality.mul_single_mul_apply
#print axioms VOA.Moonshine.Rationality.groupAverage_eq_smul
#print axioms VOA.Moonshine.Rationality.sum_mul_coeff_eq
#print axioms VOA.Moonshine.Rationality.schur_span_formula
#print axioms VOA.Moonshine.Rationality.dual_ratCast_mul
#print axioms VOA.Moonshine.Rationality.dual_mul_ratCast
#print axioms VOA.Moonshine.Rationality.eq_map_ratCast_of_forall_dual
#print axioms VOA.Moonshine.Rationality.map_dual_mul_mul
#print axioms VOA.Moonshine.Rationality.trace_mul_map_dual
#print axioms VOA.Moonshine.Rationality.eq_map_ratCast_of_rational_traces

/-! ## Ramanujan sums -/
#print axioms VOA.Moonshine.Rationality.sum_divisors_moebius_eq_ite
#print axioms VOA.Moonshine.Rationality.filter_divisors_dvd_eq_divisors_gcd
#print axioms VOA.Moonshine.Rationality.sum_filter_dvd_range_eq
#print axioms VOA.Moonshine.Rationality.sum_coprime_eq_sum_divisors_moebius
#print axioms VOA.Moonshine.Rationality.mul_geom_sum_eq_of_pow_eq_one
#print axioms VOA.Moonshine.Rationality.pow_mul_geom_sum_eq_of_pow_eq_one
#print axioms VOA.Moonshine.Rationality.geom_sum_mul_geom_sum_of_pow_eq_one
#print axioms VOA.Moonshine.Rationality.exists_trace_eq_mul_natCast_of_mul_self
#print axioms VOA.Moonshine.Rationality.exists_trace_geom_sum_eq_of_pow_eq_one
#print axioms VOA.Moonshine.Rationality.exists_rat_trace_of_trace_pow_coprime

/-! ## Rational traces -/
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicable_holds
#print axioms VOA.Moonshine.ConwayNorton.conwayNortonGammaOne_holds
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFun_pow_eq_of_coprime_holds
#print axioms VOA.Moonshine.ConwayNorton.mckayThompson_eq_of_mckayThompsonFun_eq
#print axioms VOA.Moonshine.ConwayNorton.mckayThompson_pow_eq_of_coprime
#print axioms VOA.Moonshine.ConwayNorton.exists_rat_gradedAutTrace
#print axioms VOA.Moonshine.ConwayNorton.exists_rat_gradedAutTrace_two
#print axioms VOA.Moonshine.ConwayNorton.rationalTraces

/-! ## The unit, the fixed line, `Gmat` -/
#print axioms VOA.Moonshine.MonsterAction.gmulA_oneB
#print axioms VOA.Moonshine.MonsterAction.gmulX_oneB
#print axioms VOA.Moonshine.MonsterAction.gmulW_oneB
#print axioms VOA.Moonshine.MonsterAction.gmul_oneB_left
#print axioms VOA.Moonshine.MonsterAction.griessIdentityVec
#print axioms VOA.Moonshine.MonsterAction.griessIdentityVec_eq_smul_oneB
#print axioms VOA.Moonshine.MonsterAction.gmul_griessIdentityVec
#print axioms VOA.Moonshine.MonsterAction.bform_griessIdentityVec_self
#print axioms VOA.Moonshine.MonsterAction.vnatConformalTwo
#print axioms VOA.Moonshine.MonsterAction.griessMul_vnatConformalTwo
#print axioms VOA.Moonshine.MonsterAction.griessMul_griessIdentityVec
#print axioms VOA.Moonshine.MonsterAction.griessNat_griessIdentityVec
#print axioms VOA.Moonshine.MonsterAction.autVnat_apply_griessNat_identityVec
#print axioms VOA.Moonshine.MonsterAction.gmatToLiftable
#print axioms VOA.Moonshine.MonsterAction.gmatLift
#print axioms VOA.Moonshine.MonsterAction.gmatLift_injective
#print axioms VOA.Moonshine.MonsterAction.gmatLift_apply_griessNat
#print axioms VOA.Moonshine.MonsterAction.finite_gmat
#print axioms VOA.Moonshine.MonsterAction.gmat_apply_identityVec

/-! ## The projection `P₀` and the commutant input -/
#print axioms VOA.Moonshine.MonsterAction.griessUnitProj
#print axioms VOA.Moonshine.MonsterAction.griessUnitProj_apply
#print axioms VOA.Moonshine.MonsterAction.griessUnitProj_identityVec
#print axioms VOA.Moonshine.MonsterAction.griessUnitProj_mul_self
#print axioms VOA.Moonshine.MonsterAction.trace_griessUnitProj
#print axioms VOA.Moonshine.MonsterAction.griessUnitProj_apply_gmat
#print axioms VOA.Moonshine.MonsterAction.GmatCommutantScalar
#print axioms VOA.Moonshine.MonsterAction.gmat_commute_griessUnitProj

/-! ## Matrices in the dictionary bases -/
#print axioms VOA.Moonshine.MonsterAction.griessLinear
#print axioms VOA.Moonshine.MonsterAction.griessLinear_griessNat
#print axioms VOA.Moonshine.MonsterAction.griessBasisC_repr_griessNat
#print axioms VOA.Moonshine.MonsterAction.toMatrix_griessLinear
#print axioms VOA.Moonshine.MonsterAction.gmatMatrixRep
#print axioms VOA.Moonshine.MonsterAction.gmatMatrixRep_apply
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict_gmatLift
#print axioms VOA.Moonshine.MonsterAction.gmatMatrixRep_map
#print axioms VOA.Moonshine.MonsterAction.trace_vnatWeightTwoRestrict
#print axioms VOA.Moonshine.MonsterAction.exists_rat_trace_vnatWeightTwoRestrict
#print axioms VOA.Moonshine.MonsterAction.griessLinear_griessUnitProj_apply
#print axioms VOA.Moonshine.MonsterAction.griessLinear_griessUnitProj_mul_restrict
#print axioms VOA.Moonshine.MonsterAction.restrict_mul_griessLinear_griessUnitProj
#print axioms VOA.Moonshine.MonsterAction.griessUnitMatrix
#print axioms VOA.Moonshine.MonsterAction.griessComplMatrix
#print axioms VOA.Moonshine.MonsterAction.griessUnitMatrix_mul_self
#print axioms VOA.Moonshine.MonsterAction.griessUnitMatrix_commute
#print axioms VOA.Moonshine.MonsterAction.griessComplMatrix_mul_unit
#print axioms VOA.Moonshine.MonsterAction.griessComplMatrix_mul_self
#print axioms VOA.Moonshine.MonsterAction.griessComplMatrix_commute
#print axioms VOA.Moonshine.MonsterAction.trace_griessComplMatrix
#print axioms VOA.Moonshine.MonsterAction.trace_griessComplMatrix_ne_zero
#print axioms VOA.Moonshine.MonsterAction.griessComplMatrix_commutant
#print axioms VOA.Moonshine.MonsterAction.vnatMatrix
#print axioms VOA.Moonshine.MonsterAction.griessUnitMatrix_map
#print axioms VOA.Moonshine.MonsterAction.griessUnitMatrix_map_mul_vnatMatrix
#print axioms VOA.Moonshine.MonsterAction.vnatMatrix_mul_griessUnitMatrix_map
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict_mul_coe
#print axioms VOA.Moonshine.MonsterAction.vnatMatrix_mul
#print axioms VOA.Moonshine.MonsterAction.gmatMatrixRep_map_mul_vnatMatrix
#print axioms VOA.Moonshine.MonsterAction.exists_rat_trace_gmat_compl_vnatMatrix

/-! ## Rationality and corollaries -/
#print axioms VOA.Moonshine.MonsterAction.exists_vnatMatrix_eq_map_of_commutant
#print axioms VOA.Moonshine.MonsterAction.autVnat_rational_of_commutant
#print axioms VOA.Moonshine.MonsterAction.monsterLift_surjective_of_commutant
#print axioms VOA.Moonshine.MonsterAction.autVnat_mulEquiv_liftable_of_commutant
#print axioms VOA.Moonshine.MonsterAction.autVnat_mulEquiv_liftable_of_commutant_symm_apply
#print axioms VOA.Moonshine.MonsterAction.nonempty_autVnat_mulEquiv_liftable_of_commutant
#print axioms VOA.Moonshine.MonsterAction.autVnat_mulEquiv_autO_of_commutant_of_Gmat
