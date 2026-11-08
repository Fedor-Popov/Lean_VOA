/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNMonsterActionMoonshine
import VOA.Moonshine.MoonshineCNMonsterActionExtra

/-! Axiom audit for the lift of the rational Monster `AutO` to `Aut V♮`
(`MoonshineCNMonsterAction*`): one `#print axioms` per public declaration. -/

-- MoonshineCNMonsterActionConj
#print axioms VOA.Moonshine.MonsterAction.griessBaseChange
#print axioms VOA.Moonshine.MonsterAction.griessBaseChange_tmul
#print axioms VOA.Moonshine.MonsterAction.griessBaseChange_gmul
#print axioms VOA.Moonshine.MonsterAction.griessBaseChange_bform
#print axioms VOA.Moonshine.MonsterAction.griessBaseChange_mul
#print axioms VOA.Moonshine.MonsterAction.griessConj
#print axioms VOA.Moonshine.MonsterAction.griessConj_apply
#print axioms VOA.Moonshine.MonsterAction.griessConj_griessIso
#print axioms VOA.Moonshine.MonsterAction.griessConj_griessNat
#print axioms VOA.Moonshine.MonsterAction.griessConj_one
#print axioms VOA.Moonshine.MonsterAction.griessConj_mul
#print axioms VOA.Moonshine.MonsterAction.griessConjHom
#print axioms VOA.Moonshine.MonsterAction.griessConjHom_apply
#print axioms VOA.Moonshine.MonsterAction.griessNat_injective
#print axioms VOA.Moonshine.MonsterAction.griessConjHom_injective
#print axioms VOA.Moonshine.MonsterAction.griessConj_griessMul
#print axioms VOA.Moonshine.MonsterAction.griessConj_natForm
#print axioms VOA.Moonshine.MonsterAction.griessForm_eq_natForm
#print axioms VOA.Moonshine.MonsterAction.natForm_autRestrict
#print axioms VOA.Moonshine.MonsterAction.griessConj_griessForm
#print axioms VOA.Moonshine.MonsterAction.griessConj_mem_griessAutVnat
#print axioms VOA.Moonshine.MonsterAction.griessConjAut
#print axioms VOA.Moonshine.MonsterAction.griessConjAut_coe
#print axioms VOA.Moonshine.MonsterAction.griessConjAut_injective
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict_apply_coe
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict_eq
#print axioms VOA.Moonshine.MonsterAction.vnatWeightTwoRestrict_injective

-- MoonshineCNMonsterActionLift
#print axioms VOA.Moonshine.MonsterAction.IsVnatLiftable
#print axioms VOA.Moonshine.MonsterAction.liftableSubgroup
#print axioms VOA.Moonshine.MonsterAction.mem_liftableSubgroup
#print axioms VOA.Moonshine.MonsterAction.isVnatLiftable_one
#print axioms VOA.Moonshine.MonsterAction.IsVnatLiftable.mul
#print axioms VOA.Moonshine.MonsterAction.IsVnatLiftable.inv
#print axioms VOA.Moonshine.MonsterAction.subgroupClosure_le_liftable
#print axioms VOA.Moonshine.MonsterAction.subgroupClosure_insert_le_liftable
#print axioms VOA.Moonshine.MonsterAction.isVnatLiftable_of_closure_eq_top
#print axioms VOA.Moonshine.MonsterAction.monsterLift
#print axioms VOA.Moonshine.MonsterAction.monsterLift_griessRestrict
#print axioms VOA.Moonshine.MonsterAction.monsterLift_restrict
#print axioms VOA.Moonshine.MonsterAction.monsterLift_apply_griessNat
#print axioms VOA.Moonshine.MonsterAction.monsterLift_unique
#print axioms VOA.Moonshine.MonsterAction.monsterLift_injective
#print axioms VOA.Moonshine.MonsterAction.monsterLiftOfAll
#print axioms VOA.Moonshine.MonsterAction.monsterLiftOfAll_restrict
#print axioms VOA.Moonshine.MonsterAction.monsterLiftOfAll_injective
#print axioms VOA.Moonshine.MonsterAction.linearMap_ext_griessNat
#print axioms VOA.Moonshine.MonsterAction.rationalPart
#print axioms VOA.Moonshine.MonsterAction.rationalPart_spec
#print axioms VOA.Moonshine.MonsterAction.griessNat_coe_injective
#print axioms VOA.Moonshine.MonsterAction.autVnat_map_add
#print axioms VOA.Moonshine.MonsterAction.autVnat_map_smul
#print axioms VOA.Moonshine.MonsterAction.rationalPartLinear
#print axioms VOA.Moonshine.MonsterAction.rationalPartLinear_injective
#print axioms VOA.Moonshine.MonsterAction.rationalPartEquiv
#print axioms VOA.Moonshine.MonsterAction.rationalPartEquiv_spec
#print axioms VOA.Moonshine.MonsterAction.rationalPartEquiv_mem_autO
#print axioms VOA.Moonshine.MonsterAction.isVnatLiftable_of_rational
#print axioms VOA.Moonshine.MonsterAction.mem_range_monsterLift_iff
#print axioms VOA.Moonshine.MonsterAction.autVnat_mulEquiv_autO_of_liftable_of_rational

-- MoonshineCNMonsterActionMoonshine
#print axioms VOA.Moonshine.MonsterAction.conwayNorton_liftable
#print axioms VOA.Moonshine.MonsterAction.conwayNortonVia_monsterLift
#print axioms VOA.Moonshine.MonsterAction.trace_griessConj
#print axioms VOA.Moonshine.MonsterAction.mckayThompson_monsterLift_coeff_one
#print axioms VOA.Moonshine.MonsterAction.mckayThompsonFun_eq_of_restrict
#print axioms VOA.Moonshine.MonsterAction.conwayNorton_monster_of_isVnatLiftable
#print axioms VOA.Moonshine.MonsterAction.conwayNorton_monster_of_liftable
#print axioms VOA.Moonshine.MonsterAction.conwayNorton_autO_of_closure
#print axioms VOA.Moonshine.MonsterAction.conwayNorton_autO_of_generators

-- MoonshineCNMonsterActionExtra
#print axioms VOA.Moonshine.MonsterAction.extraSpinPhase_mul_self
#print axioms VOA.Moonshine.MonsterAction.exists_extraSign
#print axioms VOA.Moonshine.MonsterAction.extraPlusIsometry_spinTopState
#print axioms VOA.Moonshine.MonsterAction.extraScalar_smul_spinOp
#print axioms VOA.Moonshine.MonsterAction.extraPlusIsometry_spinDict
#print axioms VOA.Moonshine.MonsterAction.extraVnatAut_griessNat
#print axioms VOA.Moonshine.MonsterAction.extraVnatAut_mem_range_monsterLift
#print axioms VOA.Moonshine.MonsterAction.exists_monsterLift_eq_extraVnatAut
#print axioms VOA.Moonshine.MonsterAction.extraSign
#print axioms VOA.Moonshine.MonsterAction.extraSign_eq_one_or
#print axioms VOA.Moonshine.MonsterAction.extraSign_cast
#print axioms VOA.Moonshine.MonsterAction.extraLiftable
#print axioms VOA.Moonshine.MonsterAction.monsterLift_extraLiftable
#print axioms VOA.Moonshine.MonsterAction.extraLiftable_apply
