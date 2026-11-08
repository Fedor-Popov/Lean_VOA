/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroAnalytic
import VOA.Moonshine.MoonshineCNGenusZeroInterface
import VOA.Moonshine.MoonshineCNGenusZeroTop
import VOA.Moonshine.MoonshineCNGenusZeroShimizu
import VOA.Moonshine.MoonshineCNGenusZeroPairing

/-!
# Axiom audit for the files of the genus-zero theorem (FP side)

One `#print axioms` line per public theorem of `MoonshineCNGenusZero{Analytic, Interface, Top,
Shimizu, Pairing}`. Expected output for every line: `[propext, Classical.choice, Quot.sound]`.
-/

open VOA.Moonshine.ConwayNorton

-- MoonshineCNGenusZeroAnalytic
#print axioms summable_norm_mul_pow_of_summable
#print axioms norm_qPar_eq
#print axioms real_exp_mul_succ
#print axioms summable_jCoeffMajorant_mul_exp
#print axioms jTail_nonneg
#print axioms exp_neg_mul_le_of_le
#print axioms jTail_le_of_le
#print axioms tendsto_jTail_atTop
#print axioms qSeriesFun_eq_inv_add_qTailSeries
#print axioms norm_qTail_term_le
#print axioms summable_qTail_term
#print axioms norm_qTailSeries_le
#print axioms norm_qSeriesFun_sub_inv_qPar_le
#print axioms tendsto_qSeriesFun_sub_inv_qPar
#print axioms mdifferentiable_qSeriesFun
#print axioms norm_pow_sub_pow_le_of_norm_le
#print axioms norm_qTailSeries_sub_le
#print axioms summable_lipschitz_majorant
#print axioms exists_height_injective
#print axioms ReplicableFamily.isJDominated
#print axioms ReplicableFamily.mdifferentiable
#print axioms ReplicableFamily.tendsto_sub_inv_qPar
#print axioms ReplicableFamily.c_add_mul
#print axioms ReplicableFamily.c_eq_of_modEq
#print axioms ReplicableFamily.c_mul_eq_of_modEq_one

-- MoonshineCNGenusZeroInterface
#print axioms ReplicableFamily.exists_monic_eval_eq_heckeOrbitSum
#print axioms mem_symmetryGroup
#print axioms hasDetOne_symmetryGroup

-- MoonshineCNGenusZeroTop
#print axioms qTailSeries_differentiableOn
#print axioms exists_large_values_from_height
#print axioms largeValuesFromTop_qSeriesFun
#print axioms ReplicableFamily.largeValuesFromTop

-- MoonshineCNGenusZeroShimizu
#print axioms shimizuMatrixFrom_entry00
#print axioms shimizuMatrixFrom_entry10
#print axioms shimizuMatrixFrom_det
#print axioms shimizuMatrixFrom_succ_mul
#print axioms shimizuMatrixFrom_mem
#print axioms shimizuWitnessFrom_mem
#print axioms shimizuWitnessFrom_val
#print axioms shimizuWitnessFrom_det
#print axioms shimizuPairFrom_snd_ne_zero
#print axioms shimizuPairFrom_snd_abs_le
#print axioms shimizuPairFrom_fst_abs_le
#print axioms shimizuPairFrom_fst_tendsto
#print axioms shimizuWitnessFrom_entries_tendsto
#print axioms shimizuWitnessFrom_moves
#print axioms eq_of_invariant_of_lowerLeft_abs_lt_one
#print axioms det_val_eq_one_of_mem_symmetryGroup
#print axioms one_le_abs_lowerLeft_of_mem_symmetryGroup
#print axioms glUpperUnipotent_one_mem_symmetryGroup_qSeriesFun
#print axioms qSeriesFun_exists_ne
#print axioms one_le_abs_lowerLeft_qSeriesFun

-- MoonshineCNGenusZeroPairing
#print axioms forall_poly_of_monic_basis
#print axioms eval_prod_X_sub_C
#print axioms mem_of_forall_sum_eval_eq
#print axioms sum_map_eval_heckeValues
#print axioms exists_poly_heckeValueSum
#print axioms heckeValues_pairing
#print axioms mem_heckeValues_iff
#print axioms hecke_pairing_shift
#print axioms hecke_pairing_scale
