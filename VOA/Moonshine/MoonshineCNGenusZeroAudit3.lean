/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroAudit2
import VOA.Moonshine.MoonshineCNGenusZeroDiscrete
import VOA.Moonshine.MoonshineCNGenusZeroHeckeStep
import VOA.Moonshine.MoonshineCNGenusZeroLevel
import VOA.Moonshine.MoonshineCNGenusZeroCusps
import VOA.Moonshine.MoonshineCNGenusZeroIndex
import VOA.Moonshine.MoonshineCNGenusZeroSurjective
import VOA.Moonshine.MoonshineCNGenusZeroMain

/-!
# Axiom audit for the files of the genus-zero theorem, third batch (FP side)

One `#print axioms` line per public declaration of `MoonshineCNGenusZero{Discrete, HeckeStep,
Level, Cusps, Index, Surjective, Main}` (the Hecke step, Shimura's finiteness lemma,
rationality, the `Γ₁(N′)` containment, the Hauptmodul fields, and the final assembly; blueprint
`Notes/moonshine/MOON_M8_LEAN.md`). Imports the second-batch audit `MoonshineCNGenusZeroAudit2`
(which imports the first). Expected output for every line:
`[propext, Classical.choice, Quot.sound]`.
The headline theorems are conditional on the explicit hypotheses `hB1` (the prime Hecke identity,
proved on the LR side) and `hD7` (non-injectivity modulo translations, proved on the LR side);
`#print axioms` does not list them.
-/

open VOA.Moonshine.ConwayNorton

-- MoonshineCNGenusZeroDiscrete
#print axioms glFinTwo_mul_apply
#print axioms glFinTwo_det_eq
#print axioms glOfDetOne_apply_zero_zero
#print axioms glOfDetOne_apply_zero_one
#print axioms glOfDetOne_apply_one_zero
#print axioms glOfDetOne_apply_one_one
#print axioms det_entries_of_mem_symmetryGroup
#print axioms glFinTwo_inv_eq
#print axioms conj_glUpperUnipotent
#print axioms glUpperUnipotent_intCast_mem_symmetryGroup
#print axioms neg_one_mem_symmetryGroup
#print axioms eq_one_of_mem_symmetryGroup_of_near
#print axioms abs_mul_sub_mul_le
#print axioms eq_of_mem_symmetryGroup_of_close
#print axioms finite_bounded_mem_symmetryGroup
#print axioms finite_fract_diag_div_lowerLeft
#print axioms finite_fract_upperLeft_div_lowerLeft
#print axioms finite_fract_lowerRight_div_lowerLeft
-- MoonshineCNGenusZeroHeckeStep
#print axioms exists_heckeStep_mem_symmetryGroup
-- MoonshineCNGenusZeroLevel
#print axioms infinite_admissible_primes_gt
#print axioms rat_mul_den_eq_num_real
#print axioms glLowerUnipotent_mul
#print axioms glLowerUnipotent_zero
#print axioms glLowerUnipotent_inv
#print axioms glFinTwo_mul_glUpperUnipotent_apply
#print axioms glUpperUnipotent_mul_glFinTwo_apply
#print axioms exists_rat_upperLeft_div_lowerLeft
#print axioms exists_rat_lowerLeft_sq
#print axioms exists_integral_mem_symmetryGroup
#print axioms exists_mem_symmetryGroup_heckeStep_of_integral
#print axioms exists_glLowerUnipotent_mem_symmetryGroup
#print axioms glLowerUnipotent_intCast_mul_mem
#print axioms exists_mem_symmetryGroup_firstColumn
#print axioms gamma1GL_le_symmetryGroup_of_lowerUnipotent
#print axioms ReplicableFamily.exists_gamma1GL_le_symmetryGroup
-- MoonshineCNGenusZeroCusps
#print axioms im_smul_le_of_det_eq_one
#print axioms det_val_mul_eq_one
#print axioms det_val_inv_eq_one
#print axioms one_le_mul_abs_lowerLeft_of_conj
#print axioms one_le_mul_lowerLeft_sq_of_mem
#print axioms im_le_of_eq_comp_smul
#print axioms exists_bound_comp_smul_of_other
#print axioms periodic_comp_smul_ofComplex
#print axioms cuspData_of_other
#print axioms qSeriesFun_ne_of_tendsto_comp_smul
#print axioms exists_mem_lowerLeft_eq_zero_of_tendsto_eq
#print axioms tendsto_norm_qSeriesFun_atImInfty
#print axioms hasCuspValue_of_tendsto_comp_smul
-- MoonshineCNGenusZeroIndex
#print axioms upperSL_natCast_mem_Gamma
#print axioms Gamma_le_Gamma1_of
#print axioms mapGL_upperSL_natCast
#print axioms conj_glUpperUnipotent_mem_of_gamma1GL_le
#print axioms det_val_mapGL
#print axioms exists_im_bound_norm_sub_ge
#print axioms exists_smul_eq_smul_fd
#print axioms finiteIndex_comap_of_gamma1GL_le
#print axioms exists_im_ge_norm_le_of_isCompact
#print axioms commensurable_symmetryGroup_of_gamma1GL_le
-- MoonshineCNGenusZeroSurjective
#print axioms isOtherCusp_smul_infty
#print axioms exists_SL2Z_of_isOtherCusp
#print axioms nhds_le_map_cuspFunction_of_other
#print axioms surjective_of_gamma1GL_le
-- MoonshineCNGenusZeroMain
#print axioms isNormalizedHauptmodul_symmetryGroup
#print axioms ReplicableFamily.exists_hauptmodul_gammaOne
#print axioms mckayThompsonFun_eq_qSeriesFun_family
#print axioms conwayNortonGammaOne_of_completelyReplicable
#print axioms conwayNorton_of_completelyReplicable
#print axioms conwayNorton_of_completelyReplicable_of_families
