import VOA.Moonshine.MoonshineCNGammaZeroShimizu
import VOA.Moonshine.MoonshineCNGammaZeroCosets
import VOA.Moonshine.MoonshineCNGammaZeroBridge
import VOA.Moonshine.MoonshineCNGammaZeroGalois
import VOA.Moonshine.MoonshineCNGammaZeroFamily

/-! # Audit of the `Γ₁ ⇒ Γ₀` bridge

Headlines: `conwayNorton_of_gammaOne`, `conwayNorton_of_gammaOne_of_finOrder`,
`conwayNortonFor_of_gammaOne`, `replicate_eq_and_diamond_mem`,
`isMoonshineGroup_adjoinNegOne_of_replicable`, `mckayThompsonFun_pow_eq_of_coprime`.
They are conditional on their explicit hypotheses (`ConwayNortonGammaOne`,
`CompletelyReplicable`, finite order), which `#print axioms` does not report.
-/

-- Shimizu and constancy
#print axioms VOA.Moonshine.ConwayNorton.entries_of_two_fixed
#print axioms VOA.Moonshine.ConwayNorton.smul_eq_self_of_scalar
#print axioms VOA.Moonshine.ConwayNorton.exists_smul_ne_of_lowerLeft_ne_zero
#print axioms VOA.Moonshine.ConwayNorton.tendsto_smul_of_entries_tendsto
#print axioms VOA.Moonshine.ConwayNorton.eq_of_invariant_of_frequently_moved
#print axioms VOA.Moonshine.ConwayNorton.eq_of_invariant_of_entries_tendsto_one
#print axioms VOA.Moonshine.ConwayNorton.eq_of_invariant_of_tendsto_one
#print axioms VOA.Moonshine.ConwayNorton.shimizuMatrix_succ_eq
#print axioms VOA.Moonshine.ConwayNorton.shimizuWitness_entries_tendsto
#print axioms VOA.Moonshine.ConwayNorton.shimizuWitness_moves
#print axioms VOA.Moonshine.ConwayNorton.eq_of_invariant_upper_lower_unipotent
-- Hecke coset matching
#print axioms VOA.Moonshine.ConwayNorton.diamondLift_mem_Gamma0
#print axioms VOA.Moonshine.ConwayNorton.diamondLift_mul_upperSL
#print axioms VOA.Moonshine.ConwayNorton.diamond_periodic
#print axioms VOA.Moonshine.ConwayNorton.heckeIndexMap_mem
#print axioms VOA.Moonshine.ConwayNorton.heckeIndexInv_mem
#print axioms VOA.Moonshine.ConwayNorton.heckeIndexInv_map
#print axioms VOA.Moonshine.ConwayNorton.heckeIndexMap_inv
#print axioms VOA.Moonshine.ConwayNorton.heckeIndexMap_dvd
#print axioms VOA.Moonshine.ConwayNorton.heckeShift_lowerSL
#print axioms VOA.Moonshine.ConwayNorton.heckeShift_lowerSL_exceptional
#print axioms VOA.Moonshine.ConwayNorton.diamondScale_lowerSL
#print axioms VOA.Moonshine.ConwayNorton.heckeLevelSum_lowerSL
#print axioms VOA.Moonshine.ConwayNorton.heckeScale_lowerSL
#print axioms VOA.Moonshine.ConwayNorton.diamond_sub_replicate_lowerUnipotent
#print axioms VOA.Moonshine.ConwayNorton.diamond_eq_replicate_add_const
-- Asymptotics, `±Γ`, bridge
#print axioms VOA.Moonshine.ConwayNorton.tendsto_norm_inv_qPar_atTop
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFun_periodic
#print axioms VOA.Moonshine.ConwayNorton.affine_eq_of_normalized
#print axioms VOA.Moonshine.ConwayNorton.replicate_eq_and_diamond_mem
#print axioms VOA.Moonshine.ConwayNorton.gamma0_le_adjoinNegOne_of_replicable
#print axioms VOA.Moonshine.ConwayNorton.isOtherCusp_adjoinNegOne_iff
#print axioms VOA.Moonshine.ConwayNorton.IsNormalizedHauptmodul.adjoinNegOne
#print axioms VOA.Moonshine.ConwayNorton.hasDetOne_adjoinNegOne
#print axioms VOA.Moonshine.ConwayNorton.isMoonshineGroup_adjoinNegOne_of_replicable
#print axioms VOA.Moonshine.ConwayNorton.heckeSum_prime
#print axioms VOA.Moonshine.ConwayNorton.replicatesAtPrime_of_replication
#print axioms VOA.Moonshine.ConwayNorton.completelyReplicableOfFinOrder_of_completelyReplicable
#print axioms VOA.Moonshine.ConwayNorton.conwayNortonFor_of_gammaOne
#print axioms VOA.Moonshine.ConwayNorton.conwayNorton_of_gammaOne_of_finOrder
#print axioms VOA.Moonshine.ConwayNorton.conwayNorton_of_gammaOne
-- Galois invariance
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFun_pow_eq_of_coprime
#print axioms VOA.Moonshine.ConwayNorton.mckayThompsonFun_pow_eq_of_coprime_of_completelyReplicable
-- Abstract replicable families
#print axioms VOA.Moonshine.ConwayNorton.qSeriesFun_periodic
#print axioms VOA.Moonshine.ConwayNorton.ReplicableFamily.replicatesAtPrime
#print axioms VOA.Moonshine.ConwayNorton.ReplicableFamily.isMoonshineGroup_of_gammaOne
#print axioms VOA.Moonshine.ConwayNorton.ReplicableFamily.qSeriesFun_mul_prime_eq
