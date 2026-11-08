import VOA.Moonshine.MoonshineCNAudit15
import VOA.Moonshine.MoonshineCNNearOppositeComul
import VOA.Moonshine.MoonshineCNNearOppositeLeft
import VOA.Moonshine.MoonshineCNNearOppositeRight
import VOA.Moonshine.MoonshineCNNearOppositeIterate
import VOA.Moonshine.MoonshineCNMonsterLieInvariance

/-! Kernel dependency audit for the opposite iterate identity of near-VOAs with locally
nilpotent `L₁` and the hypothesis-free Lie invariance of the Monster Lie algebra form. -/

#print axioms VOA.NearVOA.smul_smul_scalar_left
#print axioms VOA.NearVOA.virasoroOne_smul_of_mem_weight
#print axioms VOA.NearVOA.virasoroOneBracket
#print axioms VOA.NearVOA.virasoroOneBracket_apply
#print axioms VOA.NearVOA.virasoroOneBracket_mode_of_mem_weight
#print axioms VOA.NearVOA.virasoroOneBracket_pow_mode_of_mem_weight
#print axioms VOA.NearVOA.virasoroOne_mul_eq
#print axioms VOA.NearVOA.virasoroOne_pow_mul_eq_sum
#print axioms VOA.NearVOA.virasoroOne_pow_smul_eq_sum
#print axioms VOA.NearVOA.smulLeftLinear
#print axioms VOA.NearVOA.smulLeftLinear_apply
#print axioms VOA.NearVOA.smul_smul_skew
#print axioms VOA.NearVOA.finsum_sum_sum_comm
#print axioms VOA.NearVOA.oppositeModeAtWeight_apply_eq_sum
#print axioms VOA.NearVOA.oppositeModeAtWeight_comp_eq_sum
#print axioms VOA.NearVOA.oppositePair_jacobi_term
#print axioms VOA.NearVOA.oppositePair_term_finite
#print axioms VOA.NearVOA.oppositePair_borcherds_eq_blocks
#print axioms VOA.NearVOA.smul_virasoroOne_pow_smul_eq_sum
#print axioms VOA.NearVOA.triangle_sum_eq_box
#print axioms VOA.NearVOA.finsum_nat_shift
#print axioms VOA.NearVOA.oppositeTowerVector
#print axioms VOA.NearVOA.oppositeTowerCoeff
#print axioms VOA.NearVOA.oppositeProductCoeff
#print axioms VOA.NearVOA.oppositePairCoeff_collapse
#print axioms VOA.NearVOA.oppositeProductCoeff_collapse
#print axioms VOA.NearVOA.oppositeTowerVector_eventually_zero
#print axioms VOA.NearVOA.oppositePairIterate_eq_tower
#print axioms VOA.NearVOA.cbz_smul_oppositeModeAtWeight_product_eq
#print axioms VOA.NearVOA.oppositeProduct_borcherds_eq_blocks
#print axioms VOA.NearVOA.oppositeModeAtWeight_borcherds
#print axioms VOA.NearVOA.oppositeModeAtWeight_iterate
#print axioms VOA.NearVOA.oppositeIterateSum
#print axioms VOA.NearVOA.oppositeIterateSum_zero_left
#print axioms VOA.NearVOA.oppositeIterateSum_zero_right
#print axioms VOA.NearVOA.oppositeIterateSum_add_left
#print axioms VOA.NearVOA.oppositeIterateSum_add_right
#print axioms VOA.NearVOA.oppositeIterateIdentity_of_locallyNilpotent
#print axioms VOA.NearVOA.adjoint_of_locallyNilpotent_generators
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterNearVOA_oppositeIterateIdentity
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterOppositeModes_adjoint
#print axioms VOA.Moonshine.ConwayNorton.moonshineMatterForm_primary_zeroMode_skew
#print axioms VOA.Moonshine.ConwayNorton.monsterLieBilinearForm_invariant

open VOA.Moonshine.ConwayNorton in
example (u v w : monsterLieAlgebra) :
    monsterLieBilinearForm ⁅u, v⁆ w = monsterLieBilinearForm u ⁅v, w⁆ :=
  monsterLieBilinearForm_invariant u v w

example {H : Type*} [AddCommGroup H] [Module ℂ H] (V : VOA.NearVOA H)
    (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0) : V.OppositeIterateIdentity hNil :=
  V.oppositeIterateIdentity_of_locallyNilpotent hNil

#check @VOA.NearVOA.oppositeModeAtWeight_borcherds
#check @VOA.NearVOA.adjoint_of_locallyNilpotent_generators
#check @VOA.Moonshine.ConwayNorton.monsterLieBilinearForm_invariant
