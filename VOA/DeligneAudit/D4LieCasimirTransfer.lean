import VOA.AffineGeneral.LieData

/-! The adjoint Casimir transfer is independent of concrete bracket data. -/
namespace VOA.DeligneAudit.D4Lie
open VOA.AffineGeneral
noncomputable section
section Transfer

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] {κ : LinearMap.BilinForm ℂ 𝔤}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion in the dual family of a `LieData`. -/
theorem LieData_dual_expand (D : LieData κ ι) (y : 𝔤) : y = ∑ i, κ (D.basis i) y • D.dual i := by
  have hz : y - ∑ i, κ (D.basis i) y • D.dual i = 0 := by
    apply D.form_right_nondegenerate
    intro x
    conv_lhs => rw [← D.reconstruct x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sub,
      LieData.generator, D.pair, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact sub_eq_zero.mp hz

/-- **The adjoint Casimir is independent of the dual pair.** -/
theorem casimir_transfer (D : LieData κ ι) {ι' : Type*} [Fintype ι'] (b' d' : ι' → 𝔤)
    (hexp : ∀ y, y = ∑ j, κ y (d' j) • b' j) (x : 𝔤) :
    ∑ j, ⁅b' j, ⁅d' j, x⁆⁆ = ∑ i, ⁅D.basis i, ⁅D.dual i, x⁆⁆ := by
  have h1 : ∀ j, ⁅b' j, ⁅d' j, x⁆⁆ = ∑ i, κ (D.basis i) (d' j) • ⁅b' j, ⁅D.dual i, x⁆⁆ := by
    intro j
    conv_lhs => rw [LieData_dual_expand D (d' j)]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [hexp (D.basis i)]
  simp only [sum_lie, smul_lie]

end Transfer
end
end VOA.DeligneAudit.D4Lie
