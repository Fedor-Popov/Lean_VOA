import VOA.Moonshine.MoonshineCNTensorFields

/-! The sum of the factor conformal vectors has the sum of the central charges. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open Module (End)
open TensorFieldLift

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem nearTensorField_first_vacuum (V : NearVOA A) (W : NearVOA B) (a : A) :
    nearTensorField V W (a ⊗ₜ W.vacuum) = firstField (V.Y a) := by
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [nearTensorField_tmul_apply, W.vacuum_Y, firstField_tmul,
    finsum_eq_single _ s]
  · simp [FormalDist.one_apply]
  · intro m hm
    rw [FormalDist.one_apply, if_neg (by omega : s - m ≠ 0), LinearMap.zero_apply,
      TensorProduct.tmul_zero]

theorem nearTensorField_second_vacuum (V : NearVOA A) (W : NearVOA B) (b : B) :
    nearTensorField V W (V.vacuum ⊗ₜ b) = secondField (W.Y b) := by
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [nearTensorField_tmul_apply, V.vacuum_Y, secondField_tmul,
    finsum_eq_single _ 0]
  · simp [FormalDist.one_apply]
  · intro m hm
    rw [FormalDist.one_apply, if_neg hm, LinearMap.zero_apply, TensorProduct.zero_tmul]

theorem nearTensorField_vacuum (V : NearVOA A) (W : NearVOA B) :
    nearTensorField V W (V.vacuum ⊗ₜ W.vacuum) = 1 := by
  rw [nearTensorField_first_vacuum, V.vacuum_Y]
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [firstField_tmul, FormalDist.one_apply, FormalDist.one_apply]
  split_ifs <;> simp

/-- The usual factorwise action of the Virasoro algebra. -/
noncomputable def nearVirasoroMode (V : NearVOA A) (n : ℤ) : End ℂ A :=
  mode (V.Y V.conformalVector) (n + 1)

/-- The conformal vector on the tensor carrier. -/
noncomputable def nearTensorConformalVector (V : NearVOA A) (W : NearVOA B) : A ⊗[ℂ] B :=
  V.conformalVector ⊗ₜ W.vacuum + V.vacuum ⊗ₜ W.conformalVector

theorem nearTensorField_conformal (V : NearVOA A) (W : NearVOA B) :
    nearTensorField V W (nearTensorConformalVector V W) =
      firstField (V.Y V.conformalVector) + secondField (W.Y W.conformalVector) := by
  rw [nearTensorConformalVector, map_add,
    nearTensorField_first_vacuum, nearTensorField_second_vacuum]

theorem nearTensorField_conformal_mode (V : NearVOA A) (W : NearVOA B) (n : ℤ) :
    mode (nearTensorField V W (nearTensorConformalVector V W)) (n + 1) =
      tensorTranslation (nearVirasoroMode V n) (nearVirasoroMode W n) := by
  rw [nearTensorField_conformal]
  rfl

theorem nearTensorOperator_commutator (a a' : End ℂ A) (b b' : End ℂ B) :
    ⁅tensorTranslation a b, tensorTranslation a' b'⁆ =
      tensorTranslation ⁅a, a'⁆ ⁅b, b'⁆ := by
  apply TensorProduct.ext'
  intro x y
  simp only [tensorTranslation, Ring.lie_def, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- The central term is the sum of the two factor central charges. -/
theorem nearTensorField_virasoro (V : NearVOA A) (W : NearVOA B) (m n : ℤ) :
    ⁅mode (nearTensorField V W (nearTensorConformalVector V W)) (m + 1),
      mode (nearTensorField V W (nearTensorConformalVector V W)) (n + 1)⁆ =
      ((m : ℂ) - n) •
        mode (nearTensorField V W (nearTensorConformalVector V W)) (m + n + 1) +
      (if m + n = 0 then
        (((m : ℂ) ^ 3 - m) / 12 * (V.centralCharge + W.centralCharge)) •
          (1 : End ℂ (A ⊗[ℂ] B)) else 0) := by
  simp only [nearTensorField_conformal_mode, nearTensorOperator_commutator, nearVirasoroMode,
    V.virasoro, W.virasoro]
  apply TensorProduct.ext'
  intro x y
  by_cases hmn : m + n = 0
  · simp only [hmn, if_pos, tensorTranslation, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, mul_add, add_smul, smul_add]
    abel
  · simp only [hmn, if_false, add_zero, tensorTranslation, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

/-- Translation is the Leibniz rule for the two factor fields. -/
theorem nearTensorField_translation (V : NearVOA A) (W : NearVOA B) (u : A ⊗[ℂ] B) :
    nearTensorField V W
      (mode (nearTensorField V W (nearTensorConformalVector V W)) 0 u) =
      deriv (nearTensorField V W u) := by
  have he : mode (nearTensorField V W (nearTensorConformalVector V W)) 0 =
      tensorTranslation (mode (V.Y V.conformalVector) 0) (mode (W.Y W.conformalVector) 0) := by
    rw [nearTensorField_conformal]; rfl
  rw [he]
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
  | tmul a b =>
      rw [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add]
      simp only [nearTensorField_tmul]
      rw [Reconstruction.deriv_nprod]
      congr 1
      · apply nearNormalProduct_congr
        · rw [V.translation, deriv_firstField]
        · rfl
      · apply nearNormalProduct_congr
        · rfl
        · rw [W.translation, deriv_secondField]

end VOA.Moonshine.ConwayNorton
