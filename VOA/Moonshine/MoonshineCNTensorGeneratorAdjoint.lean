import VOA.Moonshine.MoonshineCNCurrentAdjoint
import VOA.Moonshine.MoonshineCNTensorForm

/-! Adjoint identities for the actual generating fields of the matter tensor product. -/

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open AutMonster SimpleNat IntegralLattice LatGen HeisenbergN Nondeg TensorFieldLift

theorem moonshineMatter_latticeGenerator_mode (b : LorentzianFockSpace) (n : ℤ) :
    mode (moonshineMatterNearVOA.Y (VnatVOA.vacuum ⊗ₜ[ℂ] b)) n =
      LinearMap.lTensor Vnat (mode (lorentzianNearVOA.Y b) n) := by
  change mode (nearTensorField VnatVOA.toNearVOA lorentzianNearVOA
    (VnatVOA.toNearVOA.vacuum ⊗ₜ[ℂ] b)) n = _
  rw [nearTensorField_second_vacuum]
  rfl

theorem moonshineMatter_vnatGenerator_mode (a : Vnat) (n : ℤ) :
    mode (moonshineMatterNearVOA.Y (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum)) n =
      LinearMap.rTensor LorentzianFockSpace (mode (VnatVOA.Y a) n) := by
  change mode (nearTensorField VnatVOA.toNearVOA lorentzianNearVOA
    (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum)) n = _
  rw [nearTensorField_first_vacuum]
  rfl

theorem bilinearTensor_lTensor_adjoint
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (P : LinearMap.BilinForm ℂ A) (Q : LinearMap.BilinForm ℂ B)
    (f g : End ℂ B) (c : ℂ) (h : ∀ b b', Q (f b) b' = c * Q b (g b'))
    (x y : A ⊗[ℂ] B) :
    (P.tmul Q) (LinearMap.lTensor A f x) y =
      c * (P.tmul Q) x (LinearMap.lTensor A g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
      | tmul a' b' =>
          simp only [LinearMap.lTensor_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
            smul_eq_mul, h]
          ring

/-- Charged generators of the actual tensor state-field map satisfy FHL adjointness. -/
theorem moonshineMatterForm_chargeGenerator_adjoint (γ : lorentzianLattice.carrier)
    (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm
      (mode (moonshineMatterNearVOA.Y
        (VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice γ)) n x) y =
      (-1 : ℂ) ^ LatGen.halfNorm lorentzianLattice γ * moonshineMatterForm x
        (mode (moonshineMatterNearVOA.Y
          (VnatVOA.vacuum ⊗ₜ[ℂ] latChargeGen lorentzianLattice γ))
          (2 * LatGen.halfNorm lorentzianLattice γ - n - 2) y) := by
  rw [moonshineMatter_latticeGenerator_mode, moonshineMatter_latticeGenerator_mode]
  exact bilinearTensor_lTensor_adjoint natForm lorentzianBilinearForm _ _ _
    (latForm_frameStateField_charge_adjoint lorentzianComplexFrame lorentzian_even γ n) x y

/-- The zero-momentum Heisenberg generators remain skew-adjoint after tensoring. -/
theorem moonshineMatterForm_currentGenerator_adjoint (a : Fin (rank lorentzianLattice))
    (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm
      (mode (moonshineMatterNearVOA.Y
        (VnatVOA.vacuum ⊗ₜ[ℂ] frameWordState lorentzianLattice [(0, a)] 0)) n x) y =
      -moonshineMatterForm x
        (mode (moonshineMatterNearVOA.Y
          (VnatVOA.vacuum ⊗ₜ[ℂ] frameWordState lorentzianLattice [(0, a)] 0)) (-n) y) := by
  rw [moonshineMatter_latticeGenerator_mode, moonshineMatter_latticeGenerator_mode]
  simpa only [neg_one_mul] using
    bilinearTensor_lTensor_adjoint natForm lorentzianBilinearForm _ _ (-1)
      (fun b b' => by simpa only [neg_one_mul] using
        latForm_frameStateField_current_adjoint lorentzianComplexFrame lorentzian_even a n b b') x y

/-- Full FHL identity on the Vnat factor embedded as tensor generators. -/
theorem moonshineMatterForm_vnatGenerator_fhl (wt : ℤ) (a : Vnat)
    (ha : a ∈ VnatVOA.grading wt) (n : ℤ) (x y : moonshineMatterSpace) :
    moonshineMatterForm
      (mode (moonshineMatterNearVOA.Y (a ⊗ₜ[ℂ] lorentzianNearVOA.vacuum)) n x) y =
      (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
        moonshineMatterForm x
          (mode (moonshineMatterNearVOA.Y
            (((VnatVOA.L 1 ^ j) a) ⊗ₜ[ℂ] lorentzianNearVOA.vacuum))
            (2 * wt - n - 2 - (j : ℤ)) y) := by
  simp only [moonshineMatter_vnatGenerator_mode]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx', mul_add, Finset.sum_add_distrib]
  | tmul v p =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
          simp only [map_add, hy, hy', mul_add, Finset.sum_add_distrib]
      | tmul w q =>
          simp only [moonshineMatterForm, LinearMap.rTensor_tmul,
            LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
          have h := natForm_fhl vnat_twistedLocality wt a ha n v w
          change natForm (mode (VnatVOA.Y a) n v) w =
            (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
              natForm v (mode (VnatVOA.Y ((VnatVOA.L 1 ^ j) a))
                (2 * wt - n - 2 - (j : ℤ)) w) at h
          rw [h]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

end VOA.Moonshine.ConwayNorton
