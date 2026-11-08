import VOA.Moonshine.MoonshineCNRealization

/-!
# The conformal vector in the isotropic lattice basis

For `u=(1,0)` and `v=(0,1)`, the dual basis is `(v,u)`. The Sugawara
vector is exactly `(u(-1)v(-1) + v(-1)u(-1))1/2`.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open IntegralLattice HeisenbergN LatGen MvPolynomial

/-- Negative-one Heisenberg action, lifted to the full lattice carrier. -/
noncomputable def lorentzianCreation (α : lorentzianLattice.carrier) :
    Module.End ℂ LorentzianFockSpace :=
  LinearMap.rTensor (lorentzianLattice.carrier →₀ ℂ)
    (frameOscillator lorentzianComplexFrame α (-1))

/-- The Heisenberg current, including its momentum zero mode. -/
noncomputable def lorentzianHeisenbergField (α : lorentzianLattice.carrier) :
    FormalDist (Module.End ℂ LorentzianFockSpace) :=
  ∑ a, frameCoordinate lorentzianComplexFrame α a • frameCurrent lorentzianComplexFrame a

theorem lorentzianCreation_eq_current_mode (α : lorentzianLattice.carrier) :
    mode (lorentzianHeisenbergField α) (-1) = lorentzianCreation α := by
  change ((∑ a, frameCoordinate lorentzianComplexFrame α a •
    frameCurrent lorentzianComplexFrame a) 0 : Module.End ℂ LorentzianFockSpace) = _
  rw [show ((∑ a, frameCoordinate lorentzianComplexFrame α a •
      frameCurrent lorentzianComplexFrame a) 0 : Module.End ℂ LorentzianFockSpace) =
      ∑ a, frameCoordinate lorentzianComplexFrame α a • frameCurrent lorentzianComplexFrame a 0 from
    Finset.sum_apply (s := Finset.univ)
      (g := fun a => frameCoordinate lorentzianComplexFrame α a •
        frameCurrent lorentzianComplexFrame a) 0]
  simp [lorentzianCreation, frameCurrent,
    frameOscillator, frameCoordinate, currentN_apply, ← LinearMap.coe_rTensorHom,
    Finset.sum_apply, Pi.smul_apply]

theorem lorentzianIsotropicBasis_pairing :
    lorentzianLattice.form ![1, 0] ![1, 0] = 0 ∧
    lorentzianLattice.form ![0, 1] ![0, 1] = 0 ∧
    lorentzianLattice.form ![1, 0] ![0, 1] = 1 ∧
    lorentzianLattice.form ![0, 1] ![1, 0] = 1 := by
  norm_num [lorentzian_form_apply]

/-- The explicit complex-frame creation variable in the two polynomial directions. -/
theorem lorentzianCreationVariable_coordinates (α : lorentzianLattice.carrier) :
    creationVariable lorentzianComplexFrame α 0 =
      ((α 0 : ℂ) + (α 1 : ℂ) / 2) •
        (X (0, (finCongr lorentzian_rank).symm 0) : FockN (rank lorentzianLattice)) +
      (Complex.I * ((α 0 : ℂ) - (α 1 : ℂ) / 2)) •
        X (0, (finCongr lorentzian_rank).symm 1) := by
  change (∑ a, complexHyperbolicCoordinate α (finCongr lorentzian_rank a) •
    (X (0, a) : FockN (rank lorentzianLattice))) = _
  rw [← Equiv.sum_comp (finCongr lorentzian_rank).symm
    (fun a => complexHyperbolicCoordinate α (finCongr lorentzian_rank a) •
      (X (0, a) : FockN (rank lorentzianLattice)))]
  simp [Fin.sum_univ_two, complexHyperbolicCoordinate]

/-- The prescribed dual-basis formula for the actual reconstructed conformal vector. -/
theorem lorentzianNearVOA_conformal_dualBasis :
    lorentzianNearVOA.conformalVector = (1 / 2 : ℂ) •
      (lorentzianCreation ![1, 0] (lorentzianCreation ![0, 1] lorentzianVacuum) +
       lorentzianCreation ![0, 1] (lorentzianCreation ![1, 0] lorentzianVacuum)) := by
  change mkEα lorentzianLattice 0 (ωN (rank lorentzianLattice) 1) = _
  simp only [lorentzianCreation, lorentzianVacuum, latVacuumGen, latStateGen,
    mkEα_apply, LinearMap.rTensor_tmul, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  congr 1
  have hcreation (α : lorentzianLattice.carrier) :
      frameOscillator lorentzianComplexFrame α (-1) =
        LinearMap.mulLeft ℂ (creationVariable lorentzianComplexFrame α 0) := by
    exact frameOscillator_neg_eq_mulLeft_creationVariable lorentzianComplexFrame α 0
  simp only [hcreation, LinearMap.mulLeft_apply, vacuumN, mul_one,
    lorentzianCreationVariable_coordinates]
  rw [ωN, ← Equiv.sum_comp (finCongr lorentzian_rank).symm
    (fun a => ωNa (rank lorentzianLattice) 1 a), Fin.sum_univ_two]
  simp only [ωNa, oscN_neg_one_sq_vacuumN, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_sub, map_div₀, map_one]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one,
    neg_mul, neg_neg]
  have hc : (MvPolynomial.C ((1 / 2 : ℂ) ^ 2) : FockN (rank lorentzianLattice)) * 2 =
      MvPolynomial.C (1 / 2 : ℂ) := by
    calc
      MvPolynomial.C ((1 / 2 : ℂ) ^ 2) * 2 = MvPolynomial.C ((1 / 2 : ℂ) ^ 2 * 2) := by
        rw [map_mul]
        rw [show (MvPolynomial.C (2 : ℂ) : FockN (rank lorentzianLattice)) = 2 from
          map_ofNat MvPolynomial.C 2]
      _ = MvPolynomial.C (1 / 2 : ℂ) := congrArg MvPolynomial.C (by norm_num)
  rw [← hc]
  ring

end VOA.Moonshine.ConwayNorton
