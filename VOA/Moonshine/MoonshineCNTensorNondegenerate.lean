import VOA.Moonshine.MoonshineCNTensorForm

/-! Nondegeneracy of the actual matter form, using explicit lattice coefficients. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct Classical
open IntegralLattice LatGen HeisenbergN Nondeg SimpleNat AutMonster

abbrev LorentzianOscillatorMonomial := (ℕ × Fin (rank lorentzianLattice)) →₀ ℕ

noncomputable def lorentzianStateBasis :
    Module.Basis (LorentzianOscillatorMonomial × lorentzianLattice.carrier) ℂ LorentzianFockSpace :=
  (MvPolynomial.basisMonomials (ℕ × Fin (rank lorentzianLattice)) ℂ).tensorProduct
    Finsupp.basisSingleOne

theorem lorentzianStateBasis_apply (d : LorentzianOscillatorMonomial)
    (α : lorentzianLattice.carrier) :
    lorentzianStateBasis (d, α) = latStateGen lorentzianLattice (MvPolynomial.monomial d 1) α := by
  simp [lorentzianStateBasis, Module.Basis.tensorProduct_apply, latStateGen, eGen]

/-- A basis vector at opposite charge isolates exactly one polynomial/charge coefficient. -/
theorem lorentzianStateBasis_pair (d : LorentzianOscillatorMonomial)
    (α : lorentzianLattice.carrier) (x : LorentzianFockSpace) :
    lorentzianBilinearForm x (lorentzianStateBasis (d, -α)) =
      (uWt d * chSign lorentzianLattice α) * lorentzianStateBasis.repr x (d, α) := by
  rw [lorentzianStateBasis_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | tmul p g =>
      change latForm lorentzianLattice (p ⊗ₜ g)
        (MvPolynomial.monomial d 1 ⊗ₜ eGen lorentzianLattice (-α)) = _
      rw [latForm_monomial_right, InvForm.tcoeff_tmul, chForm_symm]
      simp only [eGen, chForm_single, neg_neg, chSign_neg, one_mul,
        Finsupp.smul_apply, smul_eq_mul, lorentzianStateBasis,
        Module.Basis.tensorProduct_repr_tmul_apply]
      change uWt d * (chSign lorentzianLattice α * (MvPolynomial.coeff d p * g α)) =
        (uWt d * chSign lorentzianLattice α) * (g α * MvPolynomial.coeff d p)
      ring

/-- The `V♮` coefficient at a fixed lattice basis vector. -/
noncomputable def moonshineMatterCoefficient
    (i : LorentzianOscillatorMonomial × lorentzianLattice.carrier) (x : moonshineMatterSpace) : Vnat :=
  TensorProduct.equivFinsuppOfBasisRight lorentzianStateBasis x i

theorem moonshineMatterForm_coefficient (d : LorentzianOscillatorMonomial)
    (α : lorentzianLattice.carrier) (x : moonshineMatterSpace) (a : Vnat) :
    moonshineMatterForm x (a ⊗ₜ lorentzianStateBasis (d, -α)) =
      (uWt d * chSign lorentzianLattice α) * natForm (moonshineMatterCoefficient (d, α) x) a := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp only [moonshineMatterCoefficient, LinearEquiv.map_zero, Finsupp.zero_apply,
        LinearMap.map_zero, LinearMap.zero_apply, mul_zero]
  | add x y hx hy =>
      simp only [LinearMap.map_add, LinearMap.add_apply, hx, hy, moonshineMatterCoefficient,
        LinearEquiv.map_add, Finsupp.add_apply, mul_add]
  | tmul b v =>
      change lorentzianBilinearForm v (lorentzianStateBasis (d, -α)) * natForm b a = _
      rw [lorentzianStateBasis_pair]
      simp only [moonshineMatterCoefficient, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

theorem moonshineForm_nondegenerate (x : Vnat) (hx : x ≠ 0) : ∃ y, natForm x y ≠ 0 := by
  by_contra! h
  have hm : x ∈ VertexOperatorAlgebra.InvariantForm.leftRadical
      (natInvForm vnat_twistedLocality) := by
    rw [VertexOperatorAlgebra.InvariantForm.mem_leftRadical]
    exact LinearMap.ext h
  rw [natInvForm_leftRadical, Submodule.mem_bot] at hm
  exact hx hm

/-- Every nonzero matter state pairs nontrivially with a genuine matter state. -/
theorem moonshineMatterForm_nondegenerate (x : moonshineMatterSpace) (hx : x ≠ 0) :
    ∃ y, moonshineMatterForm x y ≠ 0 := by
  obtain ⟨⟨d, α⟩, hi⟩ : ∃ i, moonshineMatterCoefficient i x ≠ 0 := by
    by_contra! h
    apply hx
    apply (TensorProduct.equivFinsuppOfBasisRight lorentzianStateBasis).injective
    rw [LinearEquiv.map_zero]
    exact Finsupp.ext h
  obtain ⟨a, ha⟩ := moonshineForm_nondegenerate _ hi
  refine ⟨a ⊗ₜ lorentzianStateBasis (d, -α), ?_⟩
  rw [moonshineMatterForm_coefficient]
  exact mul_ne_zero (mul_ne_zero (uWt_ne_zero d) (chSign_ne_zero lorentzianLattice α)) ha

end VOA.Moonshine.ConwayNorton
