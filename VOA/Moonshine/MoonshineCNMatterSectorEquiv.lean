import VOA.Moonshine.MoonshineCNSectorFrame
import VOA.Moonshine.MoonshineCNMonsterLie
import VOA.Moonshine.MoonshineCNVnatSectorAction

/-! An explicit equivariant identification of the polynomial tensor sector with actual matter momentum.
This file asserts a linear equivalence; Virasoro intertwining is not asserted here. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster IntegralLattice HeisenbergN LatGen
open scoped TensorProduct

def moonshineMatterSectorMap (α : lorentzianLattice.carrier) :
    (Vnat ⊗[ℂ] hypFock) →ₗ[ℂ] moonshineMatterSpace :=
  LinearMap.lTensor Vnat ((mkEα lorentzianLattice α).comp
    hypLorentzianPolynomialEquiv.toLinearMap)

def moonshineMatterSectorInverse (α : lorentzianLattice.carrier) :
    moonshineMatterSpace →ₗ[ℂ] (Vnat ⊗[ℂ] hypFock) :=
  LinearMap.lTensor Vnat (hypLorentzianPolynomialEquiv.symm.toLinearMap.comp
    (coordEα lorentzianLattice α))

theorem moonshineMatterSectorMap_tmul (α : lorentzianLattice.carrier) (v : Vnat) (p : hypFock) :
    moonshineMatterSectorMap α (v ⊗ₜ p) =
      v ⊗ₜ latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv p) α := rfl

theorem moonshineMatterSectorInverse_tmul (α : lorentzianLattice.carrier)
    (v : Vnat) (p : FockN (rank lorentzianLattice)) :
    moonshineMatterSectorInverse α (v ⊗ₜ latStateGen lorentzianLattice p α) =
      v ⊗ₜ hypLorentzianPolynomialEquiv.symm p := by
  change v ⊗ₜ hypLorentzianPolynomialEquiv.symm
    (coordEα lorentzianLattice α (latStateGen lorentzianLattice p α)) = _
  rw [latStateGen, coordEα_apply, if_pos rfl]

theorem moonshineMatterSectorMap_mem (α : lorentzianLattice.carrier)
    (u : Vnat ⊗[ℂ] hypFock) : moonshineMatterSectorMap α u ∈ moonshineMatterMomentum α := by
  induction u using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero]; exact Submodule.zero_mem _
  | add u v hu hv => rw [LinearMap.map_add]; exact Submodule.add_mem _ hu hv
  | tmul v p =>
    exact moonshineMatterMomentum_tmul α v
      (latState_mem_momentum lorentzianLattice (hypLorentzianPolynomialEquiv p) α)

theorem moonshineMatterSector_leftInverse (α : lorentzianLattice.carrier)
    (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorInverse α (moonshineMatterSectorMap α u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | add u v hu hv => simp only [LinearMap.map_add, hu, hv]
  | tmul v p =>
    rw [moonshineMatterSectorMap_tmul, moonshineMatterSectorInverse_tmul,
      AlgEquiv.symm_apply_apply]

theorem moonshineMatterSector_rightInverse (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α) :
    moonshineMatterSectorMap α (moonshineMatterSectorInverse α u) = u := by
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => moonshineMatterSectorMap α (moonshineMatterSectorInverse α u) = u)
    ?_ ?_ ?_ ?_ hu
  · change moonshineMatterSectorMap α (moonshineMatterSectorInverse α 0) = 0
    simp only [LinearMap.map_zero]
  · intro u v hu hv
    simp only [LinearMap.map_add, hu, hv]
  · intro c u hu
    simp only [LinearMap.map_smul, hu]
  · intro v _ b hb
    rw [latticeMomentumGrading_eq_range] at hb
    obtain ⟨p, rfl⟩ := hb
    change moonshineMatterSectorMap α
      (moonshineMatterSectorInverse α (v ⊗ₜ latStateGen lorentzianLattice p α)) = _
    rw [moonshineMatterSectorInverse_tmul, moonshineMatterSectorMap_tmul,
      AlgEquiv.apply_symm_apply]
    rfl

/-- The actual momentum-sector equivalence, including the complex-frame change of variables. -/
def moonshineMatterSectorEquiv (α : lorentzianLattice.carrier) :
    (Vnat ⊗[ℂ] hypFock) ≃ₗ[ℂ] moonshineMatterMomentum α :=
  { (moonshineMatterSectorMap α).codRestrict (moonshineMatterMomentum α)
      (moonshineMatterSectorMap_mem α) with
    invFun := fun u => moonshineMatterSectorInverse α u
    left_inv := moonshineMatterSector_leftInverse α
    right_inv := fun u => Subtype.ext (moonshineMatterSector_rightInverse α u u.property) }

theorem moonshineMatterSectorEquiv_tmul (α : lorentzianLattice.carrier) (v : Vnat) (p : hypFock) :
    (moonshineMatterSectorEquiv α (v ⊗ₜ p) : moonshineMatterSpace) =
      v ⊗ₜ latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv p) α := rfl

theorem moonshineMatterSectorEquiv_equivariant (g : AutVnat) (α : lorentzianLattice.carrier)
    (u : Vnat ⊗[ℂ] hypFock) :
    (moonshineMatterSectorEquiv α (vnatSectorAction g u) : moonshineMatterSpace) =
      moonshineMatterAut g (moonshineMatterSectorEquiv α u) := by
  change moonshineMatterSectorMap α (vnatSectorAction g u) =
    moonshineMatterAut g (moonshineMatterSectorMap α u)
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add u v hu hv => simp only [LinearEquiv.map_add, LinearMap.map_add, hu, hv]
  | tmul v p => rfl

end VOA.Moonshine.ConwayNorton
