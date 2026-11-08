import VOA.Moonshine.MoonshineCNHyperbolicFock
import VOA.Moonshine.MoonshineCNConformalBasis
import VOA.Moonshine.MoonshineCNTensorMomentum
import Mathlib.Algebra.MvPolynomial.Monad

/-! The complex frame map, with family zero assigned to the lattice vector `(0,1)`.
Thus the sector charges `(κ,ell) = (x,y)` match momentum `(x,y)`.
Intertwining the nonzero oscillators and Virasoro modes is a separate obligation. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen MvPolynomial
open scoped TensorProduct BigOperators

def hypLorentzianFrameForward : hypFock →ₐ[ℂ] hypFock :=
  bind₁ fun v => if v.2 = 0 then
    (1 / 2 : ℂ) • X (v.1, 0) - (Complex.I / 2) • X (v.1, 1)
    else X (v.1, 0) + Complex.I • X (v.1, 1)

def hypLorentzianFrameBackward : hypFock →ₐ[ℂ] hypFock :=
  bind₁ fun v => if v.2 = 0 then
    X (v.1, 0) + (1 / 2 : ℂ) • X (v.1, 1)
    else Complex.I • X (v.1, 0) - (Complex.I / 2) • X (v.1, 1)

theorem hypLorentzianFrame_forward_backward :
    hypLorentzianFrameForward.comp hypLorentzianFrameBackward = AlgHom.id ℂ hypFock := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, a⟩
  fin_cases a <;>
    simp [hypLorentzianFrameForward, hypLorentzianFrameBackward,
      smul_add, smul_sub, smul_smul] <;>
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

theorem hypLorentzianFrame_backward_forward :
    hypLorentzianFrameBackward.comp hypLorentzianFrameForward = AlgHom.id ℂ hypFock := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, a⟩
  fin_cases a <;>
    simp [hypLorentzianFrameForward, hypLorentzianFrameBackward,
      smul_add, smul_sub, smul_smul] <;>
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

def hypLorentzianFrameEquiv : hypFock ≃ₐ[ℂ] hypFock :=
  AlgEquiv.ofAlgHom hypLorentzianFrameForward hypLorentzianFrameBackward
    hypLorentzianFrame_forward_backward hypLorentzianFrame_backward_forward

/-- The hyperbolic variables in the actual complex orthonormal Fock coordinates. -/
def hypLorentzianPolynomialEquiv : hypFock ≃ₐ[ℂ] FockN (rank lorentzianLattice) :=
  hypLorentzianFrameEquiv.trans (renameEquiv ℂ
    (Equiv.prodCongr (Equiv.refl ℕ) (finCongr lorentzian_rank).symm))

theorem hypLorentzianPolynomial_X_zero (j : ℕ) :
    hypLorentzianPolynomialEquiv (X (j, 0)) =
      (1 / 2 : ℂ) • X (j, (finCongr lorentzian_rank).symm 0) -
        (Complex.I / 2) • X (j, (finCongr lorentzian_rank).symm 1) := by
  simp [hypLorentzianPolynomialEquiv, hypLorentzianFrameEquiv, hypLorentzianFrameForward]

theorem hypLorentzianPolynomial_X_one (j : ℕ) :
    hypLorentzianPolynomialEquiv (X (j, 1)) =
      X (j, (finCongr lorentzian_rank).symm 0) +
        Complex.I • X (j, (finCongr lorentzian_rank).symm 1) := by
  simp [hypLorentzianPolynomialEquiv, hypLorentzianFrameEquiv, hypLorentzianFrameForward]

/-- Inserting a fixed charge is an equivalence onto precisely that momentum sector. -/
def lorentzianSectorFockEquiv (α : lorentzianLattice.carrier) :
    FockN (rank lorentzianLattice) ≃ₗ[ℂ] latticeMomentumGrading lorentzianLattice α :=
  LinearEquiv.ofBijective
    ((mkEα lorentzianLattice α).codRestrict (latticeMomentumGrading lorentzianLattice α)
      (fun p => latState_mem_momentum lorentzianLattice p α))
    ⟨fun p q h => mkEα_injective lorentzianLattice α (congrArg Subtype.val h),
      fun v => by
        have hv := v.property
        simp only [latticeMomentumGrading_eq_range] at hv
        obtain ⟨p, hp⟩ := hv
        exact ⟨p, Subtype.ext hp⟩⟩

def hypLorentzianSectorEquiv (α : lorentzianLattice.carrier) :
    hypFock ≃ₗ[ℂ] latticeMomentumGrading lorentzianLattice α :=
  hypLorentzianPolynomialEquiv.toLinearEquiv.trans (lorentzianSectorFockEquiv α)

theorem hypLorentzianSectorEquiv_apply (α : lorentzianLattice.carrier) (p : hypFock) :
    (hypLorentzianSectorEquiv α p : LorentzianFockSpace) =
      latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv p) α := rfl

/-- The zero mode pairs the current's lattice vector with the sector momentum. -/
theorem lorentzianHeisenberg_zeroMode (h α : lorentzianLattice.carrier)
    (p : FockN (rank lorentzianLattice)) :
    mode (lorentzianHeisenbergField h) 0 (latStateGen lorentzianLattice p α) =
      (lorentzianLattice.form h α : ℂ) • latStateGen lorentzianLattice p α := by
  change (∑ a, frameCoordinate lorentzianComplexFrame h a •
    frameCurrent lorentzianComplexFrame a) (-1) (latStateGen lorentzianLattice p α) = _
  rw [show ((∑ a, frameCoordinate lorentzianComplexFrame h a •
      frameCurrent lorentzianComplexFrame a) (-1) : Module.End ℂ LorentzianFockSpace) =
      ∑ a, frameCoordinate lorentzianComplexFrame h a • frameCurrent lorentzianComplexFrame a (-1)
    from Finset.sum_apply (s := Finset.univ)
      (g := fun a => frameCoordinate lorentzianComplexFrame h a •
        frameCurrent lorentzianComplexFrame a) (-1)]
  simp only [LinearMap.coe_sum, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    frameCurrent_tmul, currentN_apply]
  simp only [show -(-1 : ℤ) - 1 = 0 by norm_num, oscN_zero, LinearMap.zero_apply,
    latStateGen, TensorProduct.zero_tmul, if_pos rfl, ite_true,
    zero_add, smul_smul, ← Finset.sum_smul]
  congr 1
  exact lorentzianComplexFrame.pairing h α

theorem hypLorentzianSector_zeroCharges (x y : ℤ) (p : hypFock) :
    mode (lorentzianHeisenbergField ![0, 1]) 0 (hypLorentzianSectorEquiv ![x, y] p) =
        (x : ℂ) • (hypLorentzianSectorEquiv ![x, y] p : LorentzianFockSpace) ∧
      mode (lorentzianHeisenbergField ![1, 0]) 0 (hypLorentzianSectorEquiv ![x, y] p) =
        (y : ℂ) • (hypLorentzianSectorEquiv ![x, y] p : LorentzianFockSpace) := by
  rw [hypLorentzianSectorEquiv_apply, lorentzianHeisenberg_zeroMode,
    lorentzianHeisenberg_zeroMode]
  simp [lorentzian_form_apply]

end VOA.Moonshine.ConwayNorton
