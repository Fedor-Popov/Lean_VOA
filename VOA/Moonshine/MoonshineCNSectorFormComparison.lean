import VOA.Moonshine.MoonshineCNSectorOscillators
import VOA.Moonshine.MoonshineCNMomentumReversal

/-! The full oscillator and tensor form comparison, with the charge sign retained. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen Nondeg MvPolynomial AutMonster
open scoped TensorProduct

theorem sigmaN_frameOscillator {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (α : L.carrier) (n : ℤ) (p : FockN (rank L)) :
    sigmaN (rank L) (frameOscillator F α n p) =
      -frameOscillator F α n (sigmaN (rank L) p) := by
  simp only [frameOscillator_apply_sum, map_sum, map_smul, sigmaN_oscN,
    smul_neg, Finset.sum_neg_distrib]

/-- Reversal changes the negative-sign orthonormal form to the hyperbolic sector form. -/
theorem hypLorentzianPolynomial_form (p q : hypFock) :
    uForm (rank lorentzianLattice)
      (sigmaN (rank lorentzianLattice) (hypLorentzianPolynomialEquiv p))
      (hypLorentzianPolynomialEquiv q) = hypForm p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    rw [C_eq_smul_one, map_smul, map_one, map_smul, sigmaN_one,
      LinearMap.map_smul₂, LinearMap.map_smul₂, uForm_one, hypForm_one]
    exact congrArg (fun z : ℂ => c • z) (hypLorentzianPolynomial_constantCoeff q)
  | add p r hp hr =>
    simp only [map_add, LinearMap.add_apply, hp, hr]
  | mul_X p v hp =>
    rw [mul_comm p (X v)]
    have hc := hypLorentzianPolynomial_creation v.2 0 v.1 p
    rw [hypOscillator_negative_apply] at hc
    rw [hc, sigmaN_frameOscillator, map_neg, LinearMap.neg_apply,
      uForm_frameOscillator_adjoint, neg_neg, neg_neg,
      ← hypLorentzianPolynomial_oscillator, hp]
    exact (hypForm_oscillator_adjoint v.2 0 (-(v.1 + 1 : ℤ)) p q).symm.trans
      (by rw [hypOscillator_negative_apply])

/-- Full tensor comparison at every momentum, including zero. -/
theorem moonshineMatterSector_form (α : lorentzianLattice.carrier)
    (u v : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterForm
      (moonshineMatterReversal (moonshineMatterSectorEquiv α u))
      (moonshineMatterSectorEquiv α v) =
      chSign lorentzianLattice α * vnatHypForm u v := by
  change moonshineMatterForm
    (moonshineMatterReversal (moonshineMatterSectorMap α u))
    (moonshineMatterSectorMap α v) = _
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero,
      LinearMap.zero_apply, mul_zero]
  | add u w hu hw =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, LinearMap.add_apply, hu, hw, mul_add]
  | tmul a p =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, mul_zero]
    | add v w hv hw => simp only [LinearMap.map_add, hv, hw, mul_add]
    | tmul b q =>
      change moonshineMatterForm
        (moonshineMatterReversal (moonshineMatterSectorEquiv α (a ⊗ₜ p)))
        (moonshineMatterSectorEquiv α (b ⊗ₜ q)) = _
      rw [moonshineMatterReversal_sector_pairing, hypLorentzianPolynomial_form]
      change _ = chSign lorentzianLattice α * (hypForm p q * SimpleNat.natForm a b)
      ring

/-- The reversed pairing has no radical on the full actual momentum sector. -/
theorem moonshineMatterSector_form_nondegenerate (α : lorentzianLattice.carrier)
    (u : moonshineMatterMomentum α)
    (hu : ∀ v : moonshineMatterMomentum α,
      moonshineMatterForm (moonshineMatterReversal u) v = 0) : u = 0 := by
  obtain ⟨p, rfl⟩ := (moonshineMatterSectorEquiv α).surjective u
  suffices hp : p = 0 by rw [hp, LinearEquiv.map_zero]
  by_contra hp
  obtain ⟨q, hq⟩ := vnatHypForm_nondegenerate p hp
  have hz := hu (moonshineMatterSectorEquiv α q)
  rw [moonshineMatterSector_form] at hz
  exact mul_ne_zero (chSign_ne_zero lorentzianLattice α) hq hz

end VOA.Moonshine.ConwayNorton
