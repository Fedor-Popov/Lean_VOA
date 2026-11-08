import VOA.Moonshine.MoonshineCNMatterSectorEquiv
import VOA.Moonshine.MoonshineCNTensorForm

/-! Momentum reversal, oscillator signs, and the exact cross-momentum form normalization.
The displayed pairing remains in the orthonormal polynomial coordinates. Its identification
with `hypForm` is a further theorem, not an assumption of this construction. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen Nondeg AutMonster SimpleNat
open scoped TensorProduct BigOperators

theorem sigmaN_sugawaraTerm (r : ℕ) (a : Fin r) (n j : ℤ) (p : FockN r) :
    sigmaN r (sugTermN r 1 a n j p) = sugTermN r 1 a n j (sigmaN r p) := by
  simp only [sugTermN_apply]
  split_ifs <;> rw [sigmaN_oscN, sigmaN_oscN, LinearMap.map_neg, neg_neg]

theorem sigmaN_virasoro (r : ℕ) (n : ℤ) (p : FockN r) :
    sigmaN r (LvirN r 1 n p) = LvirN r 1 n (sigmaN r p) := by
  have h (a : Fin r) : sigmaN r (LvirNa r 1 a n p) = LvirNa r 1 a n (sigmaN r p) := by
    rw [LvirNa_apply', LvirNa_apply', LinearEquiv.map_smul]
    congr 1
    have hf := (sigmaN r).toLinearMap.toAddMonoidHom.map_finsum
      (sugTermN_support_finite r 1 a n p)
    change sigmaN r (∑ᶠ j, sugTermN r 1 a n j p) = _ at hf
    rw [hf]
    exact finsum_congr fun j => sigmaN_sugawaraTerm r a n j p
  simp only [LvirN, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => h a

theorem lorentzianReversal_frameOscillator (α : lorentzianLattice.carrier)
    (n : ℤ) (p : FockN (rank lorentzianLattice)) :
    sigmaN (rank lorentzianLattice) (frameOscillator lorentzianComplexFrame α n p) =
      frameOscillator lorentzianComplexFrame (-α) n (sigmaN (rank lorentzianLattice) p) := by
  simp only [frameOscillator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, LinearEquiv.map_smul, sigmaN_oscN, map_neg, Pi.neg_apply,
    neg_smul, smul_neg, LinearMap.neg_apply]

/-- The existing oscillator-parity and charge-negation involution commutes with all actual L-modes. -/
theorem lorentzianReversal_virasoro (n : ℤ) (u : LorentzianFockSpace) :
    thetaLat lorentzianLattice (lorentzianNearVOA.L n u) =
      lorentzianNearVOA.L n (thetaLat lorentzianLattice u) := by
  have he : lorentzianNearVOA.L n = frameVirasoroMode lorentzianComplexFrame n :=
    mode_frameStateField_omega_eq_frameVirasoroMode lorentzianComplexFrame lorentzian_even n
  rw [he]
  induction u using induction_latState lorentzianLattice with
  | h0 => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | hadd u v hu hv => simp only [LinearMap.map_add, LinearEquiv.map_add, hu, hv]
  | hsmul c u hu => simp only [LinearMap.map_smul, LinearEquiv.map_smul, hu]
  | hst p α =>
    rw [frameVirasoroMode_tmul, LinearEquiv.map_add, LinearEquiv.map_add,
      thetaLat_latStateGen, thetaLat_latStateGen, thetaLat_latStateGen,
      frameVirasoroMode_tmul, sigmaN_virasoro, lorentzianReversal_frameOscillator]
    split_ifs <;> simp only [LinearEquiv.map_smul, LinearEquiv.map_zero,
      thetaLat_latStateGen, map_neg, LinearMap.neg_apply, neg_neg]

def moonshineMatterReversal : moonshineMatterSpace ≃ₗ[ℂ] moonshineMatterSpace :=
  (thetaLat lorentzianLattice).lTensor Vnat

theorem moonshineMatterReversal_tmul (v : Vnat)
    (p : FockN (rank lorentzianLattice)) (α : lorentzianLattice.carrier) :
    moonshineMatterReversal (v ⊗ₜ latStateGen lorentzianLattice p α) =
      v ⊗ₜ latStateGen lorentzianLattice (sigmaN (rank lorentzianLattice) p) (-α) := by
  change v ⊗ₜ thetaLat lorentzianLattice (latStateGen lorentzianLattice p α) = _
  rw [thetaLat_latStateGen]

theorem moonshineMatterReversal_involutive : Function.Involutive moonshineMatterReversal := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add u v hu hv => simp only [LinearEquiv.map_add, hu, hv]
  | tmul v p =>
    change v ⊗ₜ thetaLat lorentzianLattice (thetaLat lorentzianLattice p) = _
    rw [thetaLat_thetaLat]

theorem moonshineMatterReversal_momentum (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α) :
    moonshineMatterReversal u ∈ moonshineMatterMomentum (-α) := by
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => moonshineMatterReversal u ∈ moonshineMatterMomentum (-α)) ?_ ?_ ?_ ?_ hu
  · change moonshineMatterReversal 0 ∈ _
    rw [LinearEquiv.map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    rw [LinearEquiv.map_add]; exact Submodule.add_mem _ hx hy
  · intro c x hx
    rw [LinearEquiv.map_smul]; exact Submodule.smul_mem _ c hx
  · intro v _ p hp
    rw [latticeMomentumGrading_eq_range] at hp
    obtain ⟨q, rfl⟩ := hp
    change moonshineMatterReversal (v ⊗ₜ latStateGen lorentzianLattice q α) ∈ _
    rw [moonshineMatterReversal_tmul]
    exact moonshineMatterMomentum_tmul _ _ (latState_mem_momentum _ _ _)

theorem moonshineMatterReversal_virasoro (n : ℤ) (u : moonshineMatterSpace) :
    moonshineMatterReversal (moonshineMatterNearVOA.L n u) =
      moonshineMatterNearVOA.L n (moonshineMatterReversal u) := by
  have he : moonshineMatterNearVOA.L n =
      TensorFieldLift.tensorTranslation (nearVirasoroMode VnatVOA.toNearVOA n)
        (nearVirasoroMode lorentzianNearVOA n) :=
    nearTensorField_conformal_mode _ _ n
  rw [he]
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add u v hu hv => simp only [LinearEquiv.map_add, LinearMap.map_add, hu, hv]
  | tmul v p =>
    simp only [TensorFieldLift.tensorTranslation, LinearMap.add_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearEquiv.map_add]
    change _ ⊗ₜ thetaLat lorentzianLattice p +
      v ⊗ₜ thetaLat lorentzianLattice (lorentzianNearVOA.L n p) =
      _ ⊗ₜ thetaLat lorentzianLattice p +
        v ⊗ₜ lorentzianNearVOA.L n (thetaLat lorentzianLattice p)
    rw [lorentzianReversal_virasoro]
    rfl

/-- Exact cross-momentum normalization for arbitrary oscillator polynomials. -/
theorem lorentzianReversal_form (α : lorentzianLattice.carrier)
    (p q : FockN (rank lorentzianLattice)) :
    lorentzianBilinearForm (thetaLat lorentzianLattice (latStateGen lorentzianLattice p α))
      (latStateGen lorentzianLattice q α) =
      chSign lorentzianLattice α * uForm (rank lorentzianLattice)
        (sigmaN (rank lorentzianLattice) p) q := by
  change latForm lorentzianLattice _ _ = _
  rw [thetaLat_latStateGen, latForm_state, neg_add_cancel, if_pos rfl, chSign_neg]

/-- The tensor-sector pairing after momentum reversal, before identifying its polynomial part. -/
theorem moonshineMatterReversal_sector_pairing (α : lorentzianLattice.carrier)
    (a b : Vnat) (p q : hypFock) :
    moonshineMatterForm
      (moonshineMatterReversal (moonshineMatterSectorEquiv α (a ⊗ₜ p)))
      (moonshineMatterSectorEquiv α (b ⊗ₜ q)) =
      chSign lorentzianLattice α *
        uForm (rank lorentzianLattice)
          (sigmaN (rank lorentzianLattice) (hypLorentzianPolynomialEquiv p))
          (hypLorentzianPolynomialEquiv q) * natForm a b := by
  rw [moonshineMatterSectorEquiv_tmul, moonshineMatterSectorEquiv_tmul]
  change lorentzianBilinearForm
    (thetaLat lorentzianLattice (latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv p) α))
    (latStateGen lorentzianLattice (hypLorentzianPolynomialEquiv q) α) * natForm a b = _
  rw [lorentzianReversal_form]

end VOA.Moonshine.ConwayNorton
