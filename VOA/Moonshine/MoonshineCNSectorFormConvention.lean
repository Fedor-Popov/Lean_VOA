import VOA.Moonshine.MoonshineCNTensorForm
import VOA.Moonshine.MoonshineCNTensorMomentum
import VOA.Moonshine.MoonshineCNVnatSectorOperators

/-! The exact momentum convention of the existing matter form.
A nonzero sector is isotropic for this opposite-momentum pairing. Consequently,
a comparison with the sector contravariant form requires momentum reversal. -/

namespace VOA.Moonshine.ConwayNorton
open scoped TensorProduct
open IntegralLattice LatGen HeisenbergN Nondeg AutMonster SimpleNat

/-- The existing lattice form is zero unless its two charges are opposite. -/
theorem lorentzianForm_momentum_orthogonal (α β : lorentzianLattice.carrier)
    (hαβ : α + β ≠ 0) (p q : LorentzianFockSpace)
    (hp : p ∈ latticeMomentumGrading lorentzianLattice α)
    (hq : q ∈ latticeMomentumGrading lorentzianLattice β) :
    lorentzianBilinearForm p q = 0 := by
  rw [latticeMomentumGrading_eq_range] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  change latForm lorentzianLattice (latStateGen _ a α) (latStateGen _ b β) = 0
  rw [latForm_state, if_neg hαβ, zero_mul]

/-- Matter tensoring preserves the opposite-momentum support condition. -/
theorem moonshineMatterForm_momentum_orthogonal (α β : lorentzianLattice.carrier)
    (hαβ : α + β ≠ 0) (u v : moonshineMatterSpace)
    (hu : u ∈ moonshineMatterMomentum α) (hv : v ∈ moonshineMatterMomentum β) :
    moonshineMatterForm u v = 0 := by
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => moonshineMatterForm u v = 0) ?_ ?_ ?_ ?_ hu
  · simp only [map_zero, LinearMap.zero_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  · intro c a ha
    simp only [map_smul, LinearMap.smul_apply, ha, smul_zero]
  · intro a _ p hp
    refine TensorVA.tenSub_induction (P := ⊤)
      (Q := latticeMomentumGrading lorentzianLattice β)
      (motive := fun v => moonshineMatterForm (a ⊗ₜ[ℂ] p) v = 0) ?_ ?_ ?_ ?_ hv
    · exact map_zero _
    · intro b c hb hc
      simp only [map_add, hb, hc, add_zero]
    · intro c b hb
      simp only [map_smul, hb, smul_zero]
    · intro b _ q hq
      change lorentzianBilinearForm p q * natForm a b = 0
      rw [lorentzianForm_momentum_orthogonal α β hαβ p q hp hq, zero_mul]

/-- Every nonzero momentum sector is totally isotropic for the existing matter form. -/
theorem moonshineMatterForm_same_momentum_zero (α : lorentzianLattice.carrier)
    (hα : α ≠ 0) (u v : moonshineMatterSpace)
    (hu : u ∈ moonshineMatterMomentum α) (hv : v ∈ moonshineMatterMomentum α) :
    moonshineMatterForm u v = 0 := by
  apply moonshineMatterForm_momentum_orthogonal α α _ u v hu hv
  intro h
  apply hα
  funext i
  have hi := congrFun h i
  change α i + α i = 0 at hi
  change α i = 0
  omega

/-- Exact charge normalization, including the library's cocycle sign. -/
theorem moonshineMatterForm_opposite_ground (α : lorentzianLattice.carrier)
    (a b : Vnat) :
    moonshineMatterForm (a ⊗ₜ[ℂ] latStateGen lorentzianLattice 1 α)
      (b ⊗ₜ[ℂ] latStateGen lorentzianLattice 1 (-α)) =
        chSign lorentzianLattice α * natForm a b := by
  change latForm lorentzianLattice (latStateGen _ 1 α) (latStateGen _ 1 (-α)) *
    natForm a b = _
  rw [latForm_state, add_neg_cancel, if_pos rfl, uForm_one]
  simp only [MvPolynomial.coeff_one, ite_true, mul_one]

/-- No nonzero scalar can turn a same-sector restriction into the sector form.
This rules out the literal same-momentum isometry even without imposing linearity. -/
theorem moonshineMatterSector_no_same_momentum_isometry (α : lorentzianLattice.carrier)
    (hα : α ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (F : (Vnat ⊗[ℂ] hypFock) → moonshineMatterMomentum α) :
    ¬ (∀ u v, moonshineMatterInvariantForm.form (F u) (F v) = c * vnatHypForm u v) := by
  intro h
  let w : Vnat ⊗[ℂ] hypFock := VnatVOA.vacuum ⊗ₜ[ℂ] (1 : hypFock)
  have hw : vnatHypForm w w = 1 := by
    change hypForm 1 1 * natForm VnatVOA.vacuum VnatVOA.vacuum = 1
    have hn : natForm VnatVOA.vacuum VnatVOA.vacuum = 1 :=
      natInvForm_normalized vnat_twistedLocality
    rw [hypForm_one, hn]
    simp
  have he := h w w
  change moonshineMatterForm (F w) (F w) = _ at he
  rw [moonshineMatterForm_same_momentum_zero α hα _ _ (F w).property (F w).property,
    hw, mul_one] at he
  exact hc he.symm

end VOA.Moonshine.ConwayNorton
