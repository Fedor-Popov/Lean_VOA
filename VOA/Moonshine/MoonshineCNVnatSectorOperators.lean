import VOA.Moonshine.MoonshineCNVnatLightCone
import VOA.Moonshine.MoonshineCNHyperbolicModeGrading
import VOA.Moonshine.MoonshineCNTensorNondegenerate

/-! # Actual charge-26 operators and nondegenerate form on V♮ tensor hypFock

This supplies the ungraded sector operations. It does not assert that the
finite graded StringModule or its physical quotient has been constructed.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat MvPolynomial TensorFieldLift
open scoped TensorProduct

def vnatHypMode (κ ell : ℂ) (n : ℤ) : Module.End ℂ (Vnat ⊗[ℂ] hypFock) :=
  tensorTranslation (nearVirasoroMode VnatVOA.toNearVOA n) (hypSugawara κ ell n)

theorem vnatHypMode_negative (κ ell : ℂ) (j : ℕ) :
    vnatHypMode κ ell (-(j + 1 : ℤ)) = vnatHypNegative κ ell j := rfl

/-- The actual matter-plus-hyperbolic modes have central charge 26. -/
theorem vnatHypMode_virasoro (κ ell : ℂ) (m n : ℤ) :
    vnatHypMode κ ell m * vnatHypMode κ ell n -
      vnatHypMode κ ell n * vnatHypMode κ ell m =
      ((m : ℂ) - n) • vnatHypMode κ ell (m + n) +
        if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * 26) • 1 else 0 := by
  change ⁅tensorTranslation (nearVirasoroMode VnatVOA.toNearVOA m) (hypSugawara κ ell m),
    tensorTranslation (nearVirasoroMode VnatVOA.toNearVOA n) (hypSugawara κ ell n)⁆ = _
  rw [nearTensorOperator_commutator]
  have hv := VnatVOA.toNearVOA.virasoro m n
  change ⁅nearVirasoroMode VnatVOA.toNearVOA m, nearVirasoroMode VnatVOA.toNearVOA n⁆ =
    ((m : ℂ) - n) • nearVirasoroMode VnatVOA.toNearVOA (m + n) +
      (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * 24) • 1 else 0) at hv
  rw [hv, show ⁅hypSugawara κ ell m, hypSugawara κ ell n⁆ = _ from
    hypSugawara_virasoro κ ell m n]
  have hc : (((m : ℂ) ^ 3 - m) / 12 * 26) =
      (((m : ℂ) ^ 3 - m) / 12 * 24) + (((m : ℂ) ^ 3 - m) / 12 * 2) := by ring
  rw [hc]
  apply TensorProduct.ext'
  intro x y
  by_cases h : m + n = 0
  · simp only [h, if_pos, vnatHypMode, tensorTranslation, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul, smul_add]
    abel
  · simp only [h, if_false, add_zero, vnatHypMode, tensorTranslation, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

def vnatHypForm : LinearMap.BilinForm ℂ (Vnat ⊗[ℂ] hypFock) := natForm.tmul hypForm

theorem vnatHypForm_symm (x y : Vnat ⊗[ℂ] hypFock) : vnatHypForm x y = vnatHypForm y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul v p =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | tmul w q =>
      change hypForm p q * natForm v w = hypForm q p * natForm w v
      rw [hypForm_symm, natForm_symm]

theorem vnatHypForm_adjoint (κ ell : ℂ) (n : ℤ) (x y : Vnat ⊗[ℂ] hypFock) :
    vnatHypForm (vnatHypMode κ ell n x) y = vnatHypForm x (vnatHypMode κ ell (-n) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul v p =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul w q =>
      simp only [vnatHypMode, tensorTranslation, LinearMap.add_apply,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add, LinearMap.add_apply,
        vnatHypForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul,
        hypForm_sugawara_adjoint]
      congr 1
      exact congrArg (fun z : ℂ => hypForm p q * z)
        (natForm_virasoro_adj vnat_twistedLocality n v w)

theorem vnatHypForm_coefficient (e : (ℕ × Fin 2) →₀ ℕ)
    (x : Vnat ⊗[ℂ] hypFock) (v : Vnat) :
    vnatHypForm x (v ⊗ₜ[ℂ] monomial (hypSwapExponent e) 1) =
      hypMonomialNorm e * natForm (hypTensorCoordinates x e) v := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [LinearEquiv.map_zero, Finsupp.zero_apply, LinearMap.map_zero,
      LinearMap.zero_apply, mul_zero]
  | add x y hx hy =>
    simp only [LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply,
      Finsupp.add_apply, hx, hy, mul_add]
  | tmul w p =>
    change hypForm p (monomial (hypSwapExponent e) 1) * natForm w v = _
    rw [hypForm_symm, hypForm_monomial, hypSwapExponent_involutive,
      hypMonomialNorm_swap, one_mul, hypTensorCoordinates_tmul, LinearMap.map_smul₂]
    simp only [smul_eq_mul]
    ring

/-- The concrete sector form is nondegenerate on the full tensor carrier. -/
theorem vnatHypForm_nondegenerate (x : Vnat ⊗[ℂ] hypFock) (hx : x ≠ 0) :
    ∃ y, vnatHypForm x y ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e, hypTensorCoordinates x e ≠ 0 := by
    by_contra! h
    apply hx
    apply hypTensorCoordinates.injective
    rw [LinearEquiv.map_zero]
    exact Finsupp.ext h
  obtain ⟨v, hv⟩ := moonshineForm_nondegenerate _ he
  refine ⟨v ⊗ₜ[ℂ] monomial (hypSwapExponent e) 1, ?_⟩
  rw [vnatHypForm_coefficient]
  exact mul_ne_zero (hypMonomialNorm_ne_zero e) hv

theorem vnatHypMode_lightConeSplit (κ ell : ℂ) (h : κ ≠ 0 ∨ ell ≠ 0) :
    ∃ a : Fin 2, IsCompl (⨆ j : ℕ, LinearMap.range (vnatHypMode κ ell (-(j + 1 : ℤ))))
      (⨅ j : ℕ, LinearMap.ker
        ((hypOscillator a (if a = 0 then κ else ell) (j + 1 : ℤ)).lTensor Vnat)) := by
  simpa only [vnatHypMode_negative] using vnatHypTensor_lightConeSplit κ ell h

end VOA.Moonshine.ConwayNorton
