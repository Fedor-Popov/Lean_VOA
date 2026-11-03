import VOA.Classification.COne.QExpThetaComparison

/-! # Removing all singularities of the theta/product quotient -/

open Complex Filter
open scoped Topology UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- At a simple zero of the denominator, use the ratio of derivatives. -/
def thetaRegularizedQuotient (f g : ℂ → ℂ) (x : ℂ) : ℂ :=
  if g x = 0 then _root_.deriv f x / _root_.deriv g x else f x / g x

/-- A quotient extends holomorphically when all denominator zeros are simple
and are also numerator zeros. -/
theorem thetaRegularizedQuotient_differentiable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : ∀ x, g x = 0 → f x = 0)
    (hsimple : ∀ x, g x = 0 → _root_.deriv g x ≠ 0) :
    Differentiable ℂ (thetaRegularizedQuotient f g) := by
  intro x
  by_cases hx : g x = 0
  · have hdsf : Differentiable ℂ (dslope f x) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 x)).mpr
        hf.differentiableOn
    have hdsg : Differentiable ℂ (dslope g x) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 x)).mpr
        hg.differentiableOn
    have hn : dslope g x x ≠ 0 := by simpa only [dslope_same] using hsimple x hx
    apply ((hdsf x).div (hdsg x) hn).congr_of_eventuallyEq
    filter_upwards [(hdsg x).continuousAt.eventually_ne hn] with y hy
    by_cases hyx : y = x
    · subst y
      simp [thetaRegularizedQuotient, hx, dslope_same, Pi.div_apply]
    · have hgy : g y ≠ 0 := by
        intro hgy
        apply hy
        simp [dslope_of_ne _ hyx, slope_def_field, hx, hgy]
      simp only [thetaRegularizedQuotient, if_neg hgy, Pi.div_apply, dslope_of_ne _ hyx,
        slope_def_field, hzeros x hx, hx, sub_zero]
      field_simp [sub_ne_zero.mpr hyx]
  · apply ((hf x).div (hg x) hx).congr_of_eventuallyEq
    filter_upwards [(hg x).continuousAt.eventually_ne hx] with y hy
    simp [thetaRegularizedQuotient, hy, Pi.div_apply]

/-- The explicitly repaired quotient for the shifted theta and product. -/
def thetaProductQuotient (τ : ℍ) : ℂ → ℂ :=
  thetaRegularizedQuotient (fun x => jacobiTheta₂ (x - ((τ : ℂ) + 1) / 2) τ)
    (fun x => thetaShiftedProduct x τ)

/-- All removable singularities in this route are discharged. -/
theorem thetaProductQuotient_differentiable (τ : ℍ) :
    Differentiable ℂ (thetaProductQuotient τ) := by
  apply thetaRegularizedQuotient_differentiable
  · have h : Differentiable ℂ (fun z => jacobiTheta₂ z τ) :=
      fun z => differentiableAt_jacobiTheta₂_fst z τ.im_pos
    exact h.comp (differentiable_id.sub_const (((τ : ℂ) + 1) / 2))
  · exact thetaShiftedProduct_differentiable τ
  · intro x hx
    obtain ⟨m, k, rfl⟩ := (thetaShiftedProduct_eq_zero_iff τ x).mp hx
    exact theta_lattice_zero τ m k
  · exact thetaShiftedProduct_deriv_ne_zero_of_zero τ

/-- The extension still multiplies back to theta, including at every zero. -/
theorem thetaProductQuotient_mul (τ : ℍ) (x : ℂ) :
    thetaProductQuotient τ x * thetaShiftedProduct x τ =
      jacobiTheta₂ (x - ((τ : ℂ) + 1) / 2) τ := by
  by_cases hx : thetaShiftedProduct x τ = 0
  · obtain ⟨m, k, he⟩ := (thetaShiftedProduct_eq_zero_iff τ x).mp hx
    rw [hx, mul_zero, he, theta_lattice_zero]
  · simp only [thetaProductQuotient, thetaRegularizedQuotient, if_neg hx]
    exact div_mul_cancel₀ _ hx

end VOA.Classification.COne.SSHecke
