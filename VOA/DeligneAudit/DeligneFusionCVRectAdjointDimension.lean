import VOA.DeligneAudit.DeligneFusionCVRectAdjointIntegration
import VOA.DeligneAudit.DeligneFusionCVRectAdjointShift
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationDimension

/-! # Actual polynomial dimension steps for the adjoint-site split -/

namespace VOA.DeligneAudit.A2.CVRectAdjointDimension

open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectAdjointOrder

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Rank--nullity converts the proved actual primitive and shift maps
to a two-piece polynomial quotient upper bound. -/
theorem polynomial_dimension_step (f g h : PowerSeries A)
    (μ τ σ : ℕ → ℕ → ℕ → ℕ) (n : ℕ)
    (hshift : Ideal.map Polynomial.C (coefficientIdeal3 f g h σ) ≤
      coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h) μ)
    (hprimitive :
      (coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
        τ).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
        μ).restrictScalars ℂ ⊔ CVRectIntegrationIdeal.constants).comap primitive)
    [FiniteDimensional ℂ (A ⧸ (coefficientIdeal3 f g h σ).restrictScalars ℂ)]
    [FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
        τ).restrictScalars ℂ)] :
    FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
        μ).restrictScalars ℂ) ∧
      Module.finrank ℂ (Polynomial A ⧸
        (coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
          μ).restrictScalars ℂ) ≤
        Module.finrank ℂ (Polynomial A ⧸
          (coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h)
            τ).restrictScalars ℂ) +
        Module.finrank ℂ (A ⧸ (coefficientIdeal3 f g h σ).restrictScalars ℂ) := by
  let X := chosenCurrent n f
  let Y := constantCurrent g
  let Z := constantCurrent h
  let I := (coefficientIdeal3 f g h σ).restrictScalars ℂ
  let J := (coefficientIdeal3 X Y Z μ).restrictScalars ℂ
  let L := (coefficientIdeal3 X Y Z τ).restrictScalars ℂ
  let C := (Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).toLinearMap
  have hI : I ≤ J.comap C := fun P hP => (Ideal.map_le_iff_le_comap.mp hshift) hP
  have hprim : ∀ p : Polynomial A, p - primitive (innerDerivative p) ∈
      CVRectIntegrationIdeal.constants := by
    intro p
    change p - primitive (Polynomial.derivative p) ∈ CVRectIntegrationIdeal.constants
    rw [primitive_derivative]
    have hp : p - (p - Polynomial.C (p.coeff 0)) = Polynomial.C (p.coeff 0) := by abel
    rw [hp]
    exact ⟨p.coeff 0, rfl⟩
  have hb := VOA.DeligneAudit.CVRectSeparation.primitive_quotient_bound
    J CVRectIntegrationIdeal.constants L primitive innerDerivative.toLinearMap hprimitive hprim
  haveI : FiniteDimensional ℂ (Polynomial A ⧸ (J ⊔ C.range)) := hb.1
  have hq := CVRectIntegrationDimension.quotient_two_term I J C hI
  exact ⟨hq.1, hq.2.trans (Nat.add_le_add_right hb.2 _)⟩

/-- The actual adjoint-site `5+3` upper step; neither ideal map is an input. -/
theorem adjoint_special_dimension_step (f g h : PowerSeries A)
    (left right center : List ℕ) (hleft : ∀ k ∈ left, k ≤ 1)
    [FiniteDimensional ℂ (A ⧸
      (coefficientIdeal3 f g h (fiveSiteOrder left right center)).restrictScalars ℂ)]
    [FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (threeSiteOrder left right center)).restrictScalars ℂ)] :
    FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (adjointOrder left right center)).restrictScalars ℂ) ∧
      Module.finrank ℂ (Polynomial A ⧸
        (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
          (adjointOrder left right center)).restrictScalars ℂ) ≤
        Module.finrank ℂ (Polynomial A ⧸
          (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
            (threeSiteOrder left right center)).restrictScalars ℂ) +
        Module.finrank ℂ (A ⧸
          (coefficientIdeal3 f g h (fiveSiteOrder left right center)).restrictScalars ℂ) :=
  polynomial_dimension_step f g h _ _ _ left.length
    (CVRectAdjointShift.adjoint_special_shift f g h left right center)
    (CVRectAdjointIntegration.chosen_adjoint_special_primitive f g h left right center hleft)

end
end VOA.DeligneAudit.A2.CVRectAdjointDimension

#print axioms VOA.DeligneAudit.A2.CVRectAdjointDimension.adjoint_special_dimension_step
