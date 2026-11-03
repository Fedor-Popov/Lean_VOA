import VOA.DeligneAudit.DeligneFusionCVRectStarIntegration
import VOA.DeligneAudit.DeligneFusionCVRectStarShift
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationDimension

/-! # The actual polynomial two-piece dimension step for a star leaf -/

namespace VOA.DeligneAudit.A2.CVRectStarDimension

open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The smaller actual star quotients bound the source by checked
leaf shift/integration maps and rank--nullity. No recurrence is assumed. -/
theorem polynomial_dimension_step (f g h : PowerSeries A)
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K)
    [FiniteDimensional ℂ (A ⧸
      (coefficientIdeal3 f g h (starOrder left right (K :: center))).restrictScalars ℂ)]
    [FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ)] :
    FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder (K :: left) right center)).restrictScalars ℂ) ∧
      Module.finrank ℂ (Polynomial A ⧸
        (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
          (starOrder (K :: left) right center)).restrictScalars ℂ) ≤
        Module.finrank ℂ (Polynomial A ⧸
          (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
            (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ) +
        Module.finrank ℂ (A ⧸
          (coefficientIdeal3 f g h (starOrder left right (K :: center))).restrictScalars ℂ) := by
  let X := chosenCurrent left.length f
  let Y := constantCurrent g
  let Z := constantCurrent h
  let I := (coefficientIdeal3 f g h (starOrder left right (K :: center))).restrictScalars ℂ
  let J := (coefficientIdeal3 X Y Z (starOrder (K :: left) right center)).restrictScalars ℂ
  let L := (coefficientIdeal3 X Y Z
    (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ
  let C := (Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).toLinearMap
  have hI : I ≤ J.comap C := by
    intro P hP
    exact (Ideal.map_le_iff_le_comap.mp
      (CVRectStarShift.shift_ideal_map f g h left right center K)) hP
  have hdesc : L ≤ (J ⊔ CVRectIntegrationIdeal.constants).comap primitive :=
    CVRectStarIntegration.chosen_primitive_preserves f g h left right center K hK hmax
  have hprim : ∀ p : Polynomial A, p - primitive (innerDerivative p) ∈
      CVRectIntegrationIdeal.constants := by
    intro p
    change p - primitive (Polynomial.derivative p) ∈ CVRectIntegrationIdeal.constants
    rw [primitive_derivative]
    have hp : p - (p - Polynomial.C (p.coeff 0)) = Polynomial.C (p.coeff 0) := by abel
    rw [hp]
    exact ⟨p.coeff 0, rfl⟩
  have hb := VOA.DeligneAudit.CVRectSeparation.primitive_quotient_bound
    J CVRectIntegrationIdeal.constants L primitive innerDerivative.toLinearMap hdesc hprim
  haveI : FiniteDimensional ℂ (Polynomial A ⧸ (J ⊔ C.range)) := hb.1
  have hq := CVRectIntegrationDimension.quotient_two_term I J C hI
  exact ⟨hq.1, hq.2.trans (Nat.add_le_add_right hb.2 _)⟩

end

end VOA.DeligneAudit.A2.CVRectStarDimension

#print axioms VOA.DeligneAudit.A2.CVRectStarDimension.polynomial_dimension_step
