import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveLeftOrder
import VOA.DeligneAudit.DeligneFusionCVRectAdjointIntegration
import VOA.DeligneAudit.DeligneFusionCVRectAdjointShift

/-! # Actual primitive and shift ideal maps for ordinary five-family left sites -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Integration preserves the full decreased-capacity coefficient ideal,
including all polynomial multiples. Every preservation premise is proved. -/
theorem left_primitive (X Y Z : PowerSeries (Polynomial A))
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ left.length)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) :
    (coefficientIdeal3 X Y Z
      (fiveSiteOrder ((K - 1) :: left) right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 X Y Z (fiveSiteOrder (K :: left) right center)).restrictScalars ℂ ⊔
        CVRectIntegrationIdeal.constants).comap primitive := by
  apply CVRectAdjointIntegration.primitive_preserves_of_orders X Y Z _ _
    (fun q _ => q) (fun _ _ => K) left.length ?_ ?_ ?_ hX hY hZ
  · exact left_low left right center K
  · intro p q r hp
    exact left_high left right center K p q r hmax hp
  · intro p q r
    exact left_decrement left right center K p q r hK

theorem chosen_left_primitive (f g h : PowerSeries A)
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K) :
    (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
      (fiveSiteOrder ((K - 1) :: left) right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (fiveSiteOrder (K :: left) right center)).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive :=
  left_primitive _ _ _ left right center K hK hmax (derivative_chosenCurrent _ _)
    (derivative_constantCurrent _) (derivative_constantCurrent _)

/-- The actual constant-branch shift preserves every coefficient ideal
generator, by its proved binomial order inequality. -/
theorem left_shift (f g h : PowerSeries A) (left right center : List ℕ) (K : ℕ) :
    Ideal.map Polynomial.C
      (coefficientIdeal3 f g h (fiveSiteOrder left right (K :: center))) ≤
      coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (fiveSiteOrder (K :: left) right center) :=
  CVRectAdjointShift.shift_ideal_map_of_orders f g h _ _ left.length
    (left_shift_le left right center K)

end

end VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.chosen_left_primitive
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.left_shift
