import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveOrder
import VOA.DeligneAudit.DeligneFusionCVRectAdjointIntegration

/-! # Actual primitive and shift ideal maps for the five-monomial shape -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveMaps

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFiveOrder

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem five_special_primitive (f g h : PowerSeries A) (active center : List ℕ)
    (hactive : ∀ k ∈ active, k ≤ 1) :
    (coefficientIdeal3 (chosenCurrent active.length f) (constantCurrent g) (constantCurrent h)
      (threeTailOrder active center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent active.length f) (constantCurrent g) (constantCurrent h)
        (fiveTailOrder active center)).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive := by
  apply CVRectAdjointIntegration.primitive_preserves_of_orders _ _ _ _ _
    (fun _ _ => 0) (fun q _ => fiveCapacity q) active.length ?_ ?_ ?_
    (derivative_chosenCurrent _ _) (derivative_constantCurrent _) (derivative_constantCurrent _)
  · intro p q r hp
    change p + 1 < fiveCapacity q at hp
    have hk := fiveCapacity_le_one q
    omega
  · intro p q r hp
    exact five_special_high active center hactive p q r (by omega)
  · intro p q r
    simpa only [Nat.add_zero] using five_special_decrement active center p q r

theorem five_ordinary_primitive (f g h : PowerSeries A) (active center : List ℕ)
    (K : ℕ) (hK : 2 ≤ K) (hmax : ∀ k ∈ active, k ≤ K) :
    (coefficientIdeal3 (chosenCurrent (active.length + 1) f)
      (constantCurrent g) (constantCurrent h)
      (fiveTailOrder ((K - 1) :: active) center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent (active.length + 1) f)
        (constantCurrent g) (constantCurrent h)
        (fiveTailOrder (K :: active) center)).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive := by
  apply CVRectAdjointIntegration.primitive_preserves_of_orders _ _ _ _ _
    (fun q _ => q) (fun _ _ => K) (active.length + 1) ?_ ?_ ?_
    (derivative_chosenCurrent _ _) (derivative_constantCurrent _) (derivative_constantCurrent _)
  · exact five_ordinary_low active center K
  · intro p q r hp
    exact five_ordinary_high active center K p q r hK hmax hp
  · intro p q r
    exact five_ordinary_decrement active center K p q r (by omega)

omit [Algebra ℂ A] in
theorem five_special_shift (f g h : PowerSeries A) (active center : List ℕ) :
    Ideal.map Polynomial.C (coefficientIdeal3 f g h (twoTailOrder active center)) ≤
      coefficientIdeal3 (chosenCurrent active.length f) (constantCurrent g) (constantCurrent h)
        (fiveTailOrder active center) :=
  CVRectAdjointShift.shift_ideal_map_of_orders f g h _ _ active.length
    (five_special_shift_le active center)

omit [Algebra ℂ A] in
theorem five_ordinary_shift (f g h : PowerSeries A) (active center : List ℕ) (K : ℕ) :
    Ideal.map Polynomial.C (coefficientIdeal3 f g h (fiveTailOrder active (K :: center))) ≤
      coefficientIdeal3 (chosenCurrent (active.length + 1) f)
        (constantCurrent g) (constantCurrent h) (fiveTailOrder (K :: active) center) :=
  CVRectAdjointShift.shift_ideal_map_of_orders f g h _ _ (active.length + 1)
    (five_ordinary_shift_le active center K)

end
end VOA.DeligneAudit.A2.CVRectAdjointFiveMaps

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveMaps.five_special_primitive
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveMaps.five_ordinary_primitive
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveMaps.five_special_shift
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveMaps.five_ordinary_shift
