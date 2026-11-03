import VOA.DeligneAudit.DeligneFusionCVRectAdjointOrder
import VOA.DeligneAudit.DeligneFusionCVRectStarIntegration

/-!
# Actual primitive maps from explicit low/high coefficient orders

The generic theorem below derives preservation of a coefficient ideal
from the checked two finite order inductions and ordinary polynomial
differentiation. The special adjoint-site instance uses its concrete
piecewise capacity, including capacity zero.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointIntegration

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarIntegration
open VOA.DeligneAudit.A2.CVRectAdjointOrder

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The actual polynomial primitive preserves the target ideal whenever
the explicit source orders satisfy the two finite induction inequalities. -/
theorem primitive_preserves_of_orders (X Y Z : PowerSeries (Polynomial A))
    (μ τ : ℕ → ℕ → ℕ → ℕ) (b K : ℕ → ℕ → ℕ) (h : ℕ)
    (hlow : ∀ p q r, p + 1 + b q r < K q r → μ (p + 1) q r ≤ μ p q r + h)
    (hhigh : ∀ p q r, K q r ≤ p + b q r → μ (p + 1) q r = μ p q r + h + 1)
    (htarget : ∀ p q r, τ p q r =
      if p + b q r < K q r then μ p q r else μ p q r + 1)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ h)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) :
    (coefficientIdeal3 X Y Z τ).restrictScalars ℂ ≤
      ((coefficientIdeal3 X Y Z μ).restrictScalars ℂ ⊔
        CVRectIntegrationIdeal.constants).comap primitive := by
  apply VOA.DeligneAudit.CVRectSeparation.primitive_preserves_of_functional
  intro ℓ hJ hU P hP
  have hℓC : ∀ B : A, ℓ (Polynomial.C B) = 0 := fun B => hU ⟨B, rfl⟩
  have hcurrent : ∀ B : A, ∀ p q r i,
      ZeroBelow (functionalStar (ℓ.comp primitive) B X Y Z p q r i) (τ p q r) := by
    intro B p q r i
    rw [htarget]
    apply order_transfer
      (fun p i => functionalStar ℓ B X Y Z p q r i)
      (fun p i => functionalStar (ℓ.comp primitive) B X Y Z p q r i)
      (fun p => μ p q r) (b q r) (K q r) h ?_ ?_
      (fun p hp => hlow p q r hp) (fun p hp => hhigh p q r hp) p i
    · intro p i j hj
      unfold functionalStar
      rw [coeff_linearSeries, PowerSeries.coeff_C_mul]
      apply hJ
      apply Ideal.mul_mem_left
      exact Ideal.subset_span ⟨p, q, r, j, hj, rfl⟩
    · intro p i
      exact functionalStar_recurrence ℓ hℓC X Y Z h hX hY hZ B p q r i
  have hmultiple : ∀ M : Polynomial A, ∀ p q r j, j < τ p q r →
      (ℓ.comp primitive) (M * PowerSeries.coeff j (X ^ p * Y ^ q * Z ^ r)) = 0 := by
    intro M
    induction M using Polynomial.induction_on' with
    | add M N hM hN =>
        intro p q r j hj
        rw [add_mul, map_add, hM p q r j hj, hN p q r j hj, add_zero]
    | monomial i B =>
        intro p q r j hj
        have hc := hcurrent B p q r i j hj
        unfold functionalStar at hc
        rw [coeff_linearSeries, PowerSeries.coeff_C_mul] at hc
        simpa only [Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial] using hc
  have hstrong : ∀ Q ∈ coefficientIdeal3 X Y Z τ,
      ∀ M : Polynomial A, (ℓ.comp primitive) (M * Q) = 0 := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
        obtain ⟨p, q, r, j, hj, rfl⟩ := hQ
        exact fun M => hmultiple M p q r j hj
    | zero => intro M; simp
    | add Q Q' hQ hQ' ih ih' => intro M; rw [mul_add, map_add, ih M, ih' M, add_zero]
    | smul c Q hQ ih =>
        intro M
        change (ℓ.comp primitive) (M * (c * Q)) = 0
        rw [← mul_assoc]
        exact ih (M * c)
  simpa only [one_mul] using hstrong P hP 1

/-- The special adjoint x-site has actual primitive image in the source
ideal plus the zero-mode-free linear subspace. Its other x-sites have
already been reduced to capacity at most one. -/
theorem adjoint_special_primitive (X Y Z : PowerSeries (Polynomial A))
    (left right center : List ℕ) (hleft : ∀ k ∈ left, k ≤ 1)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ left.length)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) :
    (coefficientIdeal3 X Y Z (threeSiteOrder left right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 X Y Z (adjointOrder left right center)).restrictScalars ℂ ⊔
        CVRectIntegrationIdeal.constants).comap primitive := by
  apply primitive_preserves_of_orders X Y Z _ _ (fun _ _ => 0) adjCapacity
    left.length ?_ ?_ ?_ hX hY hZ
  · intro p q r hp
    have hk := adjCapacity_le_one q r
    omega
  · intro p q r hp
    exact adjoint_special_high left right center hleft p q r (by omega)
  · intro p q r
    simpa only [Nat.add_zero] using adjoint_special_decrement left right center p q r

theorem adjoint_ordinary_primitive (X Y Z : PowerSeries (Polynomial A))
    (left right center : List ℕ) (K : ℕ) (hK : 2 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ (left.length + 1))
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) :
    (coefficientIdeal3 X Y Z
      (adjointOrder ((K - 1) :: left) right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 X Y Z (adjointOrder (K :: left) right center)).restrictScalars ℂ ⊔
        CVRectIntegrationIdeal.constants).comap primitive := by
  apply primitive_preserves_of_orders X Y Z _ _ (fun q _ => q) (fun _ _ => K)
    (left.length + 1) ?_ ?_ ?_ hX hY hZ
  · exact adjoint_ordinary_low left right center K
  · intro p q r hp
    exact adjoint_ordinary_high left right center K p q r hK hmax hp
  · intro p q r
    exact adjoint_ordinary_decrement left right center K p q r (by omega)

/-- Concrete selected and independent currents discharge all derivative
premises for the actual special adjoint-site map. -/
theorem chosen_adjoint_special_primitive (f g h : PowerSeries A)
    (left right center : List ℕ) (hleft : ∀ k ∈ left, k ≤ 1) :
    (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
      (threeSiteOrder left right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (adjointOrder left right center)).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive :=
  adjoint_special_primitive _ _ _ left right center hleft (derivative_chosenCurrent _ _)
    (derivative_constantCurrent _) (derivative_constantCurrent _)

end
end VOA.DeligneAudit.A2.CVRectAdjointIntegration

#print axioms VOA.DeligneAudit.A2.CVRectAdjointIntegration.primitive_preserves_of_orders
#print axioms VOA.DeligneAudit.A2.CVRectAdjointIntegration.adjoint_special_primitive
#print axioms VOA.DeligneAudit.A2.CVRectAdjointIntegration.adjoint_ordinary_primitive
