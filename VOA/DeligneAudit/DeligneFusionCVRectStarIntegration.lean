import VOA.DeligneAudit.DeligneFusionCVRectStarIdeal

/-!
# The actual leaf-color integration map for the star coefficient ideal

Fixing the middle and right powers reduces the coefficient-order
induction to the checked two-color induction. Both other currents have
zero derivative in the selected left zero-mode variable. The proof
includes every polynomial multiplier and concludes ideal preservation
modulo the linear subspace independent of that variable.
-/

namespace VOA.DeligneAudit.A2.CVRectStarIntegration

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectStarIdeal

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def functionalStar (ℓ : Polynomial A →ₗ[ℂ] ℂ) (B : A)
    (X Y Z : PowerSeries (Polynomial A)) (p q r i : ℕ) : PowerSeries ℂ :=
  linearSeries ℓ (PowerSeries.C (Polynomial.X ^ i * Polynomial.C B) *
    (X ^ p * Y ^ q * Z ^ r))

theorem functionalStar_eq_current (ℓ : Polynomial A →ₗ[ℂ] ℂ) (B : A)
    (X Y Z : PowerSeries (Polynomial A)) (p q r i : ℕ) :
    functionalStar ℓ B X Y Z p q r i =
      functionalCurrent ℓ B X (Y ^ q * Z ^ r) p 1 i := by
  simp only [functionalStar, functionalCurrent, pow_one, mul_assoc]

/-- The leaf recurrence is derived from the actual polynomial primitive
and derivative, with no target-ideal premise. -/
theorem functionalStar_recurrence (ℓ : Polynomial A →ₗ[ℂ] ℂ)
    (hℓ : ∀ B : A, ℓ (Polynomial.C B) = 0)
    (X Y Z : PowerSeries (Polynomial A)) (h : ℕ)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ h)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) (B : A) (p q r i : ℕ) :
    functionalStar ℓ B X Y Z p q r i =
      (i : ℂ) • functionalStar (ℓ.comp primitive) B X Y Z p q r (i - 1) +
      (p : ℂ) • (PowerSeries.X ^ h *
        functionalStar (ℓ.comp primitive) B X Y Z (p - 1) q r i) := by
  have hYZ : seriesDerivation innerDerivative (Y ^ q * Z ^ r) = 0 := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, hY, hZ]
    simp only [smul_zero, add_zero]
  simpa only [functionalStar_eq_current] using
    functionalCurrent_recurrence ℓ hℓ X (Y ^ q * Z ^ r) h hX hYZ B p 1 i

/-- The entire decreased-capacity star ideal is annihilated after
normalized integration against a source-ideal annihilator. -/
theorem annihilator_transfer (X Y Z : PowerSeries (Polynomial A))
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ left.length)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0)
    (ℓ : Polynomial A →ₗ[ℂ] ℂ)
    (hℓJ : ∀ P ∈ coefficientIdeal3 X Y Z (starOrder (K :: left) right center), ℓ P = 0)
    (hℓC : ∀ B : A, ℓ (Polynomial.C B) = 0) :
    ∀ P ∈ coefficientIdeal3 X Y Z (starOrder ((K - 1) :: left) right center),
      (ℓ.comp primitive) P = 0 := by
  have hcurrent : ∀ B : A, ∀ p q r i,
      ZeroBelow (functionalStar (ℓ.comp primitive) B X Y Z p q r i)
        (starOrder ((K - 1) :: left) right center p q r) := by
    intro B p q r i
    rw [active_site_order]
    apply active_site_order_transfer
      (fun p i => functionalStar ℓ B X Y Z p q r i)
      (fun p i => functionalStar (ℓ.comp primitive) B X Y Z p q r i)
      left (excess right (q + r) + excess center q) K q hK hmax ?_ ?_ p i
    · intro p i j hj
      unfold functionalStar
      rw [coeff_linearSeries, PowerSeries.coeff_C_mul]
      apply hℓJ
      apply Ideal.mul_mem_left
      refine Ideal.subset_span ⟨p, q, r, j, ?_, rfl⟩
      rwa [active_site_order]
    · intro p i
      exact functionalStar_recurrence ℓ hℓC X Y Z left.length hX hY hZ B p q r i
  have hmultiple : ∀ P : Polynomial A, ∀ p q r j,
      j < starOrder ((K - 1) :: left) right center p q r →
      (ℓ.comp primitive) (P * PowerSeries.coeff j (X ^ p * Y ^ q * Z ^ r)) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        intro p q r j hj
        rw [add_mul, map_add, hP p q r j hj, hQ p q r j hj, add_zero]
    | monomial i B =>
        intro p q r j hj
        have hc := hcurrent B p q r i j hj
        unfold functionalStar at hc
        rw [coeff_linearSeries, PowerSeries.coeff_C_mul] at hc
        simpa only [Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial] using hc
  intro P hP
  have hstrong : ∀ Q ∈ coefficientIdeal3 X Y Z
      (starOrder ((K - 1) :: left) right center),
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

/-- The actual primitive preserves the complete target star ideal
modulo the source ideal plus the zero-mode-free linear subspace. -/
theorem primitive_preserves (X Y Z : PowerSeries (Polynomial A))
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K)
    (hX : seriesDerivation innerDerivative X = PowerSeries.X ^ left.length)
    (hY : seriesDerivation innerDerivative Y = 0)
    (hZ : seriesDerivation innerDerivative Z = 0) :
    (coefficientIdeal3 X Y Z
      (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 X Y Z (starOrder (K :: left) right center)).restrictScalars ℂ ⊔
        CVRectIntegrationIdeal.constants).comap primitive := by
  apply VOA.DeligneAudit.CVRectSeparation.primitive_preserves_of_functional
  intro ℓ hJ hU P hP
  exact annihilator_transfer X Y Z left right center K hK hmax hX hY hZ ℓ
    (fun P hP => hJ hP) (fun B => hU ⟨B, rfl⟩) P hP

/-- Concrete selected and independent currents discharge every
derivative premise of the actual star ideal map. -/
theorem chosen_primitive_preserves (f g h : PowerSeries A)
    (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hmax : ∀ k ∈ left, k ≤ K) :
    (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
      (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder (K :: left) right center)).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive :=
  primitive_preserves _ _ _ left right center K hK hmax (derivative_chosenCurrent _ _)
    (derivative_constantCurrent _) (derivative_constantCurrent _)

end

end VOA.DeligneAudit.A2.CVRectStarIntegration

#print axioms VOA.DeligneAudit.A2.CVRectStarIntegration.functionalStar_recurrence
#print axioms VOA.DeligneAudit.A2.CVRectStarIntegration.primitive_preserves
#print axioms VOA.DeligneAudit.A2.CVRectStarIntegration.chosen_primitive_preserves
