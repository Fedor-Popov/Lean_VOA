import VOA.DeligneAudit.DeligneFusionCVRectIntegrationSeries
import VOA.DeligneAudit.DeligneFusionCVRectSeparation

/-!
# Normalized integration preserves the actual coefficient ideal modulo constants

The current coefficient ideal includes all its polynomial multiples.
The proof derives the functional recurrence from the actual derivative,
applies the maximal-capacity order induction, and then uses algebraic
dual separation. The subspace of polynomials independent of the chosen
zero-mode variable is treated only as a linear subspace.
-/

namespace VOA.DeligneAudit.A2.CVRectIntegrationIdeal

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The mixed-current coefficient ideal for a specified order function. -/
def coefficientIdeal {R : Type*} [CommRing R] (S T : PowerSeries R) (μ : ℕ → ℕ → ℕ) :
    Ideal R :=
  Ideal.span {P | ∃ a b j, j < μ a b ∧ P = PowerSeries.coeff j (S ^ a * T ^ b)}

/-- The active capacities include the selected site `K`; the inactive
sites see only the other color's power `b`. -/
def mixedOrder (ks inactive : List ℕ) (K a b : ℕ) : ℕ :=
  siteOrder ks (excess inactive b) K b a

/-- The subspace independent of the distinguished zero-mode variable. -/
def constants : Submodule ℂ (Polynomial A) :=
  LinearMap.range (Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).toLinearMap

/-- An annihilator of the source coefficient ideal and the constant
subspace transfers to the whole target ideal under the actual primitive. -/
theorem annihilator_transfer (S T : PowerSeries (Polynomial A))
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ ks.length)
    (hT : seriesDerivation innerDerivative T = 0)
    (ℓ : Polynomial A →ₗ[ℂ] ℂ)
    (hℓJ : ∀ P ∈ coefficientIdeal S T (mixedOrder ks inactive K), ℓ P = 0)
    (hℓC : ∀ B : A, ℓ (Polynomial.C B) = 0) :
    ∀ P ∈ coefficientIdeal S T (mixedOrder ks inactive (K - 1)),
      (ℓ.comp primitive) P = 0 := by
  have hcurrent : ∀ B : A, ∀ a b i,
      ZeroBelow (functionalCurrent (ℓ.comp primitive) B S T a b i)
        (mixedOrder ks inactive (K - 1) a b) := by
    intro B a b i
    apply active_site_order_transfer
      (fun a i => functionalCurrent ℓ B S T a b i)
      (fun a i => functionalCurrent (ℓ.comp primitive) B S T a b i)
      ks (excess inactive b) K b hK hmax ?_ ?_ a i
    · intro a i j hj
      unfold functionalCurrent
      rw [coeff_linearSeries, mul_assoc, PowerSeries.coeff_C_mul]
      apply hℓJ
      apply Ideal.mul_mem_left
      exact Ideal.subset_span ⟨a, b, j, hj, rfl⟩
    · intro a i
      exact functionalCurrent_recurrence ℓ hℓC S T ks.length hS hT B a b i
  have hmultiple : ∀ P : Polynomial A, ∀ a b j,
      j < mixedOrder ks inactive (K - 1) a b →
      (ℓ.comp primitive) (P * PowerSeries.coeff j (S ^ a * T ^ b)) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        intro a b j hj
        rw [add_mul, map_add, hP a b j hj, hQ a b j hj, add_zero]
    | monomial i B =>
        intro a b j hj
        have hc := hcurrent B a b i j hj
        unfold functionalCurrent at hc
        rw [coeff_linearSeries, mul_assoc, PowerSeries.coeff_C_mul] at hc
        simpa only [Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial]
          using hc
  intro P hP
  have hstrong : ∀ Q ∈ coefficientIdeal S T (mixedOrder ks inactive (K - 1)),
      ∀ M : Polynomial A, (ℓ.comp primitive) (M * Q) = 0 := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
        obtain ⟨a, b, j, hj, rfl⟩ := hQ
        exact fun M => hmultiple M a b j hj
    | zero => intro M; simp
    | add Q Q' hQ hQ' ih ih' => intro M; rw [mul_add, map_add, ih M, ih' M, add_zero]
    | smul c Q hQ ih =>
        intro M
        change (ℓ.comp primitive) (M * (c * Q)) = 0
        rw [← mul_assoc]
        exact ih (M * c)
  simpa only [one_mul] using hstrong P hP 1

/-- The actual normalized primitive preserves the entire target ideal
modulo the source ideal plus the shift image. -/
theorem primitive_preserves (S T : PowerSeries (Polynomial A))
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ ks.length)
    (hT : seriesDerivation innerDerivative T = 0) :
    (coefficientIdeal S T (mixedOrder ks inactive (K - 1))).restrictScalars ℂ ≤
      ((coefficientIdeal S T (mixedOrder ks inactive K)).restrictScalars ℂ ⊔ constants).comap
        primitive := by
  apply VOA.DeligneAudit.CVRectSeparation.primitive_preserves_of_functional
  intro ℓ hJ hU P hP
  exact annihilator_transfer S T ks inactive K hK hmax hS hT ℓ
    (fun P hP => hJ hP) (fun B => hU ⟨B, rfl⟩) P hP

/-- The concrete chosen-current forms discharge every derivative premise
of ideal preservation. -/
theorem chosen_primitive_preserves (f g : PowerSeries A)
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K) :
    (coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
      (mixedOrder ks inactive (K - 1))).restrictScalars ℂ ≤
      ((coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
        (mixedOrder ks inactive K)).restrictScalars ℂ ⊔ constants).comap primitive :=
  primitive_preserves _ _ ks inactive K hK hmax
    (derivative_chosenCurrent _ _) (derivative_constantCurrent _)

/-- The actual map from the decreased-capacity quotient to the source
quotient modulo the shift image. -/
def primitiveQuotientMap (S T : PowerSeries (Polynomial A))
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ ks.length)
    (hT : seriesDerivation innerDerivative T = 0) :
    (Polynomial A ⧸ (coefficientIdeal S T (mixedOrder ks inactive (K - 1))).restrictScalars ℂ)
      →ₗ[ℂ] (Polynomial A ⧸
        ((coefficientIdeal S T (mixedOrder ks inactive K)).restrictScalars ℂ ⊔ constants)) :=
  Submodule.mapQ _ _ primitive (primitive_preserves S T ks inactive K hK hmax hS hT)

/-- Surjectivity of the actual normalized-integration quotient map is the
upper-bound direction of the commutative recursion. -/
theorem primitiveQuotientMap_surjective (S T : PowerSeries (Polynomial A))
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ ks.length)
    (hT : seriesDerivation innerDerivative T = 0) :
    Function.Surjective (primitiveQuotientMap S T ks inactive K hK hmax hS hT) := by
  apply VOA.DeligneAudit.CVRectSeparation.primitive_quotient_surjective
    (I := primitive) (D := innerDerivative.toLinearMap)
  intro p
  change p - primitive (Polynomial.derivative p) ∈ constants
  rw [primitive_derivative]
  have hp : p - (p - Polynomial.C (p.coeff 0)) = Polynomial.C (p.coeff 0) := by abel
  rw [hp]
  exact ⟨p.coeff 0, rfl⟩

/-- Finite-dimensionality of the decreased-capacity quotient bounds the
actual quotient modulo the shift image. No product count is a premise. -/
theorem primitiveQuotient_bound (S T : PowerSeries (Polynomial A))
    (ks inactive : List ℕ) (K : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ ks.length)
    (hT : seriesDerivation innerDerivative T = 0)
    [FiniteDimensional ℂ (Polynomial A ⧸
      (coefficientIdeal S T (mixedOrder ks inactive (K - 1))).restrictScalars ℂ)] :
    FiniteDimensional ℂ (Polynomial A ⧸
        ((coefficientIdeal S T (mixedOrder ks inactive K)).restrictScalars ℂ ⊔ constants)) ∧
      Module.finrank ℂ (Polynomial A ⧸
        ((coefficientIdeal S T (mixedOrder ks inactive K)).restrictScalars ℂ ⊔ constants)) ≤
      Module.finrank ℂ (Polynomial A ⧸
        (coefficientIdeal S T (mixedOrder ks inactive (K - 1))).restrictScalars ℂ) := by
  have hs := primitiveQuotientMap_surjective S T ks inactive K hK hmax hS hT
  exact ⟨Module.Finite.of_surjective _ hs, LinearMap.finrank_le_finrank_of_surjective hs⟩

end

end VOA.DeligneAudit.A2.CVRectIntegrationIdeal

#print axioms VOA.DeligneAudit.A2.CVRectIntegrationIdeal.annihilator_transfer
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationIdeal.primitive_preserves
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationIdeal.chosen_primitive_preserves
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationIdeal.primitiveQuotientMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationIdeal.primitiveQuotient_bound
