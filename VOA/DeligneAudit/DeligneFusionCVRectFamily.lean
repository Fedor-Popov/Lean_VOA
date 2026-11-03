import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCurrentSplit
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationDimension
import VOA.DeligneAudit.DeligneFusionCVRectZero
import VOA.DeligneAudit.DeligneFusionCVRectCount

/-!
# Canonical finite polynomial quotients for the rectangular family

Two-color sites act on both colors; one-color sites act only on the
right color. The polynomial variables are the actual finitely many
retained current modes. The defining ideal is the checked mixed
coefficient ideal. No fusion-product identification is part of the
definition.
-/

namespace VOA.DeligneAudit.A2.CVRectFamily

open VOA.DeligneAudit.A2.CVRectSplit
open VOA.DeligneAudit.A2.CVRectZero
open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectShift
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectIntegrationDimension

noncomputable section

abbrev Ring (M N : ℕ) := MvPolynomial (Fin M ⊕ Fin N) ℂ

def ideal (M N : ℕ) (two one : List ℕ) : Ideal (Ring M N) :=
  coefficientIdeal (reverseLeft M N) (reverseRight M N) (familyOrder two one)

/-- The actual finite polynomial quotient at specified color lengths. -/
abbrev Model (M N : ℕ) (two one : List ℕ) := Ring M N ⧸ ideal M N two one

/-- The color lengths determined by the active sites. -/
abbrev Family (two one : List ℕ) := Model two.length (two.length + one.length) two one

theorem familyOrder_active (two one : List ℕ) (K : ℕ) :
    familyOrder (K :: two) one = mixedOrder two one K := by
  funext a b
  simp only [familyOrder, mixedOrder, siteOrder, excess, List.map_cons, List.sum_cons]
  omega

theorem familyOrder_shifted (two one : List ℕ) (K : ℕ) :
    familyOrder two (K :: one) = shiftedOrder two one K := by
  funext a b
  simp only [familyOrder, shiftedOrder, excess, List.map_cons, List.sum_cons]
  omega

theorem ideal_empty : ideal 0 0 [] [] = ⊥ := by
  unfold ideal coefficientIdeal
  have hs : {P : Ring 0 0 | ∃ a b j, j < familyOrder [] [] a b ∧
      P = PowerSeries.coeff j (reverseLeft 0 0 ^ a * reverseRight 0 0 ^ b)} = ∅ := by
    ext P
    simp [familyOrder, excess]
  rw [hs, Ideal.span_empty]

/-- The no-site polynomial quotient is exactly the scalar field. -/
def emptyEquiv : Family [] [] ≃ₐ[ℂ] ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ ideal_empty).trans
    ((AlgEquiv.quotientBot ℂ (Ring 0 0)).trans
      (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0 ⊕ Fin 0)))

theorem empty_finiteDimensional : FiniteDimensional ℂ (Family [] []) :=
  emptyEquiv.toLinearEquiv.symm.finiteDimensional

theorem empty_finrank : Module.finrank ℂ (Family [] []) = 1 := by
  simpa only [Module.finrank_self] using emptyEquiv.toLinearEquiv.finrank_eq

/-- The canonical finite-variable split is an actual equivalence for
the selected active site's coefficient ideal. -/
def activeSplitEquiv (two one : List ℕ) (K N : ℕ) :
    Model (two.length + 1) N (K :: two) one ≃ₗ[ℂ]
      (Polynomial (Ring two.length N) ⧸
        (coefficientIdeal (chosenCurrent two.length (reverseLeft two.length N))
          (constantCurrent (reverseRight two.length N))
          (mixedOrder two one K)).restrictScalars ℂ) := by
  unfold Model ideal
  rw [familyOrder_active]
  exact splitCoefficientQuotientLinearEquiv two.length N (mixedOrder two one K)

/-- The checked shift/integration maps give the actual dimension step
for finite canonical current variables. -/
theorem active_dimension_step (two one : List ℕ) (K N : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ two, k ≤ K)
    [FiniteDimensional ℂ (Model two.length N two (K :: one))]
    [FiniteDimensional ℂ (Model (two.length + 1) N ((K - 1) :: two) one)] :
    FiniteDimensional ℂ (Model (two.length + 1) N (K :: two) one) ∧
      Module.finrank ℂ (Model (two.length + 1) N (K :: two) one) ≤
        Module.finrank ℂ (Model (two.length + 1) N ((K - 1) :: two) one) +
        Module.finrank ℂ (Model two.length N two (K :: one)) := by
  let f := reverseLeft two.length N
  let g := reverseRight two.length N
  haveI : FiniteDimensional ℂ
      (Ring two.length N ⧸ (coefficientIdeal f g (shiftedOrder two one K)).restrictScalars ℂ) := by
    have hf := (inferInstance : FiniteDimensional ℂ (Model two.length N two (K :: one)))
    unfold Model ideal at hf
    rw [familyOrder_shifted] at hf
    exact hf
  haveI : FiniteDimensional ℂ (Polynomial (Ring two.length N) ⧸
      (coefficientIdeal (chosenCurrent two.length f) (constantCurrent g)
        (mixedOrder two one (K - 1))).restrictScalars ℂ) :=
    (activeSplitEquiv two one (K - 1) N).finiteDimensional
  have hs := polynomial_dimension_step f g two one K hK hmax
  haveI := hs.1
  refine ⟨(activeSplitEquiv two one K N).symm.finiteDimensional, ?_⟩
  have hb := hs.2
  rw [← (activeSplitEquiv two one K N).finrank_eq,
    ← (activeSplitEquiv two one (K - 1) N).finrank_eq] at hb
  have he : Module.finrank ℂ
      (Ring two.length N ⧸ (coefficientIdeal f g (shiftedOrder two one K)).restrictScalars ℂ) =
      Module.finrank ℂ (Model two.length N two (K :: one)) := by
    unfold Model ideal
    rw [familyOrder_shifted]
    rfl
  rw [he] at hb
  exact hb

/-- The finite color lengths of the two actual recursive families match
the explicit canonical-variable dimension step. -/
theorem active_family_dimension_step (two one : List ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ two, k ≤ K)
    [FiniteDimensional ℂ (Family two (K :: one))]
    [FiniteDimensional ℂ (Family ((K - 1) :: two) one)] :
    FiniteDimensional ℂ (Family (K :: two) one) ∧
      Module.finrank ℂ (Family (K :: two) one) ≤
        Module.finrank ℂ (Family ((K - 1) :: two) one) +
        Module.finrank ℂ (Family two (K :: one)) := by
  have hN : two.length + 1 + one.length = two.length + (one.length + 1) := by omega
  haveI : FiniteDimensional ℂ
      (Model (two.length + 1) (two.length + (one.length + 1)) ((K - 1) :: two) one) := by
    have hl := (inferInstance : FiniteDimensional ℂ (Family ((K - 1) :: two) one))
    change FiniteDimensional ℂ
      (Model (two.length + 1) (two.length + 1 + one.length) ((K - 1) :: two) one) at hl
    rw [hN] at hl
    exact hl
  have hs := active_dimension_step two one K (two.length + (one.length + 1)) hK hmax
  constructor
  · change FiniteDimensional ℂ
      (Model (two.length + 1) (two.length + 1 + one.length) (K :: two) one)
    rw [hN]
    exact hs.1
  · change Module.finrank ℂ
        (Model (two.length + 1) (two.length + 1 + one.length) (K :: two) one) ≤
      Module.finrank ℂ
        (Model (two.length + 1) (two.length + 1 + one.length) ((K - 1) :: two) one) +
      Module.finrank ℂ (Model two.length (two.length + (one.length + 1)) two (K :: one))
    rw [hN]
    exact hs.2

end

end VOA.DeligneAudit.A2.CVRectFamily

#print axioms VOA.DeligneAudit.A2.CVRectFamily.emptyEquiv
#print axioms VOA.DeligneAudit.A2.CVRectFamily.empty_finrank
#print axioms VOA.DeligneAudit.A2.CVRectFamily.active_dimension_step
#print axioms VOA.DeligneAudit.A2.CVRectFamily.active_family_dimension_step
