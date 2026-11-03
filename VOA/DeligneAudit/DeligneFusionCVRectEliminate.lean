import VOA.DeligneAudit.DeligneFusionCVRectEliminateVariables
import VOA.DeligneAudit.DeligneFusionCVRectFamily

/-!
# Actual zero-capacity quotient maps in the upper-bound direction

The smaller variables give a section into the larger zero-site quotient.
The highest variables vanish in that quotient, so the section is surjective.
This constructs the needed smaller-to-larger quotient maps without assuming
any projection kernel description or a desired dimension bound.
-/

namespace VOA.DeligneAudit.A2.CVRectEliminate

open VOA.DeligneAudit.A2.CVRectSplit
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectZero

noncomputable section

section SectionQuotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Exact image-ideal equality and a quotient section factorization give
an actual map in the reverse, upper-bound direction. -/
def quotientSectionMap (ι : A →ₐ[ℂ] B) (π : B →ₐ[ℂ] A)
    (I : Ideal A) (J : Ideal B) (hπ : Function.Surjective π)
    (hmap : Ideal.map π.toRingHom J = I)
    (hfactor : ((Ideal.Quotient.mkₐ ℂ J).comp ι).comp π = Ideal.Quotient.mkₐ ℂ J) :
    (A ⧸ I) →ₐ[ℂ] B ⧸ J :=
  Ideal.quotientMapₐ J ι (by
    intro p hp
    rw [← hmap] at hp
    obtain ⟨b, hb, hbp⟩ := (Ideal.mem_map_iff_of_surjective π.toRingHom hπ).mp hp
    change ι p ∈ J
    rw [← hbp]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := DFunLike.congr_fun hfactor b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at he
    change Ideal.Quotient.mk J (ι (π b)) = 0
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb)

theorem quotientSectionMap_surjective (ι : A →ₐ[ℂ] B) (π : B →ₐ[ℂ] A)
    (I : Ideal A) (J : Ideal B) (hπ : Function.Surjective π)
    (hmap : Ideal.map π.toRingHom J = I)
    (hfactor : ((Ideal.Quotient.mkₐ ℂ J).comp ι).comp π = Ideal.Quotient.mkₐ ℂ J) :
    Function.Surjective (quotientSectionMap ι π I J hπ hmap hfactor) := by
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨Ideal.Quotient.mk I (π b), ?_⟩
  change Ideal.Quotient.mk J (ι (π b)) = Ideal.Quotient.mk J b
  exact DFunLike.congr_fun hfactor b

end SectionQuotient

/-- The zero-capacity active ideal kills the highest retained left variable. -/
theorem last_left_mem_active (M N : ℕ) (two one : List ℕ) :
    MvPolynomial.X (Sum.inl (Fin.last M)) ∈
      coefficientIdeal (reverseLeft (M + 1) (N + 1)) (reverseRight (M + 1) (N + 1))
        (familyOrder (0 :: two) one) := by
  have h : PowerSeries.coeff 0
      (reverseLeft (M + 1) (N + 1) ^ 1 * reverseRight (M + 1) (N + 1) ^ 0) ∈
      coefficientIdeal (reverseLeft (M + 1) (N + 1)) (reverseRight (M + 1) (N + 1))
        (familyOrder (0 :: two) one) := by
    exact Ideal.subset_span ⟨1, 0, 0, by rw [familyOrder_active_zero]; omega, rfl⟩
  simpa only [pow_one, pow_zero, mul_one, coeff_zero_reverseLeft] using h

/-- The zero-capacity active ideal kills the highest retained right variable. -/
theorem last_right_mem_active (M N : ℕ) (two one : List ℕ) :
    MvPolynomial.X (Sum.inr (Fin.last N)) ∈
      coefficientIdeal (reverseLeft (M + 1) (N + 1)) (reverseRight (M + 1) (N + 1))
        (familyOrder (0 :: two) one) := by
  have h : PowerSeries.coeff 0
      (reverseLeft (M + 1) (N + 1) ^ 0 * reverseRight (M + 1) (N + 1) ^ 1) ∈
      coefficientIdeal (reverseLeft (M + 1) (N + 1)) (reverseRight (M + 1) (N + 1))
        (familyOrder (0 :: two) one) := by
    exact Ideal.subset_span ⟨0, 1, 0, by rw [familyOrder_active_zero]; omega, rfl⟩
  simpa only [pow_one, pow_zero, one_mul, coeff_zero_reverseRight] using h

/-- The zero-capacity inactive ideal kills its highest retained right variable. -/
theorem last_right_mem_inactive (M N : ℕ) (two one : List ℕ) :
    MvPolynomial.X (Sum.inr (Fin.last N)) ∈
      coefficientIdeal (reverseLeft M (N + 1)) (reverseRight M (N + 1))
        (familyOrder two (0 :: one)) := by
  have h : PowerSeries.coeff 0 (reverseLeft M (N + 1) ^ 0 * reverseRight M (N + 1) ^ 1) ∈
      coefficientIdeal (reverseLeft M (N + 1)) (reverseRight M (N + 1))
        (familyOrder two (0 :: one)) := by
    exact Ideal.subset_span ⟨0, 1, 0, by rw [familyOrder_inactive_zero]; omega, rfl⟩
  simpa only [pow_one, pow_zero, one_mul, coeff_zero_reverseRight] using h

/-- In the larger quotient, projecting and re-including changes no variable. -/
theorem sectionBoth_project_quotient (M N : ℕ) (J : Ideal (VarsRing (M + 1) (N + 1)))
    (hleft : MvPolynomial.X (Sum.inl (Fin.last M)) ∈ J)
    (hright : MvPolynomial.X (Sum.inr (Fin.last N)) ∈ J) :
    ((Ideal.Quotient.mkₐ ℂ J).comp (sectionBoth M N)).comp (projectBoth M N) =
      Ideal.Quotient.mkₐ ℂ J := by
  ext x
  rcases x with i | i
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [AlgHom.comp_apply, projectBoth_X_left_last, map_zero,
        Ideal.Quotient.mkₐ_eq_mk] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hleft).symm
    · simp
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [AlgHom.comp_apply, projectBoth_X_right_last, map_zero,
        Ideal.Quotient.mkₐ_eq_mk] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hright).symm
    · simp

theorem sectionRight_project_quotient (M N : ℕ) (J : Ideal (VarsRing M (N + 1)))
    (hright : MvPolynomial.X (Sum.inr (Fin.last N)) ∈ J) :
    ((Ideal.Quotient.mkₐ ℂ J).comp (sectionRight M N)).comp (projectRight M N) =
      Ideal.Quotient.mkₐ ℂ J := by
  ext x
  rcases x with i | i
  · simp
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [AlgHom.comp_apply, projectRight_X_right_last, map_zero,
        Ideal.Quotient.mkₐ_eq_mk] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hright).symm
    · simp

/-- The actual smaller-model map onto a model with an added zero two-color site. -/
def activeZeroModelMap (M N : ℕ) (two one : List ℕ) :
    CVRectFamily.Model M N two one →ₐ[ℂ]
      CVRectFamily.Model (M + 1) (N + 1) (0 :: two) one :=
  quotientSectionMap (sectionBoth M N) (projectBoth M N) _ _
    (projectBoth_surjective M N) (projectBoth_ideal M N two one)
    (sectionBoth_project_quotient M N _
      (last_left_mem_active M N two one) (last_right_mem_active M N two one))

theorem activeZeroModelMap_surjective (M N : ℕ) (two one : List ℕ) :
    Function.Surjective (activeZeroModelMap M N two one) :=
  quotientSectionMap_surjective _ _ _ _ _ _ _

/-- The actual smaller-model map onto a model with an added zero one-color site. -/
def inactiveZeroModelMap (M N : ℕ) (two one : List ℕ) :
    CVRectFamily.Model M N two one →ₐ[ℂ]
      CVRectFamily.Model M (N + 1) two (0 :: one) :=
  quotientSectionMap (sectionRight M N) (projectRight M N) _ _
    (projectRight_surjective M N) (projectRight_ideal M N two one)
    (sectionRight_project_quotient M N _ (last_right_mem_inactive M N two one))

theorem inactiveZeroModelMap_surjective (M N : ℕ) (two one : List ℕ) :
    Function.Surjective (inactiveZeroModelMap M N two one) :=
  quotientSectionMap_surjective _ _ _ _ _ _ _

/-- The arithmetic color-length transport for an added two-color site. -/
def activeZeroLengthEquiv (two one : List ℕ) :
    CVRectFamily.Model (two.length + 1) (two.length + one.length + 1) (0 :: two) one
      ≃ₗ[ℂ] CVRectFamily.Family (0 :: two) one := by
  change CVRectFamily.Model (two.length + 1) (two.length + one.length + 1) (0 :: two) one
      ≃ₗ[ℂ] CVRectFamily.Model (two.length + 1) (two.length + 1 + one.length) (0 :: two) one
  rw [show two.length + 1 + one.length = two.length + one.length + 1 by omega]

/-- Zero-site removal in the actual capacity-determined family. -/
def activeZeroMap (two one : List ℕ) :
    CVRectFamily.Family two one →ₗ[ℂ] CVRectFamily.Family (0 :: two) one :=
  (activeZeroLengthEquiv two one).toLinearMap.comp
    (activeZeroModelMap two.length (two.length + one.length) two one).toLinearMap

theorem activeZeroMap_surjective (two one : List ℕ) :
    Function.Surjective (activeZeroMap two one) :=
  (activeZeroLengthEquiv two one).surjective.comp
    (activeZeroModelMap_surjective two.length (two.length + one.length) two one)

/-- The arithmetic color-length transport for an added one-color site. -/
def inactiveZeroLengthEquiv (two one : List ℕ) :
    CVRectFamily.Model two.length (two.length + one.length + 1) two (0 :: one)
      ≃ₗ[ℂ] CVRectFamily.Family two (0 :: one) := by
  change CVRectFamily.Model two.length (two.length + one.length + 1) two (0 :: one)
      ≃ₗ[ℂ] CVRectFamily.Model two.length (two.length + (one.length + 1)) two (0 :: one)
  rw [← Nat.add_assoc]

/-- Zero one-color site removal in the actual capacity-determined family. -/
def inactiveZeroMap (two one : List ℕ) :
    CVRectFamily.Family two one →ₗ[ℂ] CVRectFamily.Family two (0 :: one) :=
  (inactiveZeroLengthEquiv two one).toLinearMap.comp
    (inactiveZeroModelMap two.length (two.length + one.length) two one).toLinearMap

theorem inactiveZeroMap_surjective (two one : List ℕ) :
    Function.Surjective (inactiveZeroMap two one) :=
  (inactiveZeroLengthEquiv two one).surjective.comp
    (inactiveZeroModelMap_surjective two.length (two.length + one.length) two one)

/-- An added zero two-color site cannot increase the actual quotient dimension. -/
theorem active_zero_bound (two one : List ℕ)
    [FiniteDimensional ℂ (CVRectFamily.Family two one)] :
    FiniteDimensional ℂ (CVRectFamily.Family (0 :: two) one) ∧
      Module.finrank ℂ (CVRectFamily.Family (0 :: two) one) ≤
        Module.finrank ℂ (CVRectFamily.Family two one) := by
  have hs := activeZeroMap_surjective two one
  exact ⟨Module.Finite.of_surjective (activeZeroMap two one) hs,
    LinearMap.finrank_le_finrank_of_surjective hs⟩

/-- An added zero one-color site cannot increase the actual quotient dimension. -/
theorem inactive_zero_bound (two one : List ℕ)
    [FiniteDimensional ℂ (CVRectFamily.Family two one)] :
    FiniteDimensional ℂ (CVRectFamily.Family two (0 :: one)) ∧
      Module.finrank ℂ (CVRectFamily.Family two (0 :: one)) ≤
        Module.finrank ℂ (CVRectFamily.Family two one) := by
  have hs := inactiveZeroMap_surjective two one
  exact ⟨Module.Finite.of_surjective (inactiveZeroMap two one) hs,
    LinearMap.finrank_le_finrank_of_surjective hs⟩

end
end VOA.DeligneAudit.A2.CVRectEliminate

#print axioms VOA.DeligneAudit.A2.CVRectEliminate.activeZeroModelMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.inactiveZeroModelMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.activeZeroMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.inactiveZeroMap_surjective

#print axioms VOA.DeligneAudit.A2.CVRectEliminate.active_zero_bound
#print axioms VOA.DeligneAudit.A2.CVRectEliminate.inactive_zero_bound
