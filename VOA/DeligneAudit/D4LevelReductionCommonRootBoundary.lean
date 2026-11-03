import VOA.DeligneAudit.D4LevelReductionCommonRootTransport

/-! Common-root characteristic relations under the four site-boundary maps. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open Polynomial
open VOA.DeligneAudit.SL4T

/-- The common-root ideal for the adjoint and complementary alphabets. -/
def grassmannianCommonRootIdeal (M A a : ℕ) : Ideal (S M A a)[X] :=
  commonRootIdeal (rightP M A a) (leftPbar M A a)

/-- Complete coefficients express the complementary characteristic in descending order. -/
theorem complementCharacteristic_descending (M A a : ℕ) :
    leftPbar M A a = descendingPoly (leftH M A a) (M - A) := by
  rw [leftPbar_eq_sum, descendingPoly_eq_sum]

/-- Boundary projection removes a complementary root precisely at a missing left site. -/
theorem complementCharacteristic_boundary (M A a : ℕ) (cutL cutR : Bool)
    (hA : A ≤ M) (ha : a ≤ M)
    (hL : BoundaryAllowed M A cutL) (hR : BoundaryAllowed M a cutR) :
    (leftPbar M A a).map (boundaryProjection M A a cutL cutR hA ha hL hR).toRingHom =
      if cutL then leftPbar (M - 1) (boundaryIndex A cutL) (boundaryIndex a cutR)
      else X * leftPbar (M - 1) (boundaryIndex A cutL) (boundaryIndex a cutR) := by
  rw [complementCharacteristic_descending, descendingPoly_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, boundaryProjection_leftH]
  cases cutL with
  | true =>
      have hpos : 0 < A := hL
      simp only [if_true, boundaryIndex, complementCharacteristic_descending]
      congr 1
      omega
  | false =>
      have hlt : A < M := hL
      simp only [Bool.false_eq_true, if_false, boundaryIndex,
        complementCharacteristic_descending]
      have hs : M - A = (M - 1 - A) + 1 := by omega
      have hz : leftH (M - 1) A (boundaryIndex a cutR) (M - 1 - A + 1) = 0 := by
        unfold leftH
        rw [hClass_eq_zero _ _ _ (by omega), map_zero]
      have he := SL4T.descendingPoly_step
        (leftH (M - 1) A (boundaryIndex a cutR)) (M - 1 - A)
      rw [hz, map_zero, add_zero] at he
      simpa only [hs, Bool.false_eq_true, if_false] using he

/-- A divided complementary characteristic projects to the smaller complement alphabet. -/
theorem complementCharacteristic_boundary_division (M A a : ℕ) (cutR : Bool)
    (hA : A < M) (ha : a ≤ M) (hR : BoundaryAllowed M a cutR) :
    (leftPbar M A a).divX.map
        (boundaryProjection M A a false cutR hA.le ha hA hR).toRingHom =
      leftPbar (M - 1) A (boundaryIndex a cutR) := by
  have h := complementCharacteristic_boundary M A a false cutR hA.le ha hA hR
  ext n
  have hc := congrArg (fun P => P.coeff (n + 1)) h
  change ((leftPbar M A a).map _).coeff (n + 1) =
    (X * leftPbar (M - 1) A (boundaryIndex a cutR)).coeff (n + 1) at hc
  rw [coeff_map, coeff_X_mul] at hc
  simpa only [coeff_map, coeff_divX] using hc

/-- The empty-site Thom multiplier preserves the divided complement relation. -/
theorem commonRoot_emptySite_relation (M A a : ℕ) (hM : 0 < M) (hA : A ≤ M) :
    Polynomial.C (leftE M A a A * rightE M A a a) * (leftPbar M A a).divX ∈
      grassmannianCommonRootIdeal M A a := by
  have hz : leftE M A a A * (leftPbar M A a).coeff 0 = 0 := by
    rw [leftPbar_constant]
    exact left_boundary_product M A a hM hA
  have h := commonRoot_unusedSite (rightP M A a) (leftPbar M A a)
    (leftE M A a A) hz
  rw [rightP_constant] at h
  apply ((grassmannianCommonRootIdeal M A a).smul_mem_iff_of_isUnit
    (isUnit_neg_one.pow a)).mp
  change (-1 : (S M A a)[X]) ^ a *
    (Polynomial.C (leftE M A a A * rightE M A a a) * (leftPbar M A a).divX) ∈ _
  convert h using 1
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- A site outside the left alphabet shifts both common-root relations by one. -/
theorem commonRoot_adjointSite_relations (M A a : ℕ) (hM : 0 < M) (hA : A ≤ M) :
    Polynomial.C (leftE M A a A) * X * (rightP M A a).divX ∈
        (thomI1 M A a).map Polynomial.C ⊔ grassmannianCommonRootIdeal M A a ∧
      Polynomial.C (leftE M A a A) * X * (leftPbar M A a).divX ∈
        (thomI1 M A a).map Polynomial.C ⊔ grassmannianCommonRootIdeal M A a := by
  apply commonRoot_sharedSite
  · rw [rightP_constant]
    have hmem : leftE M A a A * rightE M A a a ∈ thomI1 M A a :=
      Ideal.subset_span (Set.mem_singleton _)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (thomI1 M A a).mul_mem_left ((-1) ^ a) hmem
  · rw [leftPbar_constant, left_boundary_product M A a hM hA]
    exact Ideal.zero_mem _

/-- A site in both original alphabets contributes no common-root degree. -/
theorem commonRoot_intersectionSite_relation (M A a : ℕ)
    (hM : 0 < M) (hA : A ≤ M) (ha : a ≤ M) :
    Polynomial.C (rightH M A a (M - a)) * (rightP M A a).divX ∈
      (thomI2 M A a).map Polynomial.C ⊔ grassmannianCommonRootIdeal M A a := by
  have hp : rightP M A a * rightPbar M A a = X ^ ((M - 1) + 1) := by
    rw [Nat.sub_add_cancel (show 1 ≤ M by omega)]
    exact right_characteristic_product M A a ha
  have hg : leftP M A a * leftPbar M A a = X ^ ((M - 1) + 1) := by
    rw [Nat.sub_add_cancel (show 1 ≤ M by omega)]
    exact left_characteristic_product M A a hA
  have hc : (leftP M A a).coeff 0 ∈ thomI2 M A a := by
    rw [leftP_constant]
    exact (thomI2 M A a).mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _))
  simpa only [rightPbar_constant] using commonRoot_containedSite
    (rightP M A a) (rightPbar M A a) (leftP M A a) (leftPbar M A a)
    (M - 1) (thomI2 M A a) hp hg hc

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.complementCharacteristic_descending
#print axioms VOA.DeligneAudit.D4LevelReduction.complementCharacteristic_boundary
#print axioms VOA.DeligneAudit.D4LevelReduction.complementCharacteristic_boundary_division
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRoot_emptySite_relation
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRoot_adjointSite_relations
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRoot_intersectionSite_relation
