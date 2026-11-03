import VOA.DeligneAudit.D4LeviKSFlagXStep
import VOA.DeligneAudit.D4LeviKSTargetProducts

/-! Exact-degree pure products span the separately symmetric target. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def ksFlagXYZCoefficient (a b c d : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  ksProductCoefficient (fun e => ksBlockCoefficient a e (ksTargetXMap a b c))
    (ksFlagYZCoefficient a b c) d

/-- Projection of a pure symmetric product retains only products whose three
    factor degrees add to the requested total degree. -/
theorem ksFlag_pure_component_mem (a b c d : ℕ) (F : PairTargetFactors a b c) :
    homogeneousComponent d (pairTargetPure a b c F) ∈ ksFlagXYZCoefficient a b c d := by
  classical
  let Fx := F.1.val
  let Fy := F.2.1.val
  let Fz := F.2.2.val
  have hx : Fx = ∑ j ∈ Finset.range (Fx.totalDegree + 1), homogeneousComponent j Fx :=
    (sum_homogeneousComponent Fx).symm
  have hy : Fy = ∑ j ∈ Finset.range (Fy.totalDegree + 1), homogeneousComponent j Fy :=
    (sum_homogeneousComponent Fy).symm
  have hz : Fz = ∑ j ∈ Finset.range (Fz.totalDegree + 1), homogeneousComponent j Fz :=
    (sum_homogeneousComponent Fz).symm
  change homogeneousComponent d
    (ksTargetXMap a b c Fx * ksTargetYMap a b c Fy * ksTargetZMap a b c Fz) ∈ _
  rw [hx, hy, hz]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.sum_mem
  intro i hi
  have hX := (homogeneousComponent_isHomogeneous i Fx).rename_isHomogeneous
    (f := (Sum.inl : Fin a → PairTarget a b c))
  have hY := (homogeneousComponent_isHomogeneous j Fy).rename_isHomogeneous
    (f := (fun y : Fin b => (Sum.inr (Sum.inl y) : PairTarget a b c)))
  have hZ := (homogeneousComponent_isHomogeneous k Fz).rename_isHomogeneous
    (f := (fun z : Fin c => (Sum.inr (Sum.inr z) : PairTarget a b c)))
  dsimp only [ksTargetXMap, ksTargetYMap, ksTargetZMap]
  rw [homogeneousComponent_of_mem ((hX.mul hY).mul hZ)]
  split_ifs with hd
  · apply Submodule.subset_span
    refine ⟨i, j + k, by omega, ksTargetXMap a b c (homogeneousComponent i Fx),
      ?_, ksTargetYMap a b c (homogeneousComponent j Fy) *
        ksTargetZMap a b c (homogeneousComponent k Fz), ?_, ?_⟩
    · exact ⟨_, ⟨ksHomogeneousComponent_symmetric a i Fx F.1.property,
        homogeneousComponent_isHomogeneous _ _⟩, rfl⟩
    · apply Submodule.subset_span
      exact ⟨j, k, rfl, _,
        ⟨_, ⟨ksHomogeneousComponent_symmetric b j Fy F.2.1.property,
          homogeneousComponent_isHomogeneous _ _⟩, rfl⟩, _,
        ⟨_, ⟨ksHomogeneousComponent_symmetric c k Fz F.2.2.property,
          homogeneousComponent_isHomogeneous _ _⟩, rfl⟩, rfl⟩
    · simp only [ksTargetXMap, ksTargetYMap, ksTargetZMap, mul_assoc]
  · exact Submodule.zero_mem _

/-- Every homogeneous target invariant is a linear combination of homogeneous
    three-block products of the same total degree. -/
theorem ksFlag_homogeneous_mem_products (a b c d : ℕ)
    (P : MvPolynomial (PairTarget a b c) ℂ)
    (hP : P ∈ pairTargetSymmetric a b c) (hd : P.IsHomogeneous d) :
    P ∈ ksFlagXYZCoefficient a b c d := by
  have hspan := pairTargetSymmetric_le_pureSpan a b c hP
  have hc : homogeneousComponent d P ∈ ksFlagXYZCoefficient a b c d := by
    clear hd hP
    induction hspan using Submodule.span_induction with
    | mem P hP =>
        obtain ⟨F, rfl⟩ := hP
        exact ksFlag_pure_component_mem a b c d F
    | zero => simp
    | add P Q hP hQ ihP ihQ =>
        simpa only [map_add] using Submodule.add_mem _ ihP ihQ
    | smul t P hP ihP =>
        simpa only [map_smul] using Submodule.smul_mem _ t ihP
  simpa only [homogeneousComponent_of_mem hd, if_pos rfl] using hc

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlag_pure_component_mem
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_homogeneous_mem_products
