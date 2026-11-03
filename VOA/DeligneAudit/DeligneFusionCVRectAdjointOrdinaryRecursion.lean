import VOA.DeligneAudit.DeligneFusionCVRectAdjointModelDimension

/-! # Actual ordinary-rectangle recursion with a retained adjoint site -/

namespace VOA.DeligneAudit.A2.CVRectAdjointOrdinaryRecursion

open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

theorem ordinary_adjoint_dimension_step (left right center : List ℕ) (K : ℕ)
    (hK : 2 ≤ K) (hmax : ∀ k ∈ left, k ≤ K)
    [FiniteDimensional ℂ (AdjointFamily left right (K :: center))]
    [FiniteDimensional ℂ (AdjointFamily ((K - 1) :: left) right center)] :
    FiniteDimensional ℂ (AdjointFamily (K :: left) right center) ∧
      Module.finrank ℂ (AdjointFamily (K :: left) right center) ≤
        Module.finrank ℂ (AdjointFamily ((K - 1) :: left) right center) +
        Module.finrank ℂ (AdjointFamily left right (K :: center)) := by
  let N := left.length + right.length + center.length + 2
  let R := right.length + 1
  have hN : left.length + 1 + right.length + center.length + 1 = N := by dsimp [N]; omega
  have hN' : left.length + right.length + (center.length + 1) + 1 = N := by
    dsimp [N]
    omega
  haveI : FiniteDimensional ℂ (Model (left.length + 1) N R
      (adjointOrder left right (K :: center))) := by
    have hf := (inferInstance : FiniteDimensional ℂ (AdjointFamily left right (K :: center)))
    unfold AdjointFamily at hf
    rw [List.length_cons, hN'] at hf
    exact hf
  haveI : FiniteDimensional ℂ (Model (left.length + 1 + 1) N R
      (adjointOrder ((K - 1) :: left) right center)) := by
    have hf := (inferInstance :
      FiniteDimensional ℂ (AdjointFamily ((K - 1) :: left) right center))
    unfold AdjointFamily at hf
    rw [List.length_cons, hN] at hf
    exact hf
  have hb := CVRectAdjointModelDimension.model_dimension_step (left.length + 1) N R
    (adjointOrder (K :: left) right center) (adjointOrder ((K - 1) :: left) right center)
    (adjointOrder left right (K :: center))
    (CVRectAdjointShift.adjoint_ordinary_shift _ _ _ left right center K)
    (CVRectAdjointIntegration.adjoint_ordinary_primitive _ _ _ left right center K hK hmax
      (derivative_chosenCurrent _ _) (derivative_constantCurrent _) (derivative_constantCurrent _))
  let P : ℕ → ℕ → Prop := fun n n' =>
    FiniteDimensional ℂ (Model (left.length + 1 + 1) n R (adjointOrder (K :: left) right center)) ∧
      Module.finrank ℂ (Model (left.length + 1 + 1) n R (adjointOrder (K :: left) right center)) ≤
        Module.finrank ℂ (Model (left.length + 1 + 1) n R
          (adjointOrder ((K - 1) :: left) right center)) +
        Module.finrank ℂ (Model (left.length + 1) n' R (adjointOrder left right (K :: center)))
  have he : P (left.length + 1 + right.length + center.length + 1)
      (left.length + right.length + (center.length + 1) + 1) = P N N := congrArg₂ P hN hN'
  exact he.mpr hb

end
end VOA.DeligneAudit.A2.CVRectAdjointOrdinaryRecursion

#print axioms VOA.DeligneAudit.A2.CVRectAdjointOrdinaryRecursion.ordinary_adjoint_dimension_step
