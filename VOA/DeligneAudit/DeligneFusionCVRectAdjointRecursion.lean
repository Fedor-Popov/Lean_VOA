import VOA.DeligneAudit.DeligneFusionCVRectAdjointDimension
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFamily
import VOA.DeligneAudit.DeligneFusionCVRectStarSplit

/-! # The canonical finite-family form of the actual adjoint split -/

namespace VOA.DeligneAudit.A2.CVRectAdjointRecursion

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

def modelSplitEquiv (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Model (L + 1) N R μ ≃ₗ[ℂ]
      (Polynomial (StarRing L N R) ⧸
        (coefficientIdeal3 (chosenCurrent L (starX L N R))
          (constantCurrent (starY L N R)) (constantCurrent (starZ L N R))
          μ).restrictScalars ℂ) := by
  unfold Model ideal
  exact CVRectStarSplit.splitCoefficientQuotientLinearEquiv L N R μ

/-- The actual adjoint polynomial family is bounded by its three- and
five-monomial shape branches. This step assumes only finiteness of the
two smaller actual quotient families. -/
theorem special_family_dimension_step (left right center : List ℕ)
    (hleft : ∀ k ∈ left, k ≤ 1)
    [FiniteDimensional ℂ (ThreeFamily left right center)]
    [FiniteDimensional ℂ (FiveFamily left right center)] :
    FiniteDimensional ℂ (AdjointFamily left right center) ∧
      Module.finrank ℂ (AdjointFamily left right center) ≤
        Module.finrank ℂ (ThreeFamily left right center) +
        Module.finrank ℂ (FiveFamily left right center) := by
  let N := left.length + right.length + center.length + 1
  let R := right.length + 1
  let f := starX left.length N R
  let g := starY left.length N R
  let h := starZ left.length N R
  haveI : FiniteDimensional ℂ (StarRing left.length N R ⧸
      (coefficientIdeal3 f g h (fiveSiteOrder left right center)).restrictScalars ℂ) :=
    (inferInstance : FiniteDimensional ℂ (FiveFamily left right center))
  haveI : FiniteDimensional ℂ (Polynomial (StarRing left.length N R) ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (threeSiteOrder left right center)).restrictScalars ℂ) :=
    (modelSplitEquiv left.length N R (threeSiteOrder left right center)).finiteDimensional
  have hs := CVRectAdjointDimension.adjoint_special_dimension_step f g h
    left right center hleft
  haveI := hs.1
  refine ⟨(modelSplitEquiv left.length N R (adjointOrder left right center)).symm.finiteDimensional,
    ?_⟩
  have hb := hs.2
  rw [← (modelSplitEquiv left.length N R (adjointOrder left right center)).finrank_eq,
    ← (modelSplitEquiv left.length N R (threeSiteOrder left right center)).finrank_eq] at hb
  exact hb

end
end VOA.DeligneAudit.A2.CVRectAdjointRecursion

#print axioms VOA.DeligneAudit.A2.CVRectAdjointRecursion.special_family_dimension_step
