import VOA.DeligneAudit.DeligneFusionCVRectStarSplit
import VOA.DeligneAudit.DeligneFusionCVRectStarFamily
import VOA.DeligneAudit.DeligneFusionCVRectStarDimension

/-! # The actual positive-capacity recursion for canonical star quotients -/

namespace VOA.DeligneAudit.A2.CVRectStarRecursion

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarFamily
open VOA.DeligneAudit.A2.CVRectStarSplit
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

def activeSplitEquiv (left right center : List ℕ) (K N R : ℕ) :
    Model (left.length + 1) N R (K :: left) right center ≃ₗ[ℂ]
      (Polynomial (StarRing left.length N R) ⧸
        (coefficientIdeal3 (chosenCurrent left.length (starX left.length N R))
          (constantCurrent (starY left.length N R)) (constantCurrent (starZ left.length N R))
          (starOrder (K :: left) right center)).restrictScalars ℂ) := by
  unfold Model ideal
  exact splitCoefficientQuotientLinearEquiv left.length N R (starOrder (K :: left) right center)

/-- The actual split and actual polynomial maps imply the source's
finiteness and rank upper bound from the two smaller quotients. -/
theorem active_dimension_step (left right center : List ℕ) (K N R : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ left, k ≤ K)
    [FiniteDimensional ℂ (Model left.length N R left right (K :: center))]
    [FiniteDimensional ℂ (Model (left.length + 1) N R ((K - 1) :: left) right center)] :
    FiniteDimensional ℂ (Model (left.length + 1) N R (K :: left) right center) ∧
      Module.finrank ℂ (Model (left.length + 1) N R (K :: left) right center) ≤
        Module.finrank ℂ (Model (left.length + 1) N R ((K - 1) :: left) right center) +
        Module.finrank ℂ (Model left.length N R left right (K :: center)) := by
  let f := starX left.length N R
  let g := starY left.length N R
  let h := starZ left.length N R
  haveI : FiniteDimensional ℂ (StarRing left.length N R ⧸
      (coefficientIdeal3 f g h (starOrder left right (K :: center))).restrictScalars ℂ) :=
    (inferInstance : FiniteDimensional ℂ (Model left.length N R left right (K :: center)))
  haveI : FiniteDimensional ℂ (Polynomial (StarRing left.length N R) ⧸
      (coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder ((K - 1) :: left) right center)).restrictScalars ℂ) :=
    (activeSplitEquiv left right center (K - 1) N R).finiteDimensional
  have hs := CVRectStarDimension.polynomial_dimension_step f g h left right center K hK hmax
  haveI := hs.1
  refine ⟨(activeSplitEquiv left right center K N R).symm.finiteDimensional, ?_⟩
  have hb := hs.2
  rw [← (activeSplitEquiv left right center K N R).finrank_eq,
    ← (activeSplitEquiv left right center (K - 1) N R).finrank_eq] at hb
  exact hb

/-- Active-site color lengths match the actual leaf recursion exactly. -/
theorem active_family_dimension_step (left right center : List ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ left, k ≤ K)
    [FiniteDimensional ℂ (Family left right (K :: center))]
    [FiniteDimensional ℂ (Family ((K - 1) :: left) right center)] :
    FiniteDimensional ℂ (Family (K :: left) right center) ∧
      Module.finrank ℂ (Family (K :: left) right center) ≤
        Module.finrank ℂ (Family ((K - 1) :: left) right center) +
        Module.finrank ℂ (Family left right (K :: center)) := by
  have hN : left.length + 1 + right.length + center.length =
      left.length + right.length + (center.length + 1) := by omega
  haveI : FiniteDimensional ℂ (Model (left.length + 1)
      (left.length + right.length + (center.length + 1)) right.length
      ((K - 1) :: left) right center) := by
    have hl := (inferInstance : FiniteDimensional ℂ (Family ((K - 1) :: left) right center))
    change FiniteDimensional ℂ (Model (left.length + 1)
      (left.length + 1 + right.length + center.length) right.length
      ((K - 1) :: left) right center) at hl
    rw [hN] at hl
    exact hl
  have hs := active_dimension_step left right center K
    (left.length + right.length + (center.length + 1)) right.length hK hmax
  constructor
  · change FiniteDimensional ℂ (Model (left.length + 1)
      (left.length + 1 + right.length + center.length) right.length (K :: left) right center)
    rw [hN]
    exact hs.1
  · change Module.finrank ℂ (Model (left.length + 1)
        (left.length + 1 + right.length + center.length) right.length (K :: left) right center) ≤
      Module.finrank ℂ (Model (left.length + 1)
        (left.length + 1 + right.length + center.length) right.length
        ((K - 1) :: left) right center) +
      Module.finrank ℂ (Model left.length
        (left.length + right.length + (center.length + 1)) right.length left right (K :: center))
    rw [hN]
    exact hs.2

end

end VOA.DeligneAudit.A2.CVRectStarRecursion

#print axioms VOA.DeligneAudit.A2.CVRectStarRecursion.active_dimension_step
#print axioms VOA.DeligneAudit.A2.CVRectStarRecursion.active_family_dimension_step
