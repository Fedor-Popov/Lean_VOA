import VOA.DeligneAudit.DeligneFusionCVRectAdjointRecursion

/-! # A generic exact-coordinate polynomial quotient dimension assembly -/

namespace VOA.DeligneAudit.A2.CVRectAdjointModelDimension

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive
open VOA.DeligneAudit.A2.CVRectAdjointRecursion

noncomputable section

theorem model_dimension_step (L N R : ℕ) (μ τ σ : ℕ → ℕ → ℕ → ℕ)
    (hshift : Ideal.map Polynomial.C
      (coefficientIdeal3 (starX L N R) (starY L N R) (starZ L N R) σ) ≤
      coefficientIdeal3 (chosenCurrent L (starX L N R))
        (constantCurrent (starY L N R)) (constantCurrent (starZ L N R)) μ)
    (hprimitive :
      (coefficientIdeal3 (chosenCurrent L (starX L N R))
        (constantCurrent (starY L N R)) (constantCurrent (starZ L N R)) τ).restrictScalars ℂ ≤
      ((coefficientIdeal3 (chosenCurrent L (starX L N R))
        (constantCurrent (starY L N R)) (constantCurrent (starZ L N R)) μ).restrictScalars ℂ ⊔
          CVRectIntegrationIdeal.constants).comap primitive)
    [FiniteDimensional ℂ (Model L N R σ)]
    [FiniteDimensional ℂ (Model (L + 1) N R τ)] :
    FiniteDimensional ℂ (Model (L + 1) N R μ) ∧
      Module.finrank ℂ (Model (L + 1) N R μ) ≤
        Module.finrank ℂ (Model (L + 1) N R τ) + Module.finrank ℂ (Model L N R σ) := by
  let f := starX L N R
  let g := starY L N R
  let h := starZ L N R
  haveI : FiniteDimensional ℂ (StarRing L N R ⧸
      (coefficientIdeal3 f g h σ).restrictScalars ℂ) :=
    (inferInstance : FiniteDimensional ℂ (Model L N R σ))
  haveI : FiniteDimensional ℂ (Polynomial (StarRing L N R) ⧸
      (coefficientIdeal3 (chosenCurrent L f) (constantCurrent g) (constantCurrent h)
        τ).restrictScalars ℂ) := (modelSplitEquiv L N R τ).finiteDimensional
  have hs := CVRectAdjointDimension.polynomial_dimension_step f g h μ τ σ L hshift hprimitive
  haveI := hs.1
  refine ⟨(modelSplitEquiv L N R μ).symm.finiteDimensional, ?_⟩
  have hb := hs.2
  rw [← (modelSplitEquiv L N R μ).finrank_eq, ← (modelSplitEquiv L N R τ).finrank_eq] at hb
  exact hb

end
end VOA.DeligneAudit.A2.CVRectAdjointModelDimension
