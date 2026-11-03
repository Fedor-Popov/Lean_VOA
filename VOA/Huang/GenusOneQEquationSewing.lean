import VOA.Huang.GenusTwoPointRadialSystem
import VOA.Huang.GenusTwoPointModifiedTrace
import VOA.Huang.GenusTwoPointLattice
import VOA.Huang.GenusOneQEquationRegular

/-!
# Sewing consequences of a uniformly controlled coupled Euler system

These theorems close the analytic implication from `RadialEulerControl` to the
existing joint sewing predicates. The coupled system is an explicit hypothesis;
it has not been constructed for general traces from the geometric Ward laws.
The original `TraceDescent` and `QOrbitCompatibility` obligations are unchanged.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Joint product sewing and outer q-summability from one coupled coefficient
system with the uniform bounds retained explicitly. -/
theorem productSummable_of_radialEuler
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : RadialEulerControl (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂))
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (τ : UpperHalfPlane)
    (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductSewingSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ ∧
      ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ := by
  have hs := productSewingSummable_of_modeGrowth Y₁ Y₂ w₁ w₂ α₁ α₂
    (productModeGrowth_of_radialEuler Y₁ Y₂ w₁ w₂ α₁ α₂ h) hz₂ hz τ hq
  exact ⟨hs, productQSummable_of_sewing Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ hs⟩

/-- A positive local iterate sewing radius from the same precise analytic
criterion. No assertion of the criterion for general VOA data is made. -/
theorem exists_iterateSewingRadius_of_radialEuler
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : RadialEulerControl (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (z₀ z₂ : ℂ), z₀ ≠ 0 → z₂ ≠ 0 →
      ‖z₀ / z₂‖ < δ → IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ :=
  exists_iterateSewingRadius_of_modeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂
    (iterateModeGrowth_of_radialEuler Y₃ Y₄ w₁ w₂ α₁ α₂ h) τ

end VOA.Huang.GenusTwoPoint
