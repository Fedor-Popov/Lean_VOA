import VOA.Huang.LogHuangODEProductMain

/-! # Three-intertwiner coefficients and their two independent levels

The two indices are the levels in the two intermediate modules. They are
independent: homogeneity eliminates only the third mode index. In product
coordinates the corresponding power-series variables are `z₂/z₁` and `z₃/z₂`.
No convergence or regular-singular equation is asserted in this file.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid PowerSeries
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : C2Rigid.GWModule W M₀} {A₁ : C2Rigid.GWModule W M₁}
  {A₂ : C2Rigid.GWModule W M₂} {A₃ : C2Rigid.GWModule W M₃} {A₄ : C2Rigid.GWModule W M₄}
  {A₅ : C2Rigid.GWModule W M₅} {A₆ : C2Rigid.GWModule W M₆}
variable (Y₁ : IntertwiningModes M₁ M₆ M₀) (Y₂ : IntertwiningModes M₂ M₅ M₆)
  (Y₃ : IntertwiningModes M₃ M₄ M₅)

/-- The actual scalar coefficient of a product of three intertwiners. -/
def productCoeff (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) : ℂ := f (Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)))

variable {Y₁ Y₂ Y₃}
variable (hY₁ : LogHuangODEProduct.IsGradedJacobiFamily A₁ A₆ A₀ Y₁)
  (hY₂ : LogHuangODEProduct.IsGradedJacobiFamily A₂ A₅ A₆ Y₂)
  (hY₃ : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ A₅ Y₃)

include hY₁ hY₂ hY₃ in
/-- Homogeneity leaves a two-dimensional plane of potentially nonzero modes. -/
theorem product_mem_weight {α₁ α₂ α₃ α₄ : ℂ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄) (p q r : ℂ) :
    Y₁ p w₁ (Y₂ q w₂ (Y₃ r w₃ w₄)) ∈
      A₀.weight (α₁ + α₂ + α₃ + α₄ - p - q - r - 3) := by
  convert hY₁.mem_weight h₁ (hY₂.mem_weight h₂ (hY₃.mem_weight h₃ h₄ r) q) p using 1
  congr 1
  ring


end VOA.Huang.LogAssocFivePointGraded
