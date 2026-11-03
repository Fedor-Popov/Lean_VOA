import VOA.Huang.LogAssocCompletedIterate
import VOA.Huang.LogAssocCompletedProduct
import VOA.Modules.LogTensorPzPointPostcompose

/-! Actual completed logarithmic iterates are functorial in their genuine
output module. This is a literal termwise identity of the weight sums. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ M₃ M₄ M₅ Q : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] [AddCommGroup Q] [Module ℂ Q]
  {W : VertexOperatorAlgebra V}

/-- Literal completed iterates commute with every actual target module map. -/
theorem completedLogIterate_postcompose
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (P : LogVModule W Q)
    (g : N₄.toWeakModule.Hom P.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ell₀ ell₂ c β : ℂ) (f : Q →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : N₃.weight c) :
    completedLogIterate N₁ N₂ N₃ P N₅ (postcompose g Y₃) Y₄ ell₀ ell₂ c β f x y z=
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ell₀ ell₂ c β (f ∘ₗ g.toLinearMap) x y z := by
  unfold completedLogIterate completedIteratePair
  apply tsum_congr
  intro γ
  rw [pointEvaluationBlock_postcompose]
  rfl

/-- Literal completed products commute with every actual target module map. -/
theorem completedLogProduct_postcompose
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (P : LogVModule W Q)
    (g : N₄.toWeakModule.Hom P.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (ell₁ ell₂ a β : ℂ) (f : Q →ₗ[ℂ] ℂ) (x : N₁.weight a) (y : M₂) (z : M₃) :
    completedLogProduct N₁ N₂ N₃ P N₅ (postcompose g Y₁) Y₂ ell₁ ell₂ a β f x y z=
      completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ ell₁ ell₂ a β (f ∘ₗ g.toLinearMap) x y z := by
  unfold completedLogProduct completedProductPair
  apply tsum_congr
  intro γ
  rw [pointEvaluationBlock_postcompose]
  rfl

end VOA.Huang.LogAssocExpansion
