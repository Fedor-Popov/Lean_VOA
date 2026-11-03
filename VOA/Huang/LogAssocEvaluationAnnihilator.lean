import VOA.Huang.LogAssocCompletedIterate

/-! Actual mode annihilation implies literal completed point annihilation.
These statements refer to genuine all-log operators and finite generalized
point blocks, without convergence witnesses or semisimple premises. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- A scalar annihilator of every actual mode annihilates every literal point block. -/
theorem pointEvaluationBlock_zero_of_modes
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (f : M₃ →ₗ[ℂ] ℂ) (hF : ∀ n k x y,f (Y.1 n k x y)=0)
    (ell a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    f (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x y)=0 := by
  unfold pointEvaluationBlock
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Submodule.coe_smul,Submodule.coe_sum,map_smul,map_sum,smul_eq_mul]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  change ell^k*f (Y.1 (a+b-c-1) k x y)=0
  rw [hF,mul_zero]

variable {M₄ M₅ : Type u} [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- An actual outer-mode annihilator annihilates the whole literal completed iterate. -/
theorem completedLogIterate_zero_of_modes
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (hF : ∀ n k ξ z,f (Y₃.1 n k ξ z)=0)
    (ell₀ ell₂ c β : ℂ) (x : M₁) (y : M₂) (z : N₃.weight c) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ell₀ ell₂ c β f x y z=0 := by
  unfold completedLogIterate completedIteratePair
  have hz (γ : ℂ) := pointEvaluationBlock_zero_of_modes N₅ N₃ N₄ Y₃ f hF ell₂ γ c β
    (evaluatePoint N₁ N₂ N₅ Y₄ ell₀ x y γ) z
  simp only [hz,tsum_zero]

end VOA.Huang.LogAssocExpansion
