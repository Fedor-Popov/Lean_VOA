import VOA.Huang.LogAssocCompletedProduct
import VOA.Modules.LogTensorUnit

/-! A literal genuine module vacuum insertion collapses the completed
logarithmic product to a single actual weight, preserving the entire
finite logarithmic polynomial in the other intertwining operator. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₃ M₄ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] {W : VertexOperatorAlgebra V}

/-- The genuine vacuum module insertion is constant; every other actual
intermediate generalized weight contributes zero to the full product. -/
theorem completedLogProduct_module_vacuum
    (N₁ : LogVModule W M₁) (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (hv : W.vacuum∈(adjointModule W).toLog.weight 0)
    (ell a β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : N₁.weight a)
    {b : ℂ} {y : M₃} (hy : y∈N₃.weight b) :
    completedLogProduct N₁ (adjointModule W).toLog N₃ N₄ N₃ Y
      (logModuleIntertwiner N₃.toWeakModule) ell 0 a β f x W.vacuum y=
      f (pointEvaluationBlock N₁ N₃ N₄ Y ell a b β x ⟨y,hy⟩) := by
  classical
  let q := evaluatePoint (adjointModule W).toLog N₃ N₃
    (logModuleIntertwiner N₃.toWeakModule) 0 W.vacuum y
  have hq (γ : ℂ) : (q γ : M₃)=if γ=b then y else 0 := by
    dsimp only [q]
    rw [evaluatePoint_zero,evaluateOne_homogeneous (adjointModule W).toLog N₃ N₃
      (logModuleIntertwiner N₃.toWeakModule) hv hy γ]
    by_cases he : γ=b
    · subst γ
      simp only [zero_add,sub_self,zero_sub]
      rw [logModuleIntertwiner_vacuum,LinearMap.id_apply]
      simp
    · have hn : (0 : ℂ)+b-γ-1≠-1 := by
        intro hn
        apply he
        linear_combination -hn
      rw [vacuum_mode_zero_of_ne (logModuleIntertwiner N₃.toWeakModule).2 hn 0,
        LinearMap.zero_apply,if_neg he]
  have hqb : q b=⟨y,hy⟩ := Subtype.ext (by rw [hq,if_pos rfl])
  unfold completedLogProduct completedProductPair
  change (∑' γ : ℂ,f (pointEvaluationBlock N₁ N₃ N₄ Y ell a γ β x (q γ)))=_
  rw [tsum_eq_single b]
  · rw [hqb]
  · intro γ hγ
    have hq0 : q γ=0 := Subtype.ext (by rw [hq,if_neg hγ]; rfl)
    rw [hq0,map_zero]
    simp

end VOA.Huang.LogAssocExpansion
