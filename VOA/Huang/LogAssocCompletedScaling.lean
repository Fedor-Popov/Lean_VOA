import VOA.Huang.LogAssocCompletedIterate
import VOA.Modules.LogTensorPzPointScaling

/-! Literal completed product and iterate evaluations have genuine conformal
scaling, including all Jordan parts. The intermediate conformal transports
cancel componentwise before any scalar summation. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Literal completed products scale by the actual conformal exponentials. -/
theorem completedLogProduct_shift_transport
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (ell₁ ell₂ s a β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : N₁.weight a) (y : M₂) (z : M₃) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (ell₁+s) (ell₂+s) a β f x y z=
      completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ ell₁ ell₂ a β
        (f ∘ₗ (L0exp N₄ s).toLinearMap)
        ⟨L0exp N₁ (-s) x,L0exp_mem_weight N₁ (-s) x.2⟩
        (L0exp N₂ (-s) y) (L0exp N₃ (-s) z) := by
  let q := evaluatePoint N₂ N₃ N₅ Y₂ (ell₂+s) y z
  let q' := evaluatePoint N₂ N₃ N₅ Y₂ ell₂ (L0exp N₂ (-s) y) (L0exp N₃ (-s) z)
  have hq (γ : ℂ) :
      (⟨L0exp N₅ (-s) (q γ),L0exp_mem_weight N₅ (-s) (q γ).2⟩ : N₅.weight γ)=q' γ := by
    apply Subtype.ext
    have he := congrArg (fun q : Completion N₅ => (q γ : M₅))
      (evaluatePoint_shift_transport N₂ N₃ N₅ Y₂ ell₂ s y z)
    dsimp only at he
    rw [completionL0exp_apply] at he
    change L0exp N₅ (-s) (q γ)=(q' γ : M₅)
    rw [he,L0exp_neg_cancel]
  apply tsum_congr
  intro γ
  change f (pointEvaluationBlock N₁ N₅ N₄ Y₁ (ell₁+s) a γ β x (q γ))=
    f (L0exp N₄ s (pointEvaluationBlock N₁ N₅ N₄ Y₁ ell₁ a γ β
      ⟨L0exp N₁ (-s) x,L0exp_mem_weight N₁ (-s) x.2⟩ (q' γ)))
  rw [pointEvaluationBlock_shift_transport,hq]

/-- Literal completed iterates scale by the same actual conformal exponentials. -/
theorem completedLogIterate_shift_transport
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ell₀ ell₂ s c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : N₃.weight c) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ (ell₀+s) (ell₂+s) c β f x y z=
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ell₀ ell₂ c β
        (f ∘ₗ (L0exp N₄ s).toLinearMap) (L0exp N₁ (-s) x) (L0exp N₂ (-s) y)
        ⟨L0exp N₃ (-s) z,L0exp_mem_weight N₃ (-s) z.2⟩ := by
  let q := evaluatePoint N₁ N₂ N₅ Y₄ (ell₀+s) x y
  let q' := evaluatePoint N₁ N₂ N₅ Y₄ ell₀ (L0exp N₁ (-s) x) (L0exp N₂ (-s) y)
  have hq (γ : ℂ) :
      (⟨L0exp N₅ (-s) (q γ),L0exp_mem_weight N₅ (-s) (q γ).2⟩ : N₅.weight γ)=q' γ := by
    apply Subtype.ext
    have he := congrArg (fun q : Completion N₅ => (q γ : M₅))
      (evaluatePoint_shift_transport N₁ N₂ N₅ Y₄ ell₀ s x y)
    dsimp only at he
    rw [completionL0exp_apply] at he
    change L0exp N₅ (-s) (q γ)=(q' γ : M₅)
    rw [he,L0exp_neg_cancel]
  apply tsum_congr
  intro γ
  change f (pointEvaluationBlock N₅ N₃ N₄ Y₃ (ell₂+s) γ c β (q γ) z)=
    f (L0exp N₄ s (pointEvaluationBlock N₅ N₃ N₄ Y₃ ell₂ γ c β (q' γ)
      ⟨L0exp N₃ (-s) z,L0exp_mem_weight N₃ (-s) z.2⟩))
  rw [pointEvaluationBlock_shift_transport,hq]

end VOA.Huang.LogAssocExpansion
