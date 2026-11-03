import VOA.Modules.LogTensorPzPointScaling
import VOA.Modules.LogTensorPrecompose
import VOA.Modules.LogTensorTwist

/-! Actual chosen-branch evaluation is natural in both source modules, including
their genuine Jordan exponentials and every logarithmic degree. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Pz
open VOA.LogTensor VOA.LogTensor.Contra
universe u
variable {V M₁ M₂ M₃ X₁ X₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (Q₁ : LogVModule W X₁) (Q₂ : LogVModule W X₂)
  (f : Q₁.toWeakModule.Hom N₁.toWeakModule) (g : Q₂.toWeakModule.Hom N₂.toWeakModule)
  (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- Evaluation at one commutes with actual source maps. -/
theorem evaluateOne_precompose :
    evaluateOne Q₁ Q₂ N₃ (precompose f g Y)=
      ((evaluateOne N₁ N₂ N₃ Y).comp f.toLinearMap).compl₂ g.toLinearMap := by
  apply bilinear_ext_homogeneous Q₁ Q₂
  intro a b x y hx hy
  funext c
  apply Subtype.ext
  change (evaluateOne Q₁ Q₂ N₃ (precompose f g Y) x y c : M₃)=
    (evaluateOne N₁ N₂ N₃ Y (f.toLinearMap x) (g.toLinearMap y) c : M₃)
  rw [evaluateOne_homogeneous Q₁ Q₂ N₃ (precompose f g Y) hx hy c,
    evaluateOne_homogeneous N₁ N₂ N₃ Y (hom_mem_weight Q₁ N₁ f hx)
      (hom_mem_weight Q₂ N₂ g hy) c,precompose_apply]

/-- Every chosen-branch point evaluation commutes with actual source maps. -/
theorem evaluatePoint_precompose (ell : ℂ) (x : X₁) (y : X₂) :
    evaluatePoint Q₁ Q₂ N₃ (precompose f g Y) ell x y=
      evaluatePoint N₁ N₂ N₃ Y ell (f.toLinearMap x) (g.toLinearMap y) := by
  rw [evaluatePoint_L0exp Q₁ Q₂ N₃ (precompose f g Y) ell,
    evaluatePoint_L0exp N₁ N₂ N₃ Y ell]
  dsimp only [transportedEvaluateOne,LinearMap.mk₂_apply]
  rw [evaluateOne_precompose]
  dsimp only [LinearMap.comp_apply,LinearMap.compl₂_apply]
  rw [hom_L0exp Q₁ N₁ f,hom_L0exp Q₂ N₂ g]

/-- Literal output blocks have the same source naturality, with their genuine
finite logarithmic expansions. -/
theorem pointEvaluationBlock_precompose (ell a b c : ℂ) (x : Q₁.weight a) (y : Q₂.weight b) :
    (pointEvaluationBlock Q₁ Q₂ N₃ (precompose f g Y) ell a b c x y : M₃)=
      pointEvaluationBlock N₁ N₂ N₃ Y ell a b c
        ⟨f.toLinearMap x,hom_mem_weight Q₁ N₁ f x.2⟩
        ⟨g.toLinearMap y,hom_mem_weight Q₂ N₂ g y.2⟩ := by
  have h := congrArg (fun q : Completion N₃ => (q c : M₃))
    (evaluatePoint_precompose N₁ N₂ N₃ Q₁ Q₂ f g Y ell x y)
  dsimp only at h
  rw [evaluatePoint_eq_block Q₁ Q₂ N₃ (precompose f g Y) ell x.2 y.2 c,
    evaluatePoint_eq_block N₁ N₂ N₃ Y ell (hom_mem_weight Q₁ N₁ f x.2)
      (hom_mem_weight Q₂ N₂ g y.2) c] at h
  exact h

end VOA.LogTensor.Pz
