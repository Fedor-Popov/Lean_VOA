import VOA.Huang.LogAssocTensorOuterInputs
import VOA.Huang.LogAssocTensorOuterPrecompose

/-! Genuine simultaneous source naturality of the logarithmic outer operator. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct VOA.C2Rigid VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1 VOA.LogTensor.Contra
open Module (Dual)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅




variable {P₁ P₂ : Type u} [AddCommGroup P₁] [Module ℂ P₁]
  [AddCommGroup P₂] [Module ℂ P₂]
variable (Q₁ : LogVModule W P₁) (Q₂ : LogVModule W P₂)
  (hQ₁ : FinGen Q₁.toWeakModule) (hQ₂ : FinGen Q₂.toWeakModule)
variable (f₁ : Q₁.toWeakModule.Hom N₁.toWeakModule) (f₂ : Q₂.toWeakModule.Hom N₂.toWeakModule)

variable {P₃ : Type u} [AddCommGroup P₃] [Module ℂ P₃]
variable (Q₃ : LogVModule W P₃) (hQ₃ : FinGen Q₃.toWeakModule)
  (f₃ : Q₃.toWeakModule.Hom N₃.toWeakModule)

-- Nested actual tensor definitions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Simultaneous actual source maps commute with every logarithmic outer mode. -/
theorem tensorOuterIntertwiner_precompose_all :
    tensorOuterIntertwiner hC2 Q₁ Q₂ Q₃ N₄ N₅ hQ₁ hQ₂ hQ₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁) (precompose f₂ f₃ Y₂)=
    precompose (tensorMap hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂) f₃
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) := by
  have h := tensorOuterIntertwiner_precompose_third hC2 Q₁ Q₂ N₃ N₄ N₅
    hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
    (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
    (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) Q₃ hQ₃ f₃
  rw [tensorOuterIntertwiner_precompose_inputs hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ Q₁ Q₂ hQ₁ hQ₂ f₁ f₂] at h
  exact h

end VOA.Huang.LogAssocTensorOuterModes
