import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Modules.LogTensorTwist

/-! Literal outer modes on the actual logarithmic tensor object, obtained
from the actual collision coefficient inclusion in its tensor dual. -/
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




variable {P₄ : Type u} [AddCommGroup P₄] [Module ℂ P₄]
variable (Q₄ : LogVModule W P₄) (hQ₄ : FinGen Q₄.toWeakModule)
variable (g : N₄.toWeakModule.Hom Q₄.toWeakModule)

/-- True homogeneous support is preserved by precomposing an actual
functional with a genuine generalized-module morphism. -/
theorem supportedAt_comp_hom {β : ℂ} {f : P₄ →ₗ[ℂ] ℂ}
    (hf : SupportedAt Q₄ f β) : SupportedAt N₄ (f ∘ₗ g.toLinearMap) β := by
  intro a ha x hx
  exact hf a ha (g.toLinearMap x) (hom_mem_weight N₄ Q₄ g hx)

/-- Literal full-spectrum products commute with actual target morphisms. -/
theorem spectrum_postcompose (f : P₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b c β t : ℂ) :
    LogAssocExpansion.logProductSpectrumFun hC2 N₅ hfg₅ (postcompose g Y₁).1 Y₂.1
      f x y z a b c β t=
    LogAssocExpansion.logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
      (f ∘ₗ g.toLinearMap) x y z a b c β t := rfl

/-- The genuine collision coefficient commutes literally with actual
target postcomposition, before applying any tensor factor. -/
theorem coefficient_postcompose (f : P₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅ (postcompose g Y₁) Y₂ f z c β γ k=
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f ∘ₗ g.toLinearMap) z c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
    (postcompose g Y₁) Y₂ f z c β γ k hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ (f ∘ₗ g.toLinearMap) z c β γ k hx hy]
  rfl

set_option maxHeartbeats 1000000 in
/-- The actual outer logarithmic intertwiner is natural in the genuine
product target, including every logarithmic degree. -/
theorem tensorOuterIntertwiner_postcompose :
    tensorOuterIntertwiner hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
      (postcompose g Y₁) Y₂=
    postcompose g (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) := by
  apply logZero_injective
  funext n
  change (tensorOuterIntertwiner hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
    (postcompose g Y₁) Y₂).1 n 0=
    (postcompose g (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)).1 n 0
  rw [tensorOuterIntertwiner_zero]
  apply bilinear_ext_homogeneous (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
  intro γ c ξ z hξ hz
  rw [postcompose_apply,tensorOuterIntertwiner_zero]
  rw [← sub_eq_zero]
  apply eq_zero_of_supported_log hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
  intro β f hf
  rw [map_sub]
  change f (tensorOuterModes hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
    (postcompose g Y₁) Y₂ n ξ z)-
    (f ∘ₗ g.toLinearMap) (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n ξ z)=0
  rw [tensorOuterModes_pair hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
    (postcompose g Y₁) Y₂ n hξ hz f hf,
    tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ n hξ hz (f ∘ₗ g.toLinearMap) (supportedAt_comp_hom hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Q₄ g hf)]
  split_ifs
  · apply sub_eq_zero.mpr
    congr 2
  · exact sub_self _

/-- The actual universal factor is natural in its product target. -/
theorem tensorOuterFactor_postcompose :
    (tensorOuterFactor hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
      (postcompose g Y₁) Y₂).toLinearMap=
    g.toLinearMap.comp (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap := by
  let f := homComp g (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
  have hcomp : postcompose f
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)=
      tensorOuterIntertwiner hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
        (postcompose g Y₁) Y₂ := by
    have ecomp : postcompose f
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)=
        postcompose g (postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
          hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
          (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
            (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)) := by
      apply Subtype.ext
      funext n k
      rfl
    rw [ecomp,tensorOuterFactor_comp_intertwiner,← tensorOuterIntertwiner_postcompose hC2
      N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ Q₄ hQ₄ g]
  exact (tensorOuterFactor_unique hC2 N₁ N₂ N₃ Q₄ N₅ hfg₁ hfg₂ hfg₃ hQ₄ hfg₅
    (postcompose g Y₁) Y₂ f hcomp).symm

end VOA.Huang.LogAssocTensorOuterModes
