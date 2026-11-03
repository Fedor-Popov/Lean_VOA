import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Classification.COne.McRaeM2TensorMaps
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




variable {P₃ : Type u} [AddCommGroup P₃] [Module ℂ P₃]
variable (Q₃ : LogVModule W P₃) (hQ₃ : FinGen Q₃.toWeakModule)
variable (g : Q₃.toWeakModule.Hom N₃.toWeakModule)

/-- The literal coefficient is natural in the actual third module. -/
theorem coefficient_precompose_third (f : M₄ →ₗ[ℂ] ℂ) (z : P₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
      Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) f z c β γ k=
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f (g.toLinearMap z) c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [coefficient_homogeneous hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
    Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) f z c β γ k hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f (g.toLinearMap z) c β γ k hx hy]
  rfl

set_option maxHeartbeats 1000000 in
/-- The genuine all-logarithmic outer operator is natural in its actual
third input, retaining every nilpotent logarithmic degree. -/
theorem tensorOuterIntertwiner_precompose_third :
    tensorOuterIntertwiner hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
      Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂)=
    precompose (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) := by
  apply logZero_injective
  funext n
  change (tensorOuterIntertwiner hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
    Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂)).1 n 0=
    (precompose (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)).1 n 0
  rw [tensorOuterIntertwiner_zero]
  apply bilinear_ext_homogeneous (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
  intro γ c ξ z hξ hz
  rw [precompose_apply,tensorOuterIntertwiner_zero]
  rw [← sub_eq_zero]
  apply eq_zero_of_supported_log hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
  intro β f hf
  rw [map_sub]
  change f (tensorOuterModes hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
    Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) n ξ z)-
    f (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ n ξ (g.toLinearMap z))=0
  rw [tensorOuterModes_pair hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
    Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) n hξ hz f hf,
    tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ n hξ (hom_mem_weight Q₃ N₃ g hz) f hf]
  split_ifs
  · apply sub_eq_zero.mpr
    congr 2
  · exact sub_self _

/-- Genuine tensor-factor naturality in the third input. -/
theorem tensorOuterFactor_precompose_third :
    (tensorOuterFactor hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
      Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂)).toLinearMap=
    (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap.comp
      (tensorMap hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hQ₃
        (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃
        (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g).toLinearMap := by
  let T := tensorMap hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
    (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hQ₃
    (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃
    (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g
  let f := homComp (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) T
  have hf : postcompose f
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hQ₃)=
      tensorOuterIntertwiner hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
        Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) := by
    have ecomp : postcompose f
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
          (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hQ₃)=
        postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
          (postcompose T (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) Q₃
            (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hQ₃)) := by
      apply Subtype.ext
      funext n k
      rfl
    rw [ecomp,tensorMap_intertwiner]
    have eswap : postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (precompose (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g
          (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
            (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃))=
        precompose (weakIdentity (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule) g
          (postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
            (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
              (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)) := by
      apply Subtype.ext
      funext n k
      rfl
    rw [eswap,tensorOuterFactor_comp_intertwiner,
      ← tensorOuterIntertwiner_precompose_third hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ Q₃ hQ₃ g]
  exact (tensorOuterFactor_unique hC2 N₁ N₂ Q₃ N₄ N₅ hfg₁ hfg₂ hQ₃ hfg₄ hfg₅
    Y₁ (precompose (weakIdentity N₂.toWeakModule) g Y₂) f hf).symm

end VOA.Huang.LogAssocTensorOuterModes
