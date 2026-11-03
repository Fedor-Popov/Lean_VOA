import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Huang.LogAssocCoefficientTensorPair
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




variable {P₁ P₂ : Type u} [AddCommGroup P₁] [Module ℂ P₁]
  [AddCommGroup P₂] [Module ℂ P₂]
variable (Q₁ : LogVModule W P₁) (Q₂ : LogVModule W P₂)
  (hQ₁ : FinGen Q₁.toWeakModule) (hQ₂ : FinGen Q₂.toWeakModule)
variable (f₁ : Q₁.toWeakModule.Hom N₁.toWeakModule) (f₂ : Q₂.toWeakModule.Hom N₂.toWeakModule)

/-- The genuine full-spectrum coefficient is natural in its actual first
two inputs, with the actual intermediate module and every log degree retained. -/
theorem coefficient_precompose_inputs (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
      (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) f z c β γ k=
    (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k).compl₂ f₂.toLinearMap
      ∘ₗ f₁.toLinearMap := by
  apply bilinear_ext_homogeneous Q₁ Q₂
  intro a b x y hx hy
  simp only [LinearMap.comp_apply,LinearMap.compl₂_apply]
  rw [coefficient_homogeneous hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
    (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
    (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) f z c β γ k hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f z c β γ k (hom_mem_weight Q₁ N₁ f₁ hx) (hom_mem_weight Q₂ N₂ f₂ hy)]
  rfl

set_option maxHeartbeats 2000000 in
/-- The actual all-logarithmic outer operator is natural in the first two
inputs. Genuine canonical coefficients linearly span the actual tensor. -/
theorem tensorOuterIntertwiner_precompose_inputs :
    tensorOuterIntertwiner hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
      (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂)=
    precompose (tensorMap hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂)
      (weakIdentity N₃.toWeakModule)
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) := by
  apply logZero_injective
  funext n
  change (tensorOuterIntertwiner hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
    (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
    (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂)).1 n 0=
    (precompose (tensorMap hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂)
      (weakIdentity N₃.toWeakModule)
      (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)).1 n 0
  rw [tensorOuterIntertwiner_zero]
  apply tensor_linearMap_ext_homogeneous hC2 Q₁ Q₂ hQ₁ hQ₂
  intro m a b x y hx hy
  apply LinearMap.ext
  intro z
  rw [precompose_apply,tensorOuterIntertwiner_zero]
  have hm := congrArg (fun Y : LogIntertwiningOperator Q₁.toWeakModule Q₂.toWeakModule
      (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule => Y.1 m 0 x y)
    (tensorMap_intertwiner hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂)
  simp only [postcompose_apply,precompose_apply] at hm
  rw [hm]
  change tensorOuterModes hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
      (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) n
      ((tensorIntertwiner hC2 Q₁ Q₂ hQ₁ hQ₂).1 m 0 x y) z=
    tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n
      ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 m 0 (f₁.toLinearMap x) (f₂.toLinearMap y)) z
  let A := (tensorOuterModes hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
    (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
    (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) n)
    ((tensorIntertwiner hC2 Q₁ Q₂ hQ₁ hQ₂).1 m 0 x y)
  let B := (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n)
    ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 m 0 (f₁.toLinearMap x) (f₂.toLinearMap y))
  change A z=B z
  refine LogFin.induction_on N₃ (C := fun z => A z=B z) z ?_ (by simp) ?_
  · intro c z hz
    dsimp only [A,B]
    let γ := a+b-m-1
    have hP := (tensorIntertwiner hC2 Q₁ Q₂ hQ₁ hQ₂).2.mem_weight hx hy m 0
    have hN := (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).2.mem_weight
      (hom_mem_weight Q₁ N₁ f₁ hx) (hom_mem_weight Q₂ N₂ f₂ hy) m 0
    rw [← sub_eq_zero]
    apply eq_zero_of_supported_log hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    intro β f hf
    rw [map_sub,tensorOuterModes_pair hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
      (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) n hP hz f hf,
      tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n hN hz f hf]
    split_ifs
    · have hp := LogAssocCoefficientL0.tensorIntertwiner_pair_coefficient hC2 Q₁ Q₂ hQ₁ hQ₂
        N₃ N₄ N₅ hfg₃ hfg₄ hfg₅ (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
        (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) f z c β γ 0 hx hy hf hz
      have hn := LogAssocCoefficientL0.tensorIntertwiner_pair_coefficient hC2 N₁ N₂ hfg₁ hfg₂
        N₃ N₄ N₅ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0
        (hom_mem_weight Q₁ N₁ f₁ hx) (hom_mem_weight Q₂ N₂ f₂ hy) hf hz
      have eγ : a+b-γ-1=m := by dsimp [γ]; ring
      rw [eγ] at hp hn
      rw [hp,hn]
      have hc := congrArg (fun B : P₁ →ₗ[ℂ] P₂ →ₗ[ℂ] ℂ => B x y)
        (coefficient_precompose_inputs hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
          Y₁ Y₂ Q₁ Q₂ hQ₁ hQ₂ f₁ f₂ f z c β γ 0)
      exact sub_eq_zero.mpr hc
    · exact sub_self _
  · intro z z' hz hz'
    rw [map_add,map_add,hz,hz']


/-- The actual tensor factor is natural in the first two inputs, through
the genuine tensor of their actual module morphisms. -/
theorem tensorOuterFactor_precompose_inputs :
    (tensorOuterFactor hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
      (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
      (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂)).toLinearMap=
    (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap.comp
      (tensorMap hC2 (tensorModule hC2 Q₁ Q₂ hQ₁ hQ₂) N₃
        (tensorModule_finGen hC2 Q₁ Q₂ hQ₁ hQ₂) hfg₃
        (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃
        (tensorMap hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂)
        (weakIdentity N₃.toWeakModule)).toLinearMap := by
  let T₁₂ := tensorMap hC2 Q₁ Q₂ hQ₁ hQ₂ N₁ N₂ hfg₁ hfg₂ f₁ f₂
  let T := tensorMap hC2 (tensorModule hC2 Q₁ Q₂ hQ₁ hQ₂) N₃
    (tensorModule_finGen hC2 Q₁ Q₂ hQ₁ hQ₂) hfg₃
    (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
    (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃ T₁₂ (weakIdentity N₃.toWeakModule)
  let f := homComp (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) T
  have hf : postcompose f
      (tensorIntertwiner hC2 (tensorModule hC2 Q₁ Q₂ hQ₁ hQ₂) N₃
        (tensorModule_finGen hC2 Q₁ Q₂ hQ₁ hQ₂) hfg₃)=
      tensorOuterIntertwiner hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
        (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
        (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) := by
    have ecomp : postcompose f
        (tensorIntertwiner hC2 (tensorModule hC2 Q₁ Q₂ hQ₁ hQ₂) N₃
          (tensorModule_finGen hC2 Q₁ Q₂ hQ₁ hQ₂) hfg₃)=
        postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
          (postcompose T (tensorIntertwiner hC2 (tensorModule hC2 Q₁ Q₂ hQ₁ hQ₂) N₃
            (tensorModule_finGen hC2 Q₁ Q₂ hQ₁ hQ₂) hfg₃)) := by
      apply Subtype.ext
      funext n k
      rfl
    rw [ecomp,tensorMap_intertwiner]
    have eswap : postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (precompose T₁₂ (weakIdentity N₃.toWeakModule)
          (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
            (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃))=
        precompose T₁₂ (weakIdentity N₃.toWeakModule)
          (postcompose (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
            (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
              (tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂) hfg₃)) := by
      apply Subtype.ext
      funext n k
      rfl
    rw [eswap,tensorOuterFactor_comp_intertwiner,
      ← tensorOuterIntertwiner_precompose_inputs hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ Q₁ Q₂ hQ₁ hQ₂ f₁ f₂]
  exact (tensorOuterFactor_unique hC2 Q₁ Q₂ N₃ N₄ N₅ hQ₁ hQ₂ hfg₃ hfg₄ hfg₅
    (precompose f₁ (weakIdentity N₅.toWeakModule) Y₁)
    (precompose f₂ (weakIdentity N₃.toWeakModule) Y₂) f hf).symm

end VOA.Huang.LogAssocTensorOuterModes
