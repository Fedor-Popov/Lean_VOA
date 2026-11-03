import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Huang.LogAssocCompletedProduct
import VOA.Modules.LogTensorPzPointPrecompose
import VOA.Modules.LogTensorPzPointPostcompose
import VOA.Classification.COne.McRaeM2TensorMaps

/-! Actual intermediate module maps can be moved from the outer input to the
inner output of a logarithmic product. The genuine completed sum is unchanged,
so uniqueness of its full convergent logarithmic coefficients gives the same
actual outer intertwiner and universal tensor factor. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.LogAssocCoefficientCoproduct VOA.C2Rigid VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.Huang.AssocCoeffRules (logCoeff_congr)
universe u
variable {V M₁ M₂ M₃ M₄ M₅ Q : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] [AddCommGroup Q] [Module ℂ Q]
  {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (P : LogVModule W Q)
  (ψ : N₅.toWeakModule.Hom P.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule P.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)

/-- The actual completed product is unchanged by moving a genuine intermediate
morphism across its inner and outer operators. No convergence premise is needed
because the scalar summands agree at every actual generalized weight. -/
theorem completedLogProduct_intermediate (ell₁ ell₂ a c : ℂ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : N₁.weight a) (y : M₂) (z : M₃) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ ell₁ ell₂ a c f x y z=
    completedLogProduct N₁ N₂ N₃ N₄ P Y₁ (postcompose ψ Y₂) ell₁ ell₂ a c f x y z := by
  unfold completedLogProduct completedProductPair
  rw [evaluatePoint_postcompose N₂ N₃ N₅ P ψ Y₂ ell₂ y z]
  apply tsum_congr
  intro b
  congr 1
  exact pointEvaluationBlock_precompose N₁ P N₄ N₁ N₅
    (weakIdentity N₁.toWeakModule) ψ Y₁ ell₁ a b c x _

variable (hC2 : C2Cofinite W)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule) (hP : FinGen P.toWeakModule)
include hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hP

/-- The literal full-spectrum products agree on the genuine overlap domain,
independently of how the actual intermediate morphism is inserted. -/
theorem spectrum_intermediate {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ (precompose (weakIdentity N₁.toWeakModule) ψ Y₁).1 Y₂.1
      f x y z a b c β t=
    logProductSpectrumFun hC2 P hP Y₁.1 (postcompose ψ Y₂).1 f x y z a b c β t := by
  rw [← completedLogProduct_eq_spectrum hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ hx hy hz f β ht,
    ← completedLogProduct_eq_spectrum hC2 N₁ N₂ N₃ N₄ P
      hfg₁ hfg₂ hfg₃ hfg₄ hP Y₁ (postcompose ψ Y₂) hx hy hz f β ht]
  exact completedLogProduct_intermediate N₁ N₂ N₃ N₄ N₅ P ψ Y₁ Y₂ _ _ _ _ f ⟨x,hx⟩ y z

/-- Every unique logarithmic collision coefficient is invariant under the
actual intermediate map, including all nonzero logarithmic degrees. -/
theorem coefficient_intermediate (f : M₄ →ₗ[ℂ] ℂ) {z : M₃} {c : ℂ}
    (hz : z∈N₃.weight c) (β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ f z c β γ k=
    coefficient hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂) f z c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ f z c β γ k hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂) f z c β γ k hx hy]
  exact logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => spectrum_intermediate N₁ N₂ N₃ N₄ N₅ P ψ Y₁ Y₂ hC2
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hP hx hy hz f β ht)
    (log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ f x y z a b c β) (γ-a-b) k


-- The actual nested tensor and coefficient inclusions require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The genuine all-logarithmic outer operator is invariant under moving
an actual intermediate morphism through the product. -/
theorem tensorOuterIntertwiner_intermediate :
    tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂=
    tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂) := by
  apply logZero_injective
  funext n
  change (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂).1 n 0=
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂)).1 n 0
  rw [tensorOuterIntertwiner_zero,tensorOuterIntertwiner_zero]
  apply bilinear_ext_homogeneous (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃
  intro γ c ξ z hξ hz
  rw [← sub_eq_zero]
  apply eq_zero_of_supported_log hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
  intro β f hf
  rw [map_sub,tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂ n hξ hz f hf,
    tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂) n hξ hz f hf]
  split_ifs
  · apply sub_eq_zero.mpr
    apply congrArg (fun B : maximalCarrier N₁.toWeakModule N₂.toWeakModule =>
      C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW B ξ)
    apply Subtype.ext
    exact coefficient_intermediate N₁ N₂ N₃ N₄ N₅ P ψ Y₁ Y₂ hC2
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hP f hz β γ 0
  · exact sub_self _

/-- The actual universal factor depends only on the genuine product. -/
theorem tensorOuterFactor_intermediate :
    (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      (precompose (weakIdentity N₁.toWeakModule) ψ Y₁) Y₂).toLinearMap=
    (tensorOuterFactor hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
      Y₁ (postcompose ψ Y₂)).toLinearMap := by
  apply tensorOuterFactor_unique hC2 N₁ N₂ N₃ N₄ P hfg₁ hfg₂ hfg₃ hfg₄ hP
    Y₁ (postcompose ψ Y₂)
  rw [tensorOuterFactor_comp_intertwiner,tensorOuterIntertwiner_intermediate]

end VOA.Huang.LogAssocTensorOuterModes
