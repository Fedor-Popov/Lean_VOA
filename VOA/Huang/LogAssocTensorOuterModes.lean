import VOA.Huang.LogAssocCoefficientCoproductFinite
import VOA.Huang.LogAssocCoefficientOuterModes
import VOA.Modules.LogTensorPzJacobiDerivative

/-! Literal outer modes on the actual logarithmic tensor object, obtained
from the actual collision coefficient inclusion in its tensor dual. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct VOA.C2Rigid VOA.C2Rigid.LocalInjective
open VOA.Classification.COne
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



/-- The actual coefficient inclusion, with the genuine tensor-dual codomain. -/
noncomputable def coefficientSpanToTensorDualHom :
    (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).Hom
      (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule :=
  coefficientSpanHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂

/-- Actual outer zeroth modes on (N1 tensor N2) times N3. -/
noncomputable def tensorOuterModes (n : ℂ) :
    C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW →ₗ[ℂ] M₃ →ₗ[ℂ] M₄ :=
  coefficientOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (tensorDual hC2 N₁ N₂ hfg₁ hfg₂)
    (coefficientSpanToTensorDualHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂).toLinearMap n

theorem tensorOuterModes_weight (n : ℂ) :
    HasModeWeight (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ N₄ n
      (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n) :=
  coefficientOuterModes_weight hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (tensorDual hC2 N₁ N₂ hfg₁ hfg₂) _ n

theorem tensorOuterModes_truncated
    (ξ : C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW) (z : M₃) (n : ℂ) :
    ∃ K : ℤ,∀ j : ℤ,K ≤ j →
      tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (n+j) ξ z=0 :=
  coefficientOuterModes_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (tensorDual hC2 N₁ N₂ hfg₁ hfg₂) _ ξ z n

/-- Its literal matrix coefficient is the original genuine collision
coefficient in the actual maximal compatible tensor dual. -/
theorem tensorOuterModes_pair (n : ℂ) {γ c β : ℂ}
    {ξ : C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW} {z : M₃}
    (hξ : ξ∈(tensorModule hC2 N₁ N₂ hfg₁ hfg₂).weight γ) (hz : z∈N₃.weight c)
    (f : Dual ℂ M₄) (hf : SupportedAt N₄ f β) :
    f (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n ξ z)=
      if β=γ+c-n-1 then C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW
        ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
          coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
            Y₁ Y₂ f z c β γ 0 hf hz⟩ ξ else 0 :=
  coefficientOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (tensorDual hC2 N₁ N₂ hfg₁ hfg₂) _ n hξ hz f hf

/-- All outer logarithmic degrees, built by the genuine nilpotent lift of
these literal zeroth modes. The Jacobi theorem is established separately. -/
noncomputable def tensorOuterLogModes :
    LogModes (C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW) M₃ M₄ :=
  logLift (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ N₄
    (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

@[simp] theorem tensorOuterLogModes_zero (n : ℂ) :
    tensorOuterLogModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n 0=
      tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n :=
  logLift_zero _ _ _ _ n

end VOA.Huang.LogAssocTensorOuterModes
