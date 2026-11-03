import VOA.Huang.LogAssocTensorOuterModes
import VOA.Modules.LogTensorArPairing

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




/-- The genuine tensor-source action transposes the actual coproduct on
the coefficient span. The double contragredient twist is proved literally. -/
theorem pair_tensor_mode_coefficient {d : ℤ} {u : V} (hu : u∈W.grading d) (p : ℤ)
    (B : coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (ξ : C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW) :
    C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW
      ((coefficientSpanToTensorDualHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂).toLinearMap B)
      (mode ((tensorModule hC2 N₁ N₂ hfg₁ hfg₂).YM u) p ξ)=
    C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW
      ((coefficientSpanToTensorDualHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂).toLinearMap
        ⟨Huang.PzTensorRho.rhoL N₁.toWeakModule N₂.toWeakModule u p B.1,
          coefficientSpan_rho_stable hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
            Y₁ Y₂ hu p B.2⟩) ξ := by
  let N := tensorDual hC2 N₁ N₂ hfg₁ hfg₂
  let χ := (coefficientSpanToTensorDualHom hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap
  have he : Ar.oppB N.toWeakModule u p (χ B)=
      χ ⟨Huang.PzTensorRho.rhoL N₁.toWeakModule N₂.toWeakModule u p B.1,
        coefficientSpan_rho_stable hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
          Y₁ Y₂ hu p B.2⟩ := by
    rw [Ar.oppB_homog N.toWeakModule hu p]
    apply Subtype.ext
    simp only [LinearMap.smul_apply,LinearMap.coe_sum,Finset.sum_apply,
      Submodule.coe_smul,Submodule.coe_sum]
    have hm (j : ℕ) :
        (mode (N.YM ((W.L 1^j) u)) (2*d-p-2-j) (χ B) :
          BilinearDual (M₁ := M₁) (M₂ := M₂))=
        Huang.PzTensorRho.tauHat N₁.toWeakModule N₂.toWeakModule (d-j) ((W.L 1^j) u)
          (2*d-p-2-j) B.1 := by
      change (mode ((maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule).field
        ((W.L 1^j) u)) (2*d-p-2-j) (χ B) : BilinearDual (M₁ := M₁) (M₂ := M₂))=_
      rw [CompatibleSpace.mode_field,CompatibleSpace.action_homogeneous _ _
        (VertexOperatorAlgebra.L_one_pow_mem W hu j)]
      rfl
    simp only [hm]
    exact Huang.PzTensorY4.twist_twist N₁.toWeakModule N₂.toWeakModule hu p B.1
  change C2Rigid.dualPairing N.toGW (χ B) (mode ((contraLog N).YM u) p ξ)=_
  rw [Ar.pair_contra_opposite N hu p (χ B) ξ,he]

end VOA.Huang.LogAssocTensorOuterModes
