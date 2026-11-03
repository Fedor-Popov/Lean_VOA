import VOA.Huang.LogAssocTensorAssociatorAnnihilator
import VOA.Huang.LogAssocHomSurjectivity
import VOA.Huang.LogAssocProductInfinityDetection

/-! The actual canonical tensor associator is onto. Its genuine scalar
range annihilators vanish by completed product–iterate equality, true
infinity coefficient detection, and the proved actual tensor mode spans. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocTensorOuterModes
open VOA.Huang.LogAssocExpansion VOA.Huang.LogAssocCoefficientCompatibility
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- Surjectivity of the actual associator on the actual full logarithmic
module carriers, with no associativity or ordinary-module hypothesis. -/
theorem tensorAssociatorHom_surjective :
    Function.Surjective (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap := by
  apply surjective_of_supported_annihilators
    (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
    (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
  intro β f hf hcomp
  apply supported_functional_eq_zero_of_nested_modes hC2 N₁ N₂ N₃ h₁ h₂ h₃ β f hf
  intro a b c x y z hx hy hz γ
  let T := tensorModule hC2 N₂ N₃ h₂ h₃
  let R := rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  have hfgR : FinGen R.toWeakModule := tensorModule_finGen hC2 N₁ T h₁ hfgT
  exact product_mode_zero_of_completed_zero hC2 N₁ N₂ N₃ R T
    h₁ h₂ h₃ hfgR hfgT
    (tensorIntertwiner hC2 N₁ T h₁ hfgT)
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃) hx hy hz f β
    (fun t ht => tensorAssociator_product_zero_of_comp (β := β)
      hC2 N₁ N₂ N₃ h₁ h₂ h₃ f hcomp hx hy hz ht) γ 0

end VOA.C2Rigid.LocalInjective
