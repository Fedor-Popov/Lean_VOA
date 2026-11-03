import VOA.Huang.LogAssocTensorAssociatorEvaluation
import VOA.Huang.LogAssocTensorIterateFaithful

/-! The actual canonical tensor associator is uniquely characterized by
its genuine completed product–iterate identity on the convergence overlap. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- No different carrier map can satisfy the actual canonical analytic
associator identity. The uniqueness is proved from genuine mode detection. -/
theorem tensorAssociatorHom_unique_of_completed
    (F : (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule)
    (hF : ∀ (a b c β : ℂ) (x : M₁) (y : M₂) (z : M₃)
      (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
      (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ),
      ∀ t∈overlapDomain,
      completedLogProduct N₁ N₂ N₃ (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₂ N₃ h₂ h₃)
        (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
          h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
        (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
        (Complex.log (1+Complex.exp t)) 0 a β f ⟨x,hx⟩ y z=
      completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
        t 0 c β (f ∘ₗ F.toLinearMap) x y ⟨z,hz⟩) :
    F.toLinearMap=(tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap := by
  apply leftTriple_linearMap_ext_of_completed_iterate hC2 N₁ N₂ N₃ h₁ h₂ h₃
  intro f a b c β x y z hx hy hz t ht
  have hα := tensorAssociatorHom_completed_shift (β := β) hC2 N₁ N₂ N₃ h₁ h₂ h₃
    hx hy hz f ht 0
  simp only [add_zero] at hα
  exact (hF a b c β x y z hx hy hz f t ht).symm.trans hα

end VOA.C2Rigid.LocalInjective
