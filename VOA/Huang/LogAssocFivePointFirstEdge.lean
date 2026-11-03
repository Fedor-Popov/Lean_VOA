import VOA.Huang.LogAssocFivePointFrozenPoint
import VOA.Huang.LogAssocTensorAssociatorEvaluation
import VOA.Classification.COne.McRaeM2TensorMaps

/-! The first genuine logarithmic five-point sewing edge, with the unaffected
internal weight frozen in an actual outer point block. The identity follows
from the proved completed associator and naturality of the true point block;
no pentagon, joint convergence, or sewing witness is assumed. -/
set_option maxSynthPendingDepth 3
namespace VOA.C2Rigid.LocalInjective
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
open VOA.Huang.LogAssocFivePointFunctionals VOA.Huang.LogAssocCoefficientCompatibility
universe u
variable {V M₁ M₂ M₃ M₄ O : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup O] [Module ℂ O] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)
  (N₄ : LogVModule W M₄) (N₀ : LogVModule W O)
  (J : LogIntertwiningOperator
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule N₄.toWeakModule N₀.toWeakModule)

-- Actual triple tensor and finite point-block types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- Genuine first sewing fiber: the actual inner reassociation commutes with
the fixed-weight outer point pairing, retaining every logarithmic degree. -/
theorem firstFiberEdge_completed (ell₃ v d ε : ℂ) (f : O →ₗ[ℂ] ℂ)
    (hf : SupportedAt N₀ f ε) {w : M₄} (hw : w∈N₄.weight d)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    completedLogProduct N₁ N₂ N₃
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)+s) s a v
      (frozenPointFunctional (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ N₀
        J ell₃ v d ε f w) ⟨x,hx⟩ y z=
    completedLogIterate N₁ N₂ N₃
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) (t+s) s c v
      (frozenPointFunctional (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ N₀
        (precompose (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃)
          (weakIdentity N₄.toWeakModule) J) ell₃ v d ε f w) x y ⟨z,hz⟩ := by
  rw [frozenPointFunctional_precompose
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄ N₀ J
    (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) N₄
    (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃) (weakIdentity N₄.toWeakModule)
    ell₃ v d ε f hf hw]
  exact tensorAssociatorHom_completed_shift (β := v) hC2 N₁ N₂ N₃ h₁ h₂ h₃
    hx hy hz (frozenPointFunctional (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      N₄ N₀ J ell₃ v d ε f w) ht s

end VOA.C2Rigid.LocalInjective
