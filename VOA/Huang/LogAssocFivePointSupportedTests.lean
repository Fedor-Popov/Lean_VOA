import VOA.Huang.LogAssocFivePointEvaluation
import VOA.Huang.LogAssocCoefficientCompatibility
import VOA.Modules.LogTensorTwist

/-! True homogeneous scalar tests remain supported after every genuine
categorical module morphism. This applies to the actual pentagon paths and
their intermediate profiles without an ordinary-module assumption. -/
namespace VOA.Huang.LogAssocFivePoint
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficientCompatibility
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Pullback by an actual categorical map preserves the true output weight support. -/
theorem supportedAt_comp_category {N P : LogModuleCat W} (g : N ⟶ P)
    {f : P →ₗ[ℂ] ℂ} {β : ℂ} (hf : SupportedAt P.act f β) :
    SupportedAt N.act (f ∘ₗ g.1) β := by
  intro a ha x hx
  exact hf a ha (g.1 x) (hom_mem_weight N.act P.act (toWeakHom g) hx)

end VOA.Huang.LogAssocFivePoint
