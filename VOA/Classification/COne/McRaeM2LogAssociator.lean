import VOA.Classification.COne.McRaeM2LogCategory
import VOA.Huang.LogAssocTensorAssociatorIso
import VOA.Huang.LogAssocTensorAssociatorNatural

/-! The actual logarithmic associator is a natural categorical isomorphism.
Its maps, inverse laws, and naturality are the genuine tensor-carrier theorems;
no associativity or coherence witness is supplied as an extra premise. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.Classification.COne VOA.Classification.COne.McRaeM1
  VOA.C2Rigid.LocalInjective VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual nested categorical tensor objects require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The proved genuine logarithmic associator as a categorical isomorphism. -/
def associatorIso (N P Q : LogModuleCat W) :
    tensorObject hC2 (tensorObject hC2 N P) Q ≅
      tensorObject hC2 N (tensorObject hC2 P Q) where
  hom := fromWeakHom (tensorAssociatorHom hC2 N.act P.act Q.act
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration)
  inv := fromWeakHom (tensorAssociatorInverseHom hC2 N.act P.act Q.act
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration)
  hom_inv_id := by
    apply hom_ext
    intro x
    exact congrArg (fun f => f x) (tensorAssociatorInverseHom_comp hC2
      N.act P.act Q.act N.finiteGeneration P.finiteGeneration Q.finiteGeneration)
  inv_hom_id := by
    apply hom_ext
    intro y
    exact congrArg (fun f => f y) (tensorAssociatorHom_inverse_comp hC2
      N.act P.act Q.act N.finiteGeneration P.finiteGeneration Q.finiteGeneration)

-- Actual nested categorical tensor objects require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The actual categorical associator is natural in all three module morphisms. -/
theorem associatorIso_naturality {N P Q N' P' Q' : LogModuleCat W}
    (f : N ⟶ N') (g : P ⟶ P') (h : Q ⟶ Q') :
    tensorMorphism hC2 (tensorMorphism hC2 f g) h ≫
      (associatorIso hC2 N' P' Q').hom=
    (associatorIso hC2 N P Q).hom ≫
      tensorMorphism hC2 f (tensorMorphism hC2 g h) := by
  apply hom_ext
  intro x
  exact congrArg (fun F => F x) (tensorAssociatorHom_natural hC2
    N.act P.act Q.act N.finiteGeneration P.finiteGeneration Q.finiteGeneration
    N'.act P'.act Q'.act N'.finiteGeneration P'.finiteGeneration Q'.finiteGeneration
    (toWeakHom f) (toWeakHom g) (toWeakHom h)).symm

end VOA.LogTensor.LogModuleCat
