import VOA.Classification.COne.McRaeM2LogMonoidalStruct
import VOA.Huang.LogAssocTensorTriangle

/-! The categorical logarithmic triangle is the proved full-carrier vacuum
triangle for the actual associator and actual unit maps. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual nested categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The genuine actual categorical associator and unitors satisfy the triangle. -/
theorem associatorIso_triangle (N P : LogModuleCat W) :
    (associatorIso hC2 N unitObject P).hom ≫
      tensorMorphism hC2 (𝟙 N) (leftUnitIso hC2 P).hom=
    tensorMorphism hC2 (rightUnitIso hC2 N).hom (𝟙 P) := by
  apply hom_ext
  intro x
  exact congrArg (fun F => F x) (tensorTriangleHom_eq hC2 N.act P.act
    N.finiteGeneration P.finiteGeneration)

end VOA.LogTensor.LogModuleCat
