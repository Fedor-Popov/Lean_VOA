import VOA.Classification.COne.McRaeM2LogAssociator
import Mathlib.CategoryTheory.Monoidal.Category

/-! Concrete logarithmic tensor, associator, and unit data in the standard
categorical interface. This structure packages only actual proved maps and
isomorphisms; the monoidal laws require their genuine coherence proofs. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Nested actual categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The standard tensor structure consists of the genuine logarithmic tensor
objects and maps, the concrete associator isomorphism, and actual unitors. -/
abbrev logarithmicTensorStruct : MonoidalCategoryStruct (LogModuleCat W) where
  tensorObj := tensorObject hC2
  whiskerLeft := fun N {_ _} f => tensorMorphism hC2 (𝟙 N) f
  whiskerRight := fun {_ _} f N => tensorMorphism hC2 f (𝟙 N)
  tensorHom := fun {_ _ _ _} f g => tensorMorphism hC2 f g
  tensorUnit := unitObject
  associator := associatorIso hC2
  leftUnitor := leftUnitIso hC2
  rightUnitor := rightUnitIso hC2

/-- The packaged associator is the actual proved logarithmic associator. -/
theorem logarithmicTensorStruct_associator (N P Q : LogModuleCat W) :
    (logarithmicTensorStruct hC2).associator N P Q=associatorIso hC2 N P Q := rfl

/-- The packaged tensor morphism is the actual representing tensor map. -/
theorem logarithmicTensorStruct_tensorHom {N P Q R : LogModuleCat W}
    (f : N ⟶ P) (g : Q ⟶ R) :
    (logarithmicTensorStruct hC2).tensorHom f g=tensorMorphism hC2 f g := rfl

end VOA.LogTensor.LogModuleCat
