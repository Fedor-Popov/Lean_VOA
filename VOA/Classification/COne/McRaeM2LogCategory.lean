import VOA.Classification.COne.McRaeM2TensorClosure
import VOA.Classification.COne.McRaeM2TensorUnit
import VOA.Classification.COne.McRaeM2TensorRightUnit
import VOA.Classification.COne.McRaeM2TensorBraiding
import VOA.Modules.LogModuleCategory
import Mathlib.CategoryTheory.Products.Basic

/-! The genuine tensor bifunctor and unit/swap isomorphisms on finite logarithmic modules.
These structures package the already proved universal tensor maps; associativity
and hexagon coherence are constructed separately from analytic products. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.Classification.COne VOA.Classification.COne.McRaeM1
  VOA.C2Rigid.LocalInjective VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

def tensorObject (N P : LogModuleCat W) : LogModuleCat W :=
  LogModuleCat.of (tensorModule hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
    (tensorModule_finGen hC2 N.act P.act N.finiteGeneration P.finiteGeneration)

/-- An actual mode-preserving categorical map is its genuine weak-module map. -/
def toWeakHom {N P : LogModuleCat W} (f : N ⟶ P) : N.act.toWeakModule.Hom P.act.toWeakModule :=
  ⟨f.1,f.2⟩

def fromWeakHom {N P : LogModuleCat W} (f : N.act.toWeakModule.Hom P.act.toWeakModule) : N ⟶ P :=
  ⟨f.toLinearMap,f.map_act⟩

def tensorMorphism {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) (g : N₂ ⟶ P₂) :
    tensorObject hC2 N₁ N₂ ⟶ tensorObject hC2 P₁ P₂ :=
  fromWeakHom (tensorMap hC2 N₁.act N₂.act N₁.finiteGeneration N₂.finiteGeneration
    P₁.act P₂.act P₁.finiteGeneration P₂.finiteGeneration (toWeakHom f) (toWeakHom g))

/-- The actual logarithmic tensor product is a genuine categorical bifunctor. -/
def tensorBifunctor : (LogModuleCat W × LogModuleCat W) ⥤ LogModuleCat W where
  obj NP := tensorObject hC2 NP.1 NP.2
  map f := tensorMorphism hC2 f.1 f.2
  map_id NP := by
    apply hom_ext
    intro q
    exact congrArg (fun f => f q) (tensorMap_identity hC2 NP.1.act NP.2.act
      NP.1.finiteGeneration NP.2.finiteGeneration)
  map_comp {X Y Z} f g := by
    apply hom_ext
    intro q
    exact congrArg (fun f => f q) (tensorMap_composition hC2
      X.1.act X.2.act X.1.finiteGeneration X.2.finiteGeneration
      Y.1.act Y.2.act Y.1.finiteGeneration Y.2.finiteGeneration
      Z.1.act Z.2.act Z.1.finiteGeneration Z.2.finiteGeneration
      (toWeakHom f.1) (toWeakHom f.2) (toWeakHom g.1) (toWeakHom g.2))

def unitObject : LogModuleCat W := LogModuleCat.of (adjointModule W).toLog finGen_adjoint

/-- The genuine vacuum-mode unit equivalence is an actual categorical isomorphism. -/
def leftUnitIso (N : LogModuleCat W) : tensorObject hC2 unitObject N ≅ N where
  hom := fromWeakHom (tensorLeftUnitHom hC2 N.act N.finiteGeneration)
  inv := fromWeakHom (tensorLeftUnitInvHom hC2 N.act N.finiteGeneration)
  hom_inv_id := by
    apply hom_ext
    intro q
    exact tensorLeftUnit_inv_hom hC2 N.act N.finiteGeneration q
  inv_hom_id := by
    apply hom_ext
    intro x
    exact tensorLeftUnit_hom_inv hC2 N.act N.finiteGeneration x

/-- The genuine right vacuum unit is an actual categorical isomorphism. -/
def rightUnitIso (N : LogModuleCat W) : tensorObject hC2 N unitObject ≅ N where
  hom := fromWeakHom (tensorRightUnitHom hC2 N.act N.finiteGeneration)
  inv := fromWeakHom (tensorRightUnitInvHom hC2 N.act N.finiteGeneration)
  hom_inv_id := by
    apply hom_ext
    intro q
    exact tensorRightUnit_inv_hom hC2 N.act N.finiteGeneration q
  inv_hom_id := by
    apply hom_ext
    intro x
    exact tensorRightUnit_hom_inv hC2 N.act N.finiteGeneration x

/-- The genuine logarithmic swap and its proved inverse are categorical isomorphisms. -/
def swapIso (N P : LogModuleCat W) (r : ℤ) :
    tensorObject hC2 N P ≅ tensorObject hC2 P N where
  hom := fromWeakHom (tensorBraid hC2 N.act P.act N.finiteGeneration P.finiteGeneration r)
  inv := fromWeakHom (tensorBraid hC2 P.act N.act P.finiteGeneration N.finiteGeneration (-r-1))
  hom_inv_id := by
    apply hom_ext
    intro q
    exact congrArg (fun f => f q) (tensorBraid_inverse_comp hC2
      N.act P.act N.finiteGeneration P.finiteGeneration r)
  inv_hom_id := by
    apply hom_ext
    intro q
    have h := tensorBraid_inverse_comp hC2 P.act N.act P.finiteGeneration N.finiteGeneration (-r-1)
    simpa only [show -(-r-1)-1=r by ring] using congrArg (fun f => f q) h

end VOA.LogTensor.LogModuleCat
