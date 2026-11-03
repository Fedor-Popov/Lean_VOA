import VOA.Modules.LogTensorUnit
import VOA.Modules.LogTensorFinMain
import Mathlib.CategoryTheory.Linear.Basic

/-! The actual finite logarithmic module category.
Objects carry genuine generalized-module actions and actual finite generation.
Morphisms intertwine all VOA modes. The category and its complex linear
structure are proved from these morphisms, with no categorical witness input. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor
open CategoryTheory VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- An actual finitely generated grading-restricted generalized module. -/
structure LogModuleCat (W : VertexOperatorAlgebra V) where
  carrier : Type u
  [group : AddCommGroup carrier]
  [module : Module ℂ carrier]
  act : LogVModule W carrier
  finiteGeneration : FinGen act.toWeakModule

attribute [instance] LogModuleCat.group LogModuleCat.module

namespace LogModuleCat
variable {W : VertexOperatorAlgebra V}
instance : CoeSort (LogModuleCat W) (Type u) := ⟨fun N => N.carrier⟩

/-- Bundle a genuine finite module with its original action. -/
def of {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (hN : FinGen N.toWeakModule) : LogModuleCat W :=
  ⟨M,N,hN⟩

/-- The actual complex-linear space of genuine module morphisms. -/
abbrev Hom (N P : LogModuleCat W) := moduleHomSpace N.act.toWeakModule P.act.toWeakModule

def identity (N : LogModuleCat W) : Hom N N := ⟨LinearMap.id,fun _ _ _ => rfl⟩

def compose {N P Q : LogModuleCat W} (f : Hom N P) (g : Hom P Q) : Hom N Q :=
  ⟨g.1 ∘ₗ f.1,fun a n x => by
    change g.1 (f.1 (mode (N.act.YM a) n x)) = mode (Q.act.YM a) n (g.1 (f.1 x))
    rw [f.2,g.2]⟩

instance : Category.{u} (LogModuleCat W) where
  Hom := fun N P => (Hom N P : Type u)
  id := identity
  comp f g := compose f g
  id_comp := by intro N P f; apply Subtype.ext; ext x; rfl
  comp_id := by intro N P f; apply Subtype.ext; ext x; rfl
  assoc := by intro N P Q R f g h; apply Subtype.ext; ext x; rfl

/-- Equality of categorical maps is genuine pointwise equality on the carrier. -/
@[ext] theorem hom_ext {N P : LogModuleCat W} {f g : N ⟶ P}
    (h : ∀ x : N, f.1 x=g.1 x) : f=g := by
  apply Subtype.ext
  exact LinearMap.ext h

instance : Preadditive (LogModuleCat W) where
  homGroup N P := inferInstanceAs (AddCommGroup (Hom N P))
  add_comp := by
    intro N P Q f f' g
    apply hom_ext
    intro x
    change g.1 (f.1 x+f'.1 x) = g.1 (f.1 x)+g.1 (f'.1 x)
    exact map_add _ _ _
  comp_add := by
    intro N P Q f g g'
    apply hom_ext
    intro x
    rfl

instance : Linear ℂ (LogModuleCat W) where
  homModule N P := inferInstanceAs (Module ℂ (Hom N P))
  smul_comp := by
    intro N P Q c f g
    apply hom_ext
    intro x
    change g.1 (c • f.1 x)=c • g.1 (f.1 x)
    exact map_smul _ _ _
  comp_smul := by
    intro N P Q f c g
    apply hom_ext
    intro x
    rfl

/-- C2-cofiniteness gives finite-dimensional actual categorical Hom spaces. -/
theorem finiteDimensional_hom (hC2 : C2Cofinite W) (N P : LogModuleCat W) :
    FiniteDimensional ℂ (N ⟶ P) := by
  haveI : FiniteDimensional ℂ
      (LogIntertwiningOperator (adjointModule W).toWeakModule
        N.act.toWeakModule P.act.toWeakModule) :=
    LogFin.logFusionFiniteFact_of_c2Cofinite hC2 V N.carrier P.carrier
      (adjointModule W).toLog N.act P.act finGen_adjoint N.finiteGeneration P.finiteGeneration
  let e := vacuumIntertwinerEquiv N.act.toWeakModule P.act.toWeakModule
  exact e.finiteDimensional

end LogModuleCat
end VOA.LogTensor
