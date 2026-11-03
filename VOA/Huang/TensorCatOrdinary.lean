import VOA.Huang.FusionProductUnique
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Products.Basic

/-! # The complex-linear category of ordinary VOA modules

Objects carry actual ordinary modules, and morphisms commute with every mode.
The carrier universe agrees with the existing fusion-product universal property.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Bundled ordinary modules, including reducible modules and the zero module. -/
structure Ordinary where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  isMod : OrdVModule W carrier

attribute [instance] Ordinary.addCommGroup Ordinary.module

instance : Category (Ordinary W) where
  Hom X Y := homSpace X.isMod Y.isMod
  id _ := ⟨LinearMap.id, fun _ _ _ => rfl⟩
  comp f g := compHom g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {W}

/-- Equality of module morphisms can be checked on vectors. -/
@[ext] theorem Ordinary.hom_ext {X Y : Ordinary W} (f g : X ⟶ Y)
    (h : ∀ x, f.val x = g.val x) : f = g :=
  Subtype.ext (LinearMap.ext h)

@[simp] theorem Ordinary.id_apply (X : Ordinary W) (x : X.carrier) :
    (𝟙 X : X ⟶ X).val x = x := rfl

@[simp] theorem Ordinary.comp_apply {X Y Z : Ordinary W} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) : (f ≫ g).val x = g.val (f.val x) := rfl

instance : Preadditive (Ordinary W) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homSpace X.isMod Y.isMod))
  add_comp := by
    intro X Y Z f f' g
    apply Ordinary.hom_ext
    intro x
    exact g.val.map_add (f.val x) (f'.val x)
  comp_add := by intros; rfl

instance : Linear ℂ (Ordinary W) where
  homModule X Y := inferInstanceAs (Module ℂ (homSpace X.isMod Y.isMod))
  smul_comp := by
    intro X Y Z c f g
    apply Ordinary.hom_ext
    intro x
    exact g.val.map_smul c (f.val x)
  comp_smul := by intros; rfl

/-- An ordinary module as an object of its actual module category. -/
def Ordinary.of {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) : Ordinary W := ⟨M, A⟩

/-- Bundle an existing representing fusion product as an ordinary object. -/
def Ordinary.ofProduct {X Y : Ordinary W} (P : Product X.isMod Y.isMod) : Ordinary W :=
  Ordinary.of P.isMod

/-- Module equivalences give categorical isomorphisms, without a monoidal assumption. -/
def Ordinary.isoOfModuleEquiv {X Y : Ordinary W} (e : ModuleEquiv W X.isMod Y.isMod) :
    X ≅ Y where
  hom := ⟨e.toLinearEquiv.toLinearMap, e.map_act⟩
  inv := ⟨e.symm.toLinearEquiv.toLinearMap, e.symm.map_act⟩
  hom_inv_id := by apply Ordinary.hom_ext; exact e.toLinearEquiv.symm_apply_apply
  inv_hom_id := by apply Ordinary.hom_ext; exact e.toLinearEquiv.apply_symm_apply

/-- The actual adjoint ordinary module is the proposed tensor unit. -/
def vacuumObject : Ordinary W := Ordinary.of (adjointModule W)

end VOA.Huang.TensorCat
