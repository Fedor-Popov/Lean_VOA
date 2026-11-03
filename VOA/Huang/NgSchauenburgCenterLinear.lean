import VOA.Huang.NgSchauenburgCategory

/-! # Linear structure on Mathlib's Drinfeld center

Mathlib supplies the category, monoidal structure, braiding, forgetful
monoidal functor and reflection of isomorphisms. Here central morphisms are
identified with a submodule of the underlying Hom space. This supplies the
linear and monoidal linear structures and finite-dimensional Hom spaces.
Rigidity, semisimplicity, the finite simple family and modularity of the
center are not constructed in this file.
-/

noncomputable section
universe v u
namespace VOA.Huang.NgSchauenburg.CenterLinear

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Central morphisms as a genuine submodule of the underlying Hom space. -/
def homSubmodule (X Y : Center C) : Submodule ℂ (X.1 ⟶ Y.1) where
  carrier := {f | ∀ U, f ▷ U ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ U ◁ f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg U
    simp [MonoidalPreadditive.add_whiskerRight, MonoidalPreadditive.whiskerLeft_add,
      Preadditive.add_comp, Preadditive.comp_add, hf U, hg U]
  smul_mem' := by intro z f hf U; simp [hf U]

def homEquiv (X Y : Center C) : (X ⟶ Y) ≃ homSubmodule X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance centerPreadditive : Preadditive (Center C) where
  homGroup X Y := (homEquiv X Y).addCommGroup
  add_comp _ _ _ f g h := Center.Hom.ext (Preadditive.add_comp _ _ _ f.f g.f h.f)
  comp_add _ _ _ f g h := Center.Hom.ext (Preadditive.comp_add _ _ _ f.f g.f h.f)

instance centerLinear : Linear ℂ (Center C) where
  homModule X Y := (homEquiv X Y).module ℂ
  smul_comp _ _ _ z f g := Center.Hom.ext (by exact Linear.smul_comp _ _ _ z f.f g.f)
  comp_smul _ _ _ f z g := Center.Hom.ext (by exact Linear.comp_smul _ _ _ f.f z g.f)

instance centerMonoidalPreadditive : MonoidalPreadditive (Center C) where
  whiskerLeft_zero := by intros; apply Center.Hom.ext; exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight := by intros; apply Center.Hom.ext; exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add := by intros; apply Center.Hom.ext; exact MonoidalPreadditive.whiskerLeft_add _ _
  add_whiskerRight := by
    intros; apply Center.Hom.ext; exact MonoidalPreadditive.add_whiskerRight _ _

instance centerMonoidalLinear : MonoidalLinear ℂ (Center C) where
  whiskerLeft_smul := by
    intros; apply Center.Hom.ext; exact MonoidalLinear.whiskerLeft_smul _ _ _
  smul_whiskerRight := by
    intros; apply Center.Hom.ext; exact MonoidalLinear.smul_whiskerRight _ _ _

/-- The forgetful functor is faithful and complex linear. -/
instance forgetFaithful : (Center.forget C).Faithful where
  map_injective h := Center.Hom.ext h

instance forgetLinear : (Center.forget C).Linear ℂ where
  map_smul := by intros; rfl

/-- The central Hom space with its new module structure is the submodule above. -/
def homLinearEquiv (X Y : Center C) : (X ⟶ Y) ≃ₗ[ℂ] homSubmodule X Y :=
  (homEquiv X Y).linearEquiv ℂ

theorem hom_finiteDimensional (X Y : Center C) [FiniteDimensional ℂ (X.1 ⟶ Y.1)] :
    FiniteDimensional ℂ (X ⟶ Y) :=
  (homLinearEquiv X Y).symm.finiteDimensional

end VOA.Huang.NgSchauenburg.CenterLinear
