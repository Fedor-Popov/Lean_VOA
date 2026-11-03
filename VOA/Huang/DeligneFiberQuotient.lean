/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import VOA.Huang.DeligneFiberField

/-!
# Deligne's fiber functor — quotients of lax braided functors by ideals

**Ind-objects without Ind-categories.**  For a semisimple `D`, a commutative algebra `A` in
`Ind(D)` is the same as the lax braided functor `Y ↦ Hom(𝟙, A ⊗ Y)` from `D` to vector spaces
(Day convolution: algebra objects = lax monoidal functors).  Ideals of `A` are then families of
subspaces `I Y ⊆ F Y`, natural in `Y` and absorbing under the multiplication `μ`; quotient
algebras are pointwise quotients.  This file provides that quotient construction:

* `LaxIdeal Fn` — an ideal in a lax braided functor `Fn : D ⥤ ModuleCat ℂ`;
* `LaxIdeal.quot` — the quotient functor `Y ↦ Fn Y ⧸ I Y`, with `LaxBraided`, `Additive`,
  `Linear` instances; `quot_ε_apply`, `quot_μ_apply`, `quot_map_apply` compute on classes.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Functor.LaxMonoidal
open scoped TensorProduct

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- An **ideal** of a lax braided functor `Fn : D ⥤ ModuleCat ℂ` (= an ideal of the corresponding
commutative algebra in `Ind(D)`): natural subspaces absorbing under the multiplication. -/
structure LaxIdeal (Fn : D ⥤ ModuleCat.{0} ℂ) [Fn.LaxMonoidal] where
  I : ∀ Y : D, Submodule ℂ (Fn.obj Y)
  map_mem : ∀ {Y Y' : D} (f : Y ⟶ Y') (y : Fn.obj Y), y ∈ I Y → (Fn.map f).hom y ∈ I Y'
  mul_mem_left : ∀ (Y Z : D) (y : Fn.obj Y) (z : Fn.obj Z), z ∈ I Z →
    (μ Fn Y Z).hom (y ⊗ₜ z) ∈ I (Y ⊗ Z)
  mul_mem_right : ∀ (Y Z : D) (y : Fn.obj Y) (z : Fn.obj Z), y ∈ I Y →
    (μ Fn Y Z).hom (y ⊗ₜ z) ∈ I (Y ⊗ Z)

namespace LaxIdeal

variable {Fn : D ⥤ ModuleCat.{0} ℂ} [Fn.LaxMonoidal] (J : LaxIdeal Fn)

/-- The quotient functor `Y ↦ Fn Y ⧸ I Y`. -/
def quot : D ⥤ ModuleCat.{0} ℂ where
  obj Y := ModuleCat.of ℂ (Fn.obj Y ⧸ J.I Y)
  map f := ModuleCat.ofHom ((J.I _).mapQ (J.I _) (Fn.map f).hom (fun y hy => J.map_mem f y hy))
  map_id Y := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

@[simp] theorem quot_map_apply {Y Y' : D} (f : Y ⟶ Y') (y : Fn.obj Y) :
    (J.quot.map f).hom (Submodule.Quotient.mk y : Fn.obj Y ⧸ J.I Y) =
      (Submodule.Quotient.mk ((Fn.map f).hom y) : Fn.obj Y' ⧸ J.I Y') := rfl

/-- The bilinear multiplication on quotients. -/
def mulQ (Y Z : D) : (Fn.obj Y ⧸ J.I Y) →ₗ[ℂ] (Fn.obj Z ⧸ J.I Z) →ₗ[ℂ] (Fn.obj (Y ⊗ Z) ⧸ J.I (Y ⊗ Z)) :=
  let B : Fn.obj Y →ₗ[ℂ] Fn.obj Z →ₗ[ℂ] (Fn.obj (Y ⊗ Z) ⧸ J.I (Y ⊗ Z)) :=
    (TensorProduct.mk ℂ (Fn.obj Y) (Fn.obj Z)).compr₂ ((J.I (Y ⊗ Z)).mkQ ∘ₗ (μ Fn Y Z).hom)
  let C : (Fn.obj Z ⧸ J.I Z) →ₗ[ℂ] Fn.obj Y →ₗ[ℂ] (Fn.obj (Y ⊗ Z) ⧸ J.I (Y ⊗ Z)) :=
    (J.I Z).liftQ B.flip (by
      intro z hz
      simp only [LinearMap.mem_ker]
      ext y
      simp [B, (Submodule.Quotient.mk_eq_zero _).2 (J.mul_mem_left Y Z y z hz)])
  (J.I Y).liftQ C.flip (by
      intro y hy
      simp only [LinearMap.mem_ker]
      ext z
      simp [C, B, (Submodule.Quotient.mk_eq_zero _).2 (J.mul_mem_right Y Z y z hy)])

@[simp] theorem mulQ_mk (Y Z : D) (y : Fn.obj Y) (z : Fn.obj Z) :
    J.mulQ Y Z (Submodule.Quotient.mk y) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((μ Fn Y Z).hom (y ⊗ₜ z)) := rfl

instance : J.quot.LaxMonoidal where
  ε := ModuleCat.ofHom ((J.I (𝟙_ D)).mkQ ∘ₗ (ε Fn).hom)
  μ Y Z := ModuleCat.ofHom (TensorProduct.lift (J.mulQ Y Z))
  μ_natural_left f X' := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have h := congrArg (fun φ => φ.hom (y ⊗ₜ z)) (Functor.LaxMonoidal.μ_natural_left Fn f X')
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply] at h
    exact congrArg Submodule.Quotient.mk h
  μ_natural_right X' f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have h := congrArg (fun φ => φ.hom (y ⊗ₜ z)) (Functor.LaxMonoidal.μ_natural_right Fn X' f)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
    exact congrArg Submodule.Quotient.mk h
  associativity X Y Z := by
    apply ModuleCat.MonoidalCategory.tensor_ext₃'
    intro a b c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have h := congrArg (fun φ => φ.hom ((x ⊗ₜ y) ⊗ₜ z)) (Functor.LaxMonoidal.associativity Fn X Y Z)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply] at h
    exact congrArg Submodule.Quotient.mk h
  left_unitality X := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c a
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have h := congrArg (fun φ => φ.hom (c ⊗ₜ x)) (Functor.LaxMonoidal.left_unitality Fn X)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply] at h
    exact congrArg Submodule.Quotient.mk h
  right_unitality X := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have h := congrArg (fun φ => φ.hom (x ⊗ₜ c)) (Functor.LaxMonoidal.right_unitality Fn X)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply] at h
    exact congrArg Submodule.Quotient.mk h

@[simp] theorem quot_ε_apply (c : ℂ) :
    (ε J.quot).hom c = (Submodule.Quotient.mk ((ε Fn).hom c) : Fn.obj (𝟙_ D) ⧸ J.I (𝟙_ D)) := rfl

@[simp] theorem quot_μ_apply (Y Z : D) (y : Fn.obj Y) (z : Fn.obj Z) :
    (μ J.quot Y Z).hom ((Submodule.Quotient.mk y : Fn.obj Y ⧸ J.I Y) ⊗ₜ
      (Submodule.Quotient.mk z : Fn.obj Z ⧸ J.I Z)) =
      (Submodule.Quotient.mk ((μ Fn Y Z).hom (y ⊗ₜ z)) : Fn.obj (Y ⊗ Z) ⧸ J.I (Y ⊗ Z)) := rfl

end LaxIdeal

section Braided

variable {Fn : D ⥤ ModuleCat.{0} ℂ} [Fn.LaxBraided] (J : LaxIdeal Fn)

instance : J.quot.LaxBraided where
  braided X Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have h := congrArg (fun φ => φ.hom (x ⊗ₜ y)) (Functor.LaxBraided.braided (F := Fn) X Y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply] at h
    exact congrArg Submodule.Quotient.mk h

end Braided

section Linear

variable [Preadditive D] {Fn : D ⥤ ModuleCat.{0} ℂ} [Fn.LaxMonoidal] (J : LaxIdeal Fn)

instance [Fn.Additive] : J.quot.Additive where
  map_add {Y Y' f g} := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show (Submodule.Quotient.mk ((Fn.map (f + g)).hom y) : Fn.obj Y' ⧸ J.I Y') =
      Submodule.Quotient.mk ((Fn.map f).hom y) + Submodule.Quotient.mk ((Fn.map g).hom y)
    rw [Fn.map_add]; rfl

instance [Linear ℂ D] [Fn.Linear ℂ] : J.quot.Linear ℂ where
  map_smul {Y Y'} f c := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show (Submodule.Quotient.mk ((Fn.map (c • f)).hom y) : Fn.obj Y' ⧸ J.I Y') =
      c • Submodule.Quotient.mk ((Fn.map f).hom y)
    rw [Functor.map_smul]; rfl

end Linear

end VOA.Huang.TensorCat.DeligneFiber
