/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangRigidPivotal
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The twist-pivotal dimension through an arbitrary exact pairing, and its transport

Monoidal category theory only.

* `twistPivotal_trL_id` — for the twist pivotal structure, `tr(𝟙_X)` can be computed with ANY
  exact pairing `(X, Y, η, ε)`: `tr(𝟙_X) = η ≫ (θ_X ▷ Y) ≫ β_{X,Y} ≫ ε` (comparison of the pairing
  with the chosen one by `rightDualIso`, naturality of the braiding);
* `map_coev_braid_ev` — along a braided monoidal fully faithful functor `G`, the composite
  `η ≫ β ≫ ε` of the pulled-back pairing (`ExactPairing.ofFullyFaithful`) is sent to
  `η_G ≫ (η' ≫ β' ≫ ε') ≫ ε_G`;
* `smul_of_conj` — scalars of `End 𝟙` are preserved.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open CategoryTheory CategoryTheory.MonoidalCategory VOA.Huang.TensorCat VOA.Huang.HuangRigid

universe v u v' u'

section Pairing

variable {𝒞 : Type u} [Category.{v} 𝒞] [MonoidalCategory 𝒞] [BraidedCategory 𝒞]
  [RightRigidCategory 𝒞] [Preadditive 𝒞] [Linear ℂ 𝒞] {θ : ∀ X : 𝒞, X ≅ X}

/-- **The twist-pivotal trace of the identity through any exact pairing.** -/
theorem twistPivotal_trL_id (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
    (X Y : 𝒞) (p : ExactPairing X Y) :
    (twistPivotal hθ).trL (𝟙 X) =
      @ExactPairing.coevaluation 𝒞 _ _ X Y p ≫ ((θ X).hom ▷ Y) ≫ (β_ X Y).hom ≫
        @ExactPairing.evaluation 𝒞 _ _ X Y p := by
  simp only [PivotalStructure.trL, id_whiskerRight, Category.id_comp]
  change η_ X Xᘁ ≫ ((twistPivIso θ X).hom ▷ Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) = _
  rw [twistPiv_evaluation]
  -- compare the chosen pairing with `p`
  set i := rightDualIso p (HasRightDual.exact (X := X)) with hi
  have hη : η_ X Xᘁ = @ExactPairing.coevaluation 𝒞 _ _ X Y p ≫ (X ◁ i.hom) := by
    have h := @coevaluation_comp_rightAdjointMate 𝒞 _ _ X X ⟨Xᘁ⟩ ⟨Y⟩ (𝟙 X)
    rw [id_whiskerRight, Category.comp_id] at h
    exact h.symm
  have hε : ε_ X Xᘁ = (i.inv ▷ X) ≫ @ExactPairing.evaluation 𝒞 _ _ X Y p := by
    have h := @rightAdjointMate_comp_evaluation 𝒞 _ _ X X ⟨Y⟩ ⟨Xᘁ⟩ (𝟙 X)
    rw [whiskerLeft_id, Category.id_comp] at h
    exact h.symm
  rw [hη, hε, Category.assoc, whisker_exchange_assoc,
    BraidedCategory.braiding_naturality_right_assoc, ← comp_whiskerRight_assoc, i.hom_inv_id,
    id_whiskerRight, Category.id_comp]

end Pairing

section Transport

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (G : C ⥤ D) [G.Monoidal] [G.Full] [G.Faithful]

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- **Transport of `η ≫ β ≫ ε`** along a braided fully faithful monoidal functor. -/
theorem map_coev_braid_ev
    (hbr : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (X Y : C) [ExactPairing (G.obj X) (G.obj Y)] :
    G.map (@ExactPairing.coevaluation C _ _ X Y (ExactPairing.ofFullyFaithful G X Y) ≫
        (β_ X Y).hom ≫ @ExactPairing.evaluation C _ _ X Y (ExactPairing.ofFullyFaithful G X Y)) =
      η G ≫ (η_ (G.obj X) (G.obj Y) ≫ (β_ (G.obj X) (G.obj Y)).hom ≫
        ε_ (G.obj X) (G.obj Y)) ≫ ε G := by
  change G.map (G.preimage (η G ≫ η_ _ _ ≫ μ G _ _) ≫ (β_ X Y).hom ≫
    G.preimage (δ G _ _ ≫ ε_ _ _ ≫ ε G)) = _
  rw [G.map_comp, G.map_comp, G.map_preimage, G.map_preimage]
  simp only [Category.assoc]
  rw [← Category.assoc (μ G X Y), hbr, Category.assoc, Functor.Monoidal.μ_δ_assoc]

end Transport

section Scalar

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  (G : C ⥤ D) [G.Monoidal] [G.Additive] [G.Linear ℂ]

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- Scalars of `End 𝟙` survive the transport `f ↦ ε_G ≫ G f ≫ η_G`. -/
theorem smul_of_conj (f : 𝟙_ C ⟶ 𝟙_ C) (g : 𝟙_ D ⟶ 𝟙_ D) (k : ℂ) (hf : f = k • 𝟙 _)
    (hg : G.map f = η G ≫ g ≫ ε G) : g = k • 𝟙 _ := by
  have h1 : ε G ≫ G.map f ≫ η G = g := by
    rw [hg]; simp
  rw [← h1, hf, Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
    Category.id_comp, Linear.comp_smul, Functor.Monoidal.ε_η]

end Scalar

end VOA.Huang.HuangModularity
