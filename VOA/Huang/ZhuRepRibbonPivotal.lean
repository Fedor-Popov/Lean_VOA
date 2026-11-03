/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NgSchauenburgModular
import VOA.Huang.NgSchauenburgDualCoherence
import VOA.Huang.HuangRigidPivotal

/-!
# A ribbon twist gives a monoidal, spherical Ng–Schauenburg pivotal structure

Let `C` be a braided category with chosen right duals and a natural automorphism `θ` of the
identity satisfying balancing `θ_{X ⊗ Y} = (θ_X ⊗ θ_Y) c_{Y,X} c_{X,Y}`, `θ_𝟙 = 𝟙` and
`θ_{Xᘁ} = (θ_X)ᘁ`.  The twisted Drinfeld isomorphism `j = θ u` (`HuangRigid.twistPivIso`) is then
a pivotal structure in the strong sense of `NgSchauenburg.Pivotal`:

* `drinfeld_evaluation` — the Ng–Schauenburg Drinfeld morphism `u` has transpose `c_{X,Xᘁ} ≫ ε_X`;
  hence `twistPivIso_hom_eq : j_X = θ_X ≫ u_X`;
* `ribbonDualTensor` — the canonical iso `Yᘁ ⊗ Xᘁ ≅ (X ⊗ Y)ᘁ` (from `TensorCat.tensorPairing`);
* `braiding_tensorDualEvaluation` — the braided evaluation of `X ⊗ Y` is the nested one up to the
  inverse monodromy of the duals (no symmetry assumed);
* `twistPiv_monoidal` — monoidality of `j`;
* `ribbonPivotal_spherical` — sphericality;
* `ribbonPivotal`, `ribbonOfTwist : Ribbon (ribbonPivotal …)`.

All statements are about abstract categories; no VOA input.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.ZhuRep

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg VOA.Huang.HuangRigid

universe v u

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Sliding a cap `h : A ⊗ B ⟶ 𝟙` under a strand `Z` crossing its left leg (braided form). -/
theorem braiding_whiskerRight_cap' {A B : C} (Z : C) (h : A ⊗ B ⟶ 𝟙_ C) :
    (β_ A Z).hom ▷ B ⊗≫ Z ◁ h = 𝟙 _ ⊗≫ A ◁ (β_ B Z).inv ⊗≫ h ▷ Z ⊗≫ 𝟙 _ := by
  have hb : (β_ A Z).hom ▷ B = 𝟙 _ ⊗≫ A ◁ (β_ B Z).inv ⊗≫ (β_ (A ⊗ B) Z).hom ⊗≫ 𝟙 _ := by
    rw [braiding_tensor_left_hom]
    simp [monoidalComp]
  have hn := braiding_naturality_left h Z
  calc
    _ = 𝟙 _ ⊗≫ A ◁ (β_ B Z).inv ⊗≫ ((β_ (A ⊗ B) Z).hom ≫ Z ◁ h) ⊗≫ 𝟙 _ := by
      rw [hb]; monoidal
    _ = _ := by
      rw [← hn]; simp only [braiding_tensorUnit_left]; monoidal

/-- Sliding a cap `h : B ⊗ D ⟶ 𝟙` under a strand `Z` crossing its right leg backwards. -/
theorem braiding_inv_whiskerRight_cap {B D : C} (Z : C) (h : B ⊗ D ⟶ 𝟙_ C) :
    (β_ Z B).inv ▷ D ⊗≫ Z ◁ h = 𝟙 _ ⊗≫ B ◁ (β_ Z D).hom ⊗≫ h ▷ Z ⊗≫ 𝟙 _ := by
  have hb : B ◁ (β_ Z D).hom = 𝟙 _ ⊗≫ (β_ Z B).inv ▷ D ⊗≫ (β_ Z (B ⊗ D)).hom ⊗≫ 𝟙 _ := by
    rw [braiding_tensor_right_hom]
    simp [monoidalComp]
  have hn := braiding_naturality_right Z h
  calc
    _ = 𝟙 _ ⊗≫ (β_ Z B).inv ▷ D ⊗≫ ((β_ Z (B ⊗ D)).hom ≫ h ▷ Z) ⊗≫ 𝟙 _ := by
      rw [← hn]; simp only [braiding_tensorUnit_right]; monoidal
    _ = _ := by
      rw [hb]; monoidal

/-- A cap absorbs a block braiding on its left. -/
theorem braiding_cap_right' {A B : C} (W : C) (h : A ⊗ B ⟶ 𝟙_ C) :
    (β_ (A ⊗ B) W).hom ≫ W ◁ h = h ▷ W ⊗≫ 𝟙 _ := by
  rw [← braiding_naturality_left]; simp only [braiding_tensorUnit_left]; monoidal

/-- Yang–Baxter with an inverse crossing underneath a strand passing over both. -/
theorem yang_baxter_inv (Y A B : C) :
    (β_ Y A).hom ▷ B ⊗≫ A ◁ (β_ Y B).hom ⊗≫ (β_ B A).inv ▷ Y =
      𝟙 _ ⊗≫ Y ◁ (β_ B A).inv ⊗≫ (β_ Y B).hom ▷ A ⊗≫ B ◁ (β_ Y A).hom ⊗≫ 𝟙 _ := by
  have hn := braiding_naturality_right Y (β_ B A).inv
  calc
    _ = 𝟙 _ ⊗≫ ((β_ Y (A ⊗ B)).hom ≫ (β_ B A).inv ▷ Y) ⊗≫ 𝟙 _ := by
      rw [braiding_tensor_right_hom]; monoidal
    _ = 𝟙 _ ⊗≫ (Y ◁ (β_ B A).inv ≫ (β_ Y (B ⊗ A)).hom) ⊗≫ 𝟙 _ := by rw [← hn]
    _ = _ := by
      rw [braiding_tensor_right_hom]; monoidal

end Braided

section Rigid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- **The transpose of the Ng–Schauenburg Drinfeld morphism** is the braided evaluation. -/
theorem drinfeld_evaluation (X : C) :
    (drinfeldMorphism X ▷ Xᘁ) ≫ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  calc
    _ = 𝟙 _ ⊗≫ η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ▷ Xᘁ ⊗≫
          (Xᘁ : C) ◁ ((β_ X (Xᘁ : C)ᘁ).inv ▷ Xᘁ ⊗≫ X ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ) ⊗≫ ε_ X Xᘁ := by
      calc
        _ = 𝟙 _ ⊗≫ η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ▷ Xᘁ ⊗≫ (Xᘁ : C) ◁ (β_ X (Xᘁ : C)ᘁ).inv ▷ Xᘁ ⊗≫
              (ε_ X Xᘁ ▷ ((Xᘁ : C)ᘁ ⊗ Xᘁ) ≫ 𝟙_ C ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ) ⊗≫ 𝟙 _ := by
          simp only [drinfeldMorphism]; monoidal
        _ = 𝟙 _ ⊗≫ η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ▷ Xᘁ ⊗≫ (Xᘁ : C) ◁ (β_ X (Xᘁ : C)ᘁ).inv ▷ Xᘁ ⊗≫
              ((Xᘁ ⊗ X) ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ ≫ ε_ X Xᘁ ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
        _ = _ := by monoidal
    _ = 𝟙 _ ⊗≫ η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ▷ Xᘁ ⊗≫
          (Xᘁ : C) ◁ ((Xᘁ : C)ᘁ ◁ (β_ X Xᘁ).hom ⊗≫ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X) ⊗≫ ε_ X Xᘁ := by
      rw [braiding_inv_whiskerRight_cap]; monoidal
    _ = 𝟙 _ ⊗≫ (η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ (X ⊗ Xᘁ) ≫ ((Xᘁ : C) ⊗ (Xᘁ : C)ᘁ) ◁ (β_ X Xᘁ).hom) ⊗≫
          (Xᘁ : C) ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ⊗≫ ε_ X Xᘁ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (𝟙_ C ◁ (β_ X Xᘁ).hom ≫ η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ ((Xᘁ : C) ⊗ X)) ⊗≫
          (Xᘁ : C) ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ X ⊗≫ ε_ X Xᘁ := by
      rw [whisker_exchange]
    _ = (β_ X Xᘁ).hom ⊗≫ (η_ (Xᘁ : C) (Xᘁ : C)ᘁ ▷ Xᘁ ⊗≫ (Xᘁ : C) ◁ ε_ (Xᘁ : C) (Xᘁ : C)ᘁ) ▷ X ⊗≫ ε_ X Xᘁ := by
      monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']; monoidal

/-- The twisted Drinfeld isomorphism is `θ ≫ u` (Ng–Schauenburg's `Ribbon.pivotal` shape). -/
theorem twistPivIso_hom_eq (θ : ∀ X : C, X ≅ X) (X : C) :
    (twistPivIso θ X).hom = (θ X).hom ≫ drinfeldMorphism X := by
  apply transpose_injective (A := Xᘁ)
  rw [twistPiv_evaluation, comp_whiskerRight, Category.assoc, drinfeld_evaluation]

/-- The nested evaluation of `X ⊗ Y` in `⊗≫` form. -/
theorem tensorDualEvaluation_eq (X Y : C) :
    tensorDualEvaluation C X Y = 𝟙 _ ⊗≫ (Yᘁ : C) ◁ ε_ X Xᘁ ▷ Y ⊗≫ ε_ Y Yᘁ := by
  dsimp only [tensorDualEvaluation]; monoidal

/-- The canonical comparison `Yᘁ ⊗ Xᘁ ≅ (X ⊗ Y)ᘁ` of two right duals of `X ⊗ Y`. -/
def ribbonDualTensor (X Y : C) : (Yᘁ : C) ⊗ Xᘁ ≅ (X ⊗ Y)ᘁ :=
  rightDualIso (TensorCat.tensorPairing X Xᘁ Y Yᘁ) (HasRightDual.exact (X := X ⊗ Y))

theorem ribbonDualTensor_eval (X Y : C) :
    (ribbonDualTensor X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (X ⊗ Y)ᘁ = tensorDualEvaluation C X Y := by
  letI := TensorCat.tensorPairing X Xᘁ Y Yᘁ
  have h := @rightAdjointMate_comp_evaluation C _ _ (X ⊗ Y) (X ⊗ Y) ⟨(X ⊗ Y)ᘁ⟩
    ⟨(Yᘁ : C) ⊗ Xᘁ⟩ (𝟙 _)
  rw [whiskerLeft_id, Category.id_comp] at h
  refine h.trans ?_
  change (𝟙 _ ⊗≫ (Yᘁ : C) ◁ ε_ X Xᘁ ▷ Y ⊗≫ ε_ Y Yᘁ) = _
  rw [tensorDualEvaluation_eq]

/-- The canonical comparison `𝟙 ≅ 𝟙ᘁ`. -/
def ribbonDualUnit : 𝟙_ C ≅ (𝟙_ C)ᘁ :=
  rightDualIso exactPairingUnit (HasRightDual.exact (X := 𝟙_ C))

theorem ribbonDualUnit_eval :
    ribbonDualUnit.hom ▷ (𝟙_ C) ≫ ε_ (𝟙_ C) (𝟙_ C)ᘁ = (λ_ (𝟙_ C)).hom := by
  have h := @rightAdjointMate_comp_evaluation C _ _ (𝟙_ C) (𝟙_ C) ⟨(𝟙_ C)ᘁ⟩
    ⟨𝟙_ C⟩ (𝟙 _)
  rw [whiskerLeft_id, Category.id_comp] at h
  refine h.trans ?_
  change (ρ_ (𝟙_ C)).hom = _
  rw [unitors_equal]

/-- The mate of a braiding along the nested evaluations is the braiding of the duals. -/
theorem whiskerLeft_braiding_tensorDualEvaluation (X Y : C) :
    ((Xᘁ : C) ⊗ Yᘁ) ◁ (β_ X Y).hom ≫ tensorDualEvaluation C Y X =
      (β_ (Xᘁ : C) Yᘁ).hom ▷ (X ⊗ Y) ≫ tensorDualEvaluation C X Y := by
  rw [tensorDualEvaluation_eq, tensorDualEvaluation_eq]
  calc
    _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((Yᘁ : C) ◁ (β_ X Y).hom ⊗≫ ε_ Y Yᘁ ▷ X) ⊗≫ ε_ X Xᘁ := by monoidal
    _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((β_ X Yᘁ).inv ▷ Y ⊗≫ X ◁ ε_ Y Yᘁ) ⊗≫ ε_ X Xᘁ := by
      rw [braiding_inv_whiskerRight_cap]; monoidal
    _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ (β_ X Yᘁ).inv ▷ Y ⊗≫
          (((Xᘁ : C) ⊗ X) ◁ ε_ Y Yᘁ ≫ ε_ X Xᘁ ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ (β_ X Yᘁ).inv ▷ Y ⊗≫
          (ε_ X Xᘁ ▷ ((Yᘁ : C) ⊗ Y) ≫ 𝟙_ C ◁ ε_ Y Yᘁ) ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((Xᘁ : C) ◁ (β_ X Yᘁ).inv ⊗≫ ε_ X Xᘁ ▷ (Yᘁ : C)) ▷ Y ⊗≫ ε_ Y Yᘁ := by
      monoidal
    _ = 𝟙 _ ⊗≫ ((β_ (Xᘁ : C) Yᘁ).hom ▷ X ⊗≫ (Yᘁ : C) ◁ ε_ X Xᘁ) ▷ Y ⊗≫ ε_ Y Yᘁ := by
      rw [braiding_whiskerRight_cap']; monoidal
    _ = _ := by monoidal

/-- **The braided evaluation of `X ⊗ Y` is the nested one, up to the inverse monodromy of the
duals** (braided version of `TensorCat.braiding_tensorPairing_eval`; no symmetry assumed). -/
theorem braiding_tensorDualEvaluation (X Y : C) :
    (β_ (X ⊗ Y) ((Yᘁ : C) ⊗ Xᘁ)).hom ≫ tensorDualEvaluation C X Y =
      (X ⊗ Y) ◁ ((β_ (Xᘁ : C) Yᘁ).inv ≫ (β_ (Yᘁ : C) Xᘁ).inv) ⊗≫
        X ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ▷ (Xᘁ : C) ⊗≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [tensorDualEvaluation_eq, braiding_tensor_left_hom, braiding_tensor_right_hom X Yᘁ Xᘁ,
    braiding_tensor_right_hom Y Yᘁ Xᘁ]
  have hm : (β_ (Xᘁ : C) Yᘁ).inv =
      ((β_ (Xᘁ : C) Yᘁ).inv ≫ (β_ (Yᘁ : C) Xᘁ).inv) ≫ (β_ (Yᘁ : C) Xᘁ).hom := by simp
  calc
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y Yᘁ).hom ▷ (Xᘁ : C) ⊗≫ (Yᘁ : C) ◁ (β_ Y Xᘁ).hom) ⊗≫
          ((β_ X Yᘁ).hom ▷ (Xᘁ : C) ⊗≫ (Yᘁ : C) ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) ▷ Y ⊗≫
          ε_ Y Yᘁ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y Yᘁ).hom ▷ (Xᘁ : C) ⊗≫ (Yᘁ : C) ◁ (β_ Y Xᘁ).hom ⊗≫
          (β_ (Xᘁ : C) Yᘁ).inv ▷ Y) ⊗≫ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ (Yᘁ : C) ▷ Y ⊗≫
          ε_ Y Yᘁ := by
      rw [braiding_whiskerRight_cap']; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ (Xᘁ : C) Yᘁ).inv ⊗≫ (β_ Y Xᘁ).hom ▷ (Yᘁ : C) ⊗≫
          (Xᘁ : C) ◁ (β_ Y Yᘁ).hom) ⊗≫ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ (Yᘁ : C) ▷ Y ⊗≫
          ε_ Y Yᘁ := by
      rw [yang_baxter_inv]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ (Xᘁ : C) Yᘁ).inv ⊗≫ (β_ Y Xᘁ).hom ▷ (Yᘁ : C)) ⊗≫
          ((X ⊗ Xᘁ) ◁ (β_ Y Yᘁ).hom ≫ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ ((Yᘁ : C) ⊗ Y)) ⊗≫
          ε_ Y Yᘁ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ (Xᘁ : C) Yᘁ).inv ⊗≫ (β_ Y Xᘁ).hom ▷ (Yᘁ : C)) ⊗≫
          (((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ (Y ⊗ Yᘁ) ≫ 𝟙_ C ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ)) ⊗≫
          𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ (Xᘁ : C) Yᘁ).inv ⊗≫ (β_ Y Xᘁ).hom ▷ (Yᘁ : C)) ⊗≫
          ((X ⊗ Xᘁ) ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ≫ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ 𝟙_ C) ⊗≫
          𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ ((β_ (Xᘁ : C) Yᘁ).inv ≫ (β_ (Yᘁ : C) Xᘁ).inv) ⊗≫
          ((β_ (Y ⊗ Yᘁ) Xᘁ).hom ≫ (Xᘁ : C) ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ))) ⊗≫
          ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) := by
      rw [braiding_tensor_left_hom]
      conv_lhs => rw [hm]
      simp only [whiskerLeft_comp]
      monoidal
    _ = _ := by
      rw [braiding_cap_right']; monoidal

/-- **Monodromy-corrected braided evaluation**: precomposing with the double braiding of `X`
and `Y`, the braided evaluation of `X ⊗ Y` is exactly the nested braided evaluation. -/
theorem monodromy_braiding_tensorDualEvaluation (X Y : C) :
    ((β_ X Y).hom ≫ (β_ Y X).hom) ▷ ((Yᘁ : C) ⊗ Xᘁ) ≫ (β_ (X ⊗ Y) ((Yᘁ : C) ⊗ Xᘁ)).hom ≫
        tensorDualEvaluation C X Y =
      𝟙 _ ⊗≫ X ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ▷ (Xᘁ : C) ⊗≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  have h1 : ((Yᘁ : C) ⊗ Xᘁ) ◁ ((β_ X Y).hom ≫ (β_ Y X).hom) ≫ tensorDualEvaluation C X Y =
      ((β_ (Yᘁ : C) Xᘁ).hom ≫ (β_ (Xᘁ : C) Yᘁ).hom) ▷ (X ⊗ Y) ≫
        tensorDualEvaluation C X Y := by
    rw [whiskerLeft_comp, Category.assoc, whiskerLeft_braiding_tensorDualEvaluation Y X,
      whisker_exchange_assoc, whiskerLeft_braiding_tensorDualEvaluation X Y, comp_whiskerRight,
      Category.assoc]
  rw [braiding_naturality_left_assoc, h1, ← braiding_naturality_right_assoc,
    braiding_tensorDualEvaluation, monoidalComp, ← whiskerLeft_comp_assoc]
  have hc : ((β_ (Yᘁ : C) Xᘁ).hom ≫ (β_ (Xᘁ : C) Yᘁ).hom) ≫
      ((β_ (Xᘁ : C) Yᘁ).inv ≫ (β_ (Yᘁ : C) Xᘁ).inv) = 𝟙 _ := by simp
  rw [hc, whiskerLeft_id, Category.id_comp]
  monoidal

/-- Naturality of the nested evaluation in the two outer strands. -/
theorem nested_naturality {X X₁ Y Y₁ X' Y' : C} (f : X ⟶ X₁) (g : Y ⟶ Y₁)
    (hX : X₁ ⊗ X' ⟶ 𝟙_ C) (hY : Y₁ ⊗ Y' ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ▷ (Y' ⊗ X') ≫ (𝟙 _ ⊗≫ X₁ ◁ hY ▷ X' ⊗≫ hX) =
      𝟙 _ ⊗≫ X ◁ (g ▷ Y' ≫ hY) ▷ X' ⊗≫ (f ▷ X' ≫ hX) := by
  rw [tensorHom_def]
  calc
    _ = 𝟙 _ ⊗≫ (f ▷ (Y ⊗ Y' ⊗ X') ≫
          X₁ ◁ ((α_ Y Y' X').inv ≫ (g ▷ Y' ≫ hY) ▷ X' ≫ (λ_ X').hom)) ⊗≫ hX := by
      monoidal
    _ = 𝟙 _ ⊗≫ (X ◁ ((α_ Y Y' X').inv ≫ (g ▷ Y' ≫ hY) ▷ X' ≫ (λ_ X').hom) ≫ f ▷ X') ⊗≫
          hX := by
      rw [whisker_exchange]
    _ = _ := by monoidal

end Rigid

section Ribbon

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] (θ : ∀ X : C, X ≅ X)
  (hnat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
  (hbal : ∀ X Y : C, (θ (X ⊗ Y)).hom = ((θ X).hom ⊗ₘ (θ Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom)
  (hunit : (θ (𝟙_ C)).hom = 𝟙 (𝟙_ C))
  (hdual : ∀ X : C, (θ Xᘁ).hom = ((θ X).hom)ᘁ)

include hbal in
/-- **Monoidality of the twisted Drinfeld isomorphism** (Ng–Schauenburg `Pivotal.monoidal`). -/
theorem twistPiv_monoidal (X Y : C) :
    (twistPivIso θ (X ⊗ Y)).hom = ((twistPivIso θ X).hom ⊗ₘ (twistPivIso θ Y).hom) ≫
      (ribbonDualTensor (Yᘁ : C) Xᘁ).hom ≫ ((ribbonDualTensor X Y).inv)ᘁ := by
  apply transpose_injective (A := (X ⊗ Y)ᘁ)
  apply (cancel_epi ((X ⊗ Y) ◁ (ribbonDualTensor X Y).hom)).mp
  have hL : (X ⊗ Y) ◁ (ribbonDualTensor X Y).hom ≫ (twistPivIso θ (X ⊗ Y)).hom ▷ (X ⊗ Y)ᘁ ≫
      ε_ ((X ⊗ Y)ᘁ) ((X ⊗ Y)ᘁ)ᘁ =
      ((θ X).hom ⊗ₘ (θ Y).hom) ▷ ((Yᘁ : C) ⊗ Xᘁ) ≫
        (𝟙 _ ⊗≫ X ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ▷ (Xᘁ : C) ⊗≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ) := by
    rw [twistPiv_evaluation, whisker_exchange_assoc, braiding_naturality_right_assoc,
      ribbonDualTensor_eval, hbal, comp_whiskerRight, Category.assoc,
      monodromy_braiding_tensorDualEvaluation]
  have hR : (X ⊗ Y) ◁ (ribbonDualTensor X Y).hom ≫
      (((twistPivIso θ X).hom ⊗ₘ (twistPivIso θ Y).hom) ≫
        (ribbonDualTensor (Yᘁ : C) Xᘁ).hom ≫ ((ribbonDualTensor X Y).inv)ᘁ) ▷ (X ⊗ Y)ᘁ ≫
      ε_ ((X ⊗ Y)ᘁ) ((X ⊗ Y)ᘁ)ᘁ =
      ((θ X).hom ⊗ₘ (θ Y).hom) ▷ ((Yᘁ : C) ⊗ Xᘁ) ≫
        (𝟙 _ ⊗≫ X ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ▷ (Xᘁ : C) ⊗≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ) := by
    rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      rightAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp,
      comp_whiskerRight_assoc, ribbonDualTensor_eval, tensorDualEvaluation_eq,
      nested_naturality, twistPiv_evaluation, twistPiv_evaluation, nested_naturality]
  rw [hL, hR]

/-- The unit clause of the Ng–Schauenburg pivotal structure. -/
theorem twistPiv_unit (hunit : (θ (𝟙_ C)).hom = 𝟙 (𝟙_ C)) :
    (twistPivIso θ (𝟙_ C)).hom = ribbonDualUnit.hom ≫ rightAdjointMate (ribbonDualUnit (C := C)).inv := by
  apply transpose_injective (A := (𝟙_ C)ᘁ)
  have he : ε_ (𝟙_ C) (𝟙_ C)ᘁ = ribbonDualUnit.inv ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom := by
    rw [← ribbonDualUnit_eval, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
      Category.id_comp]
  rw [twistPiv_evaluation, hunit, id_whiskerRight, Category.id_comp, comp_whiskerRight,
    Category.assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    ribbonDualUnit_eval, braiding_tensorUnit_left, he]
  monoidal

include hnat hbal hunit hdual in
/-- The inverse monodromy of a dual pair under the evaluation is a double twist
(copy of `NSCongruence.inverseMonodromy_evaluation`, from the ribbon axioms alone). -/
theorem inverseMonodromy_evaluation' (V : C) :
    (β_ V Vᘁ).inv ≫ (β_ (Vᘁ : C) V).inv ≫ ε_ V Vᘁ =
      (Vᘁ : C) ◁ ((θ V).hom ≫ (θ V).hom) ≫ ε_ V Vᘁ := by
  have hn := hnat (ε_ V Vᘁ)
  rw [hunit, Category.comp_id, hbal] at hn
  have h1 : (β_ V Vᘁ).inv ≫ (β_ (Vᘁ : C) V).inv ≫ ε_ V Vᘁ =
      ((θ (Vᘁ : C)).hom ⊗ₘ (θ V).hom) ≫ ε_ V Vᘁ := by
    conv_lhs => rw [hn]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    rw [← braiding_inv_naturality_assoc, ← braiding_inv_naturality_assoc]
    simp
  rw [h1, hdual, MonoidalCategory.tensorHom_def, Category.assoc,
    ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc]

include hnat hbal hunit hdual in
/-- The inverse braiding under the evaluation is the double twist under the braided evaluation. -/
theorem braiding_inv_evaluation (V : C) :
    (β_ (Vᘁ : C) V).inv ≫ ε_ V Vᘁ =
      ((θ V).hom ≫ (θ V).hom) ▷ (Vᘁ : C) ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ := by
  have h := inverseMonodromy_evaluation' θ hnat hbal hunit hdual V
  rw [braiding_naturality_left_assoc, ← h, Iso.hom_inv_id_assoc]

/-- The coevaluation of the twisted swapped pairing. -/
theorem coevaluation_twistPivIso_inv (X : C) :
    η_ (Xᘁ : C) (Xᘁ : C)ᘁ ≫ (Xᘁ : C) ◁ (twistPivIso θ X).inv =
      η_ X Xᘁ ≫ (β_ (Xᘁ : C) X).inv ≫ (Xᘁ : C) ◁ (θ X).inv := by
  letI := twistSwapPairing θ X
  have h := coevaluation_of_evaluation (X := (Xᘁ : C)) (A := X) (B := (Xᘁ : C)ᘁ)
    (twistPivIso θ X).hom (twistPiv_evaluation θ X)
  rw [← h, Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id,
    Category.comp_id]
  change (η_ X Xᘁ ≫ (β_ (Xᘁ : C) X).inv) ≫ (Xᘁ : C) ◁ (θ X).inv = _
  rw [Category.assoc]

/-- **The Ng–Schauenburg pivotal structure of a ribbon twist**: `j = θ u` with the canonical
dual comparisons. -/
def ribbonPivotal : Pivotal C where
  dualTensor := ribbonDualTensor
  dualTensor_eval := ribbonDualTensor_eval
  dualUnit := ribbonDualUnit
  dualUnit_eval := ribbonDualUnit_eval
  j := twistPivIso θ
  naturality := twistPiv_naturality hnat
  monoidal := twistPiv_monoidal θ hbal
  unit := twistPiv_unit θ hunit

theorem ribbonPivotal_j (X : C) : (ribbonPivotal θ hnat hbal hunit).j X = twistPivIso θ X := rfl

include hdual in
/-- **Sphericality of the ribbon pivotal structure.** -/
theorem ribbonPivotal_spherical : (ribbonPivotal θ hnat hbal hunit).IsSpherical := by
  intro X f
  simp only [Pivotal.traceLeft, Pivotal.traceRight, ribbonPivotal_j]
  rw [whiskerLeft_comp, Category.assoc, reassoc_of% (coevaluation_twistPivIso_inv θ X),
    ← whiskerLeft_comp_assoc, ← braiding_inv_naturality_left_assoc,
    braiding_inv_evaluation θ hnat hbal hunit hdual, twistPiv_evaluation]
  have h : (θ X).inv ≫ f ≫ (θ X).hom = f := by rw [hnat f, Iso.inv_hom_id_assoc]
  simp only [← comp_whiskerRight_assoc, Category.assoc]
  rw [reassoc_of% h]

/-- **The ribbon structure** on `ribbonPivotal`, with `j = θ u` (`Ribbon.pivotal`). -/
def ribbonOfTwist : Ribbon (ribbonPivotal θ hnat hbal hunit) where
  twist := θ
  naturality := hnat
  balance := hbal
  unit := hunit
  dual := hdual
  pivotal := twistPivIso_hom_eq θ

end Ribbon

end VOA.Huang.ZhuRep
