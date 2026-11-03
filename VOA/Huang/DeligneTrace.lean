/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianDim

/-!
# Deligne's theorem — the braided trace

In a braided category with right duals, the **braided trace** of `f : X ⟶ X` is
`trMor f = ε_X ∘ c_{X,Xᘁ} ∘ (f ⊗ 1) ∘ η_X ∈ End 𝟙`; `symDim X` is the scalar of `trMor (𝟙 X)`.

* `trWith`, `trWith_indep` — the trace may be computed with any exact pairing `(X, Y)`;
* `trMor_comp_comm` — cyclicity `tr (f ≫ g) = tr (g ≫ f)` (mates + naturality; no symmetry);
* `trMor_add`, `trMor_smul`, `trMor_zero`, `trMor_sum` — linearity;
* `trMor_id_of_iso` — isomorphic objects have the same dimension;
* `trMor_id_biproduct` — `dim (⨁ X_k) = Σ dim X_k`;
* `trMor_id_eq_zero_of_isZero` — the zero object has dimension `0`;
* `tensorPairing` — the exact pairing `(X ⊗ Y, Y' ⊗ X')` (Mathlib has no tensor of duals);
* `braiding_whiskerRight_cap`, `braiding_cap_right`, `braiding_tensorPairing_eval` — in a
  symmetric category the braided evaluation of `X ⊗ Y` is the nested one (Yang–Baxter + symmetry);
* `trWith_tensor` — **multiplicativity** `tr (f ⊗ g) = tr f · tr g` in a symmetric category.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The braided trace of `f : X ⟶ X` computed with the exact pairing `p : (X, Y)`. -/
def trWith {X Y : C} (p : ExactPairing X Y) (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  p.coevaluation' ≫ f ▷ Y ≫ (β_ X Y).hom ≫ p.evaluation'

/-- The braided trace does not depend on the chosen exact pairing. -/
theorem trWith_indep {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
    (f : X ⟶ X) : trWith p₁ f = trWith p₂ f := by
  let u : Y₁ ⟶ Y₂ := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  have hη : η_ X Y₁ ≫ X ◁ u = η_ X Y₂ := by
    have := @coevaluation_comp_rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
    simpa using this
  have hε : (u ▷ X) ≫ ε_ X Y₂ = ε_ X Y₁ := by
    have := @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
    simpa using this
  change η_ X Y₁ ≫ f ▷ Y₁ ≫ (β_ X Y₁).hom ≫ ε_ X Y₁ = η_ X Y₂ ≫ f ▷ Y₂ ≫ (β_ X Y₂).hom ≫ ε_ X Y₂
  rw [← hη, ← hε, Category.assoc, ← BraidedCategory.braiding_naturality_right_assoc,
    ← whisker_exchange_assoc]

variable [RightRigidCategory C]

/-- The braided trace `ε_X ∘ c_{X,Xᘁ} ∘ (f ⊗ 1) ∘ η_X`. -/
def trMor {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

theorem trMor_eq_trWith {X : C} (f : X ⟶ X) {Y : C} (p : ExactPairing X Y) :
    trMor f = trWith p f :=
  trWith_indep (inferInstance : ExactPairing X Xᘁ) p f

theorem trMor_id (X : C) : trMor (𝟙 X) = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  simp [trMor]

/-- **Cyclicity** of the braided trace. -/
theorem trMor_comp_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    trMor (f ≫ g) = trMor (g ≫ f) := by
  unfold trMor
  -- move `g ▷ Xᘁ` through the braiding and the evaluation
  have h1 : g ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (β_ Y Xᘁ).hom ≫ (gᘁ ▷ Y) ≫ ε_ Y Yᘁ := by
    rw [BraidedCategory.braiding_naturality_left_assoc, rightAdjointMate_comp_evaluation]
  have h2 : (β_ Y Xᘁ).hom ≫ (gᘁ ▷ Y) = Y ◁ gᘁ ≫ (β_ Y Yᘁ).hom := by
    rw [BraidedCategory.braiding_naturality_right]
  rw [comp_whiskerRight, Category.assoc, h1, ← Category.assoc ((β_ Y Xᘁ).hom), h2,
    Category.assoc, ← whisker_exchange_assoc, ← Category.assoc (η_ X Xᘁ),
    coevaluation_comp_rightAdjointMate, comp_whiskerRight]
  simp only [Category.assoc]

end Braided

section Linear

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C] [RightRigidCategory C]

theorem trMor_add {X : C} (f g : X ⟶ X) : trMor (f + g) = trMor f + trMor g := by
  simp [trMor, MonoidalPreadditive.add_whiskerRight]

theorem trMor_zero (X : C) : trMor (0 : X ⟶ X) = 0 := by
  simp [trMor]

theorem trMor_smul {X : C} (c : ℂ) (f : X ⟶ X) : trMor (c • f) = c • trMor f := by
  simp [trMor, MonoidalLinear.smul_whiskerRight]

theorem trMor_sum {X : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ X)) :
    trMor (∑ i ∈ s, f i) = ∑ i ∈ s, trMor (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trMor_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, trMor_add, ih]

/-- Isomorphic objects have the same braided dimension. -/
theorem trMor_id_of_iso {X Y : C} (e : X ≅ Y) : trMor (𝟙 X) = trMor (𝟙 Y) := by
  rw [← e.hom_inv_id, trMor_comp_comm, e.inv_hom_id]

theorem trMor_conj {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) : trMor (e.hom ≫ f ≫ e.inv) = trMor f := by
  rw [trMor_comp_comm, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- The braided dimension of a zero object is `0`. -/
theorem trMor_id_eq_zero_of_isZero {X : C} (hX : IsZero X) : trMor (𝟙 X) = 0 := by
  rw [hX.eq_of_src (𝟙 X) 0, trMor_zero]

/-- **Additivity**: `dim (⨁ X_k) = Σ_k dim X_k`. -/
theorem trMor_id_biproduct {J : Type} [Fintype J] (f : J → C) [HasBiproduct f] :
    trMor (𝟙 (⨁ f)) = ∑ j, trMor (𝟙 (f j)) := by
  rw [← biproduct.total, trMor_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trMor_comp_comm, biproduct.ι_π_self]

/-- Additivity along an isomorphism `X ≅ ⨁ X_k`. -/
theorem trMor_id_of_iso_biproduct {X : C} {J : Type} [Fintype J] {f : J → C} [HasBiproduct f]
    (e : X ≅ ⨁ f) : trMor (𝟙 X) = ∑ j, trMor (𝟙 (f j)) := by
  rw [trMor_id_of_iso e, trMor_id_biproduct]

end Linear

/-! ## The tensor product of exact pairings and multiplicativity -/

section Pairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The exact pairing `(X ⊗ Y, Y' ⊗ X')` built from exact pairings `(X, X')` and `(Y, Y')`
(nested cups and caps). -/
@[implicit_reducible]
def tensorPairing (X X' Y Y' : C) [ExactPairing X X'] [ExactPairing Y Y'] :
    ExactPairing (X ⊗ Y) (Y' ⊗ X') where
  coevaluation' := η_ X X' ⊗≫ X ◁ η_ Y Y' ▷ X' ⊗≫ 𝟙 _
  evaluation' := 𝟙 _ ⊗≫ Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y'
  evaluation_coevaluation' := by
    calc
      _ = 𝟙 _ ⊗≫ η_ X X' ▷ X ▷ Y ⊗≫ ((X ◁ η_ Y Y') ▷ ((X' ⊗ X) ⊗ Y) ≫
            (X ⊗ (Y ⊗ Y')) ◁ (ε_ X X' ▷ Y)) ⊗≫ X ◁ Y ◁ ε_ Y Y' ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (η_ X X' ▷ X ⊗≫ X ◁ ε_ X X') ▷ Y ⊗≫ X ◁ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation'', ExactPairing.evaluation_coevaluation'']; monoidal
  coevaluation_evaluation' := by
    calc
      _ = 𝟙 _ ⊗≫ Y' ◁ X' ◁ η_ X X' ⊗≫ ((Y' ⊗ (X' ⊗ X)) ◁ (η_ Y Y' ▷ X') ≫
            (Y' ◁ ε_ X X') ▷ ((Y ⊗ Y') ⊗ X')) ⊗≫ ε_ Y Y' ▷ Y' ▷ X' ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ Y' ◁ (X' ◁ η_ X X' ⊗≫ ε_ X X' ▷ X') ⊗≫ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ▷ X' ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation'', ExactPairing.coevaluation_evaluation'']; monoidal

/-- Tensor powers `X^{⊗n}` (`X^{⊗0} = 𝟙`, `X^{⊗(n+1)} = X^{⊗n} ⊗ X`, left-nested). -/
@[reducible] def tpow (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => tpow X n ⊗ X

end Pairing

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- In a symmetric category, sliding a cap `h : A ⊗ B ⟶ 𝟙` under a strand `Z`. -/
theorem braiding_whiskerRight_cap {A B : C} (Z : C) (h : A ⊗ B ⟶ 𝟙_ C) :
    (β_ A Z).hom ▷ B ⊗≫ Z ◁ h = 𝟙 _ ⊗≫ A ◁ (β_ Z B).hom ⊗≫ h ▷ Z ⊗≫ 𝟙 _ := by
  have hb : (β_ A Z).hom ▷ B = 𝟙 _ ⊗≫ A ◁ (β_ Z B).hom ⊗≫ (β_ (A ⊗ B) Z).hom ⊗≫ 𝟙 _ := by
    have hs : A ◁ (β_ Z B).hom ≫ A ◁ (β_ B Z).hom = 𝟙 _ := by
      rw [← whiskerLeft_comp, SymmetricCategory.symmetry, whiskerLeft_id]
    rw [BraidedCategory.braiding_tensor_left_hom]
    simp [monoidalComp, reassoc_of% hs]
  have hn := BraidedCategory.braiding_naturality_left h Z
  calc
    _ = 𝟙 _ ⊗≫ A ◁ (β_ Z B).hom ⊗≫ ((β_ (A ⊗ B) Z).hom ≫ Z ◁ h) ⊗≫ 𝟙 _ := by
      rw [hb]; monoidal
    _ = _ := by
      rw [← hn]; simp; monoidal


/-- Sliding a cap `h : A ⊗ B ⟶ 𝟙` past a braiding on its right. -/
theorem braiding_cap_right {A B : C} (W : C) (h : A ⊗ B ⟶ 𝟙_ C) :
    (β_ (A ⊗ B) W).hom ≫ W ◁ h = h ▷ W ⊗≫ 𝟙 _ := by
  rw [← BraidedCategory.braiding_naturality_left]; simp; monoidal

/-- In a symmetric category the braided evaluation of the tensor pairing is the nested one. -/
theorem braiding_tensorPairing_eval (X X' Y Y' : C) [ExactPairing X X'] [ExactPairing Y Y'] :
    (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫ (𝟙 _ ⊗≫ Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y') =
      𝟙 _ ⊗≫ X ◁ ((β_ Y Y').hom ≫ ε_ Y Y') ▷ X' ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
  rw [BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom X Y' X',
    BraidedCategory.braiding_tensor_right_hom Y Y' X']
  calc
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y Y').hom ▷ X' ⊗≫ Y' ◁ (β_ Y X').hom) ⊗≫
          ((β_ X Y').hom ▷ X' ⊗≫ Y' ◁ ((β_ X X').hom ≫ ε_ X X')) ▷ Y ⊗≫ ε_ Y Y' := by
      monoidal
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ Y Y').hom ▷ X' ⊗≫ Y' ◁ (β_ Y X').hom ⊗≫ (β_ Y' X').hom ▷ Y) ⊗≫
          ((β_ X X').hom ≫ ε_ X X') ▷ Y' ▷ Y ⊗≫ ε_ Y Y' := by
      rw [braiding_whiskerRight_cap]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ Y' X').hom ⊗≫ (β_ Y X').hom ▷ Y') ⊗≫
          ((X ⊗ X') ◁ (β_ Y Y').hom ≫ ((β_ X X').hom ≫ ε_ X X') ▷ (Y' ⊗ Y)) ⊗≫ ε_ Y Y' := by
      rw [BraidedCategory.yang_baxter']; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ Y' X').hom ⊗≫ (β_ Y X').hom ▷ Y') ⊗≫
          (((β_ X X').hom ≫ ε_ X X') ▷ (Y ⊗ Y') ≫ 𝟙_ C ◁ ((β_ Y Y').hom ≫ ε_ Y Y')) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ (β_ Y' X').hom ⊗≫ (β_ Y X').hom ▷ Y') ⊗≫
          ((X ⊗ X') ◁ ((β_ Y Y').hom ≫ ε_ Y Y') ≫ ((β_ X X').hom ≫ ε_ X X') ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ X ◁ ((β_ (Y ⊗ Y') X').hom ≫ X' ◁ ((β_ Y Y').hom ≫ ε_ Y Y')) ⊗≫
          ((β_ X X').hom ≫ ε_ X X') := by
      rw [BraidedCategory.braiding_tensor_left_hom]; monoidal
    _ = _ := by
      rw [braiding_cap_right]; monoidal

end Symmetric

section SymmetricLinear

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]

/-- **Multiplicativity of the braided trace** in a symmetric category. -/
theorem trWith_tensor {X X' Y Y' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y')
    (f : X ⟶ X) (g : Y ⟶ Y) {c : ℂ} (hg : trWith pY g = c • 𝟙 (𝟙_ C)) :
    trWith (tensorPairing X X' Y Y') (f ⊗ₘ g) = c • trWith pX f := by
  have hg' : η_ Y Y' ≫ g ▷ Y' ≫ (β_ Y Y').hom ≫ ε_ Y Y' = c • 𝟙 (𝟙_ C) := hg
  have hev := braiding_tensorPairing_eval X X' Y Y'
  change (η_ X X' ⊗≫ X ◁ η_ Y Y' ▷ X' ⊗≫ 𝟙 _) ≫ (f ⊗ₘ g) ▷ (Y' ⊗ X') ≫
      (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫ (𝟙 _ ⊗≫ Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y') =
    c • (η_ X X' ≫ f ▷ X' ≫ (β_ X X').hom ≫ ε_ X X')
  rw [hev, tensorHom_def]
  calc
    _ = η_ X X' ⊗≫ (X ◁ (η_ Y Y' ▷ X') ≫ f ▷ ((Y ⊗ Y') ⊗ X')) ⊗≫ X ◁ (g ▷ Y' ▷ X') ⊗≫
          X ◁ ((β_ Y Y').hom ≫ ε_ Y Y') ▷ X' ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
      monoidal
    _ = η_ X X' ⊗≫ (f ▷ (𝟙_ C ⊗ X') ≫ X ◁ (η_ Y Y' ▷ X')) ⊗≫ X ◁ (g ▷ Y' ▷ X') ⊗≫
          X ◁ ((β_ Y Y').hom ≫ ε_ Y Y') ▷ X' ⊗≫ (β_ X X').hom ≫ ε_ X X' := by
      rw [whisker_exchange]
    _ = η_ X X' ⊗≫ f ▷ X' ⊗≫ X ◁ ((η_ Y Y' ≫ g ▷ Y' ≫ (β_ Y Y').hom ≫ ε_ Y Y') ▷ X') ⊗≫
          (β_ X X').hom ≫ ε_ X X' := by
      monoidal
    _ = _ := by
      rw [hg']
      simp only [MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul, monoidalComp,
        Linear.smul_comp, Linear.comp_smul]
      congr 1
      monoidal

end SymmetricLinear

end VOA.Huang.TensorCat
