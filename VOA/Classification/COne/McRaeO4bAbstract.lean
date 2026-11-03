/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # O4b, abstract part: Galois algebras in a monoidal category are self-dual

This file is pure category theory. It contains the categorical half of the rigidity proof for
McRae arXiv:1910.13226, Assumption 3.1. The argument is the Chase–Harrison–Rosenberg Galois
argument, written with morphisms.

## Setting

`C` is a `ℂ`-linear monoidal category. `A` is an algebra in `C` with:
- multiplication `m`, unit `u`, and a map `e : A ⟶ 𝟙`;
- an action `act` of a finite group `G` by algebra automorphisms;
- the condition `e ≫ u = |G|⁻¹ Σ_g act g`.

Write `ψ_g := A ◁ act g ≫ m : A ⊗ A ⟶ A`. On elements this is `a ⊗ b ↦ a · g(b)`.

## Results

* `GaloisData.exactPairing`: suppose `coev : 𝟙 ⟶ A ⊗ A` satisfies
  `coev ≫ ψ_g = if g = 1 then |G| • u else 0`. Then `(coev, m ≫ e)` is an exact pairing of `A`
  with itself. Both zigzag identities hold, and `coev ≫ m = |G| • u`.
* `GaloisData.unit_cancel`: a unit identity for the left action of `A` on `A ⊗ A`.
* `GaloisData.sum_theta`: an identity for `Σ_h (ψ_h ▷ (A ⊗ A)) ≫ α⁻¹ ≫ (ψ_h ▷ A)`. On elements
  it says `Σ_h a·h(b)·h(c) ⊗ d = Σ_y a ⊗ y(b)·y(c·y⁻¹(d))`. The right side factors through
  `(A ⊗ A) ◁ ψ_{y⁻¹}`.

`McRaeO4bInjective.lean` and `McRaeO4bRigid.lean` use `unit_cancel` and `sum_theta` to show that
the maps `ψ_g` are jointly injective on `V ⊠ V`.
-/

set_option linter.unusedSectionVars false

noncomputable section
namespace VOA.Classification.COne.McRaeO4b
open CategoryTheory MonoidalCategory

universe v w
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The data of a Galois algebra: an algebra `(A, m, u)` with a finite group of algebra
automorphisms `act` and an averaging map `e`. -/
structure GaloisData (A : C) (m : A ⊗ A ⟶ A) (u : 𝟙_ C ⟶ A) (e : A ⟶ 𝟙_ C)
    (G : Type*) [Group G] [Fintype G] (act : G → (A ⟶ A)) : Prop where
  one_mul : u ▷ A ≫ m = (λ_ A).hom
  mul_one : A ◁ u ≫ m = (ρ_ A).hom
  mul_assoc : m ▷ A ≫ m = (α_ A A A).hom ≫ A ◁ m ≫ m
  act_mul : ∀ g, (act g ⊗ₘ act g) ≫ m = m ≫ act g
  unit_act : ∀ g, u ≫ act g = u
  act_inv : ∀ g, act g⁻¹ ≫ act g = 𝟙 A
  act_one : act 1 = 𝟙 A
  counit : e ≫ u = (Fintype.card G : ℂ)⁻¹ • ∑ g, act g

namespace GaloisData
variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A} {e : A ⟶ 𝟙_ C}
  {G : Type*} [Group G] [Fintype G] {act : G → (A ⟶ A)}
  (D : GaloisData A m u e G act)
include D

theorem card_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- `A ◁ m ≫ m = α⁻¹ ≫ m ▷ A ≫ m`. -/
theorem assoc_inv : A ◁ m ≫ m = (α_ A A A).inv ≫ m ▷ A ≫ m := by
  rw [D.mul_assoc, Iso.inv_hom_id_assoc]

/-- The sum of the group action is `|G| • (e ≫ u)`. -/
theorem sum_act : ∑ g, act g = (Fintype.card G : ℂ) • (e ≫ u) := by
  rw [D.counit, smul_smul, mul_inv_cancel₀ D.card_ne_zero, one_smul]

/-- Moving `m ≫ g` in the second leg past a map into `A ⊗ A`. -/
theorem whisker_mul_act (g : G) {X : C} (c : X ⟶ A ⊗ A) :
    c ▷ A ≫ (α_ A A A).hom ≫ A ◁ (m ≫ act g) ≫ m =
      (c ≫ A ◁ act g ≫ m) ▷ A ≫ A ◁ act g ≫ m := by
  rw [← D.act_mul g, tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [D.assoc_inv, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← associator_naturality_middle_assoc, Iso.hom_inv_id_assoc]
  simp only [comp_whiskerRight, Category.assoc]

/-- `act g ▷ A = A ◁ act g⁻¹ ≫ (act g ⊗ act g)`. -/
theorem act_whiskerRight (g : G) :
    act g ▷ A = A ◁ act g⁻¹ ≫ (act g ⊗ₘ act g) := by
  rw [tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc, D.act_inv,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- `(e ≫ u)` whiskered on the left and multiplied is the average of the twisted products. -/
theorem whiskerLeft_counit_mul {X : C} (f : X ⟶ A) :
    (Fintype.card G : ℂ) • (A ◁ (f ≫ e) ≫ (ρ_ A).hom) = ∑ g, A ◁ (f ≫ act g) ≫ m := by
  rw [← D.mul_one, ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, D.counit,
    Linear.comp_smul, Preadditive.comp_sum, MonoidalLinear.whiskerLeft_smul, whiskerLeft_sum,
    Linear.smul_comp, Preadditive.sum_comp, smul_smul, mul_inv_cancel₀ D.card_ne_zero, one_smul]

/-- `(e ≫ u)` whiskered on the right and multiplied is the average of the twisted products. -/
theorem counit_whiskerRight_mul {X : C} (f : X ⟶ A) :
    (Fintype.card G : ℂ) • ((f ≫ e) ▷ A ≫ (λ_ A).hom) = ∑ g, (f ≫ act g) ▷ A ≫ m := by
  rw [← D.one_mul, ← comp_whiskerRight_assoc, Category.assoc, D.counit,
    Linear.comp_smul, Preadditive.comp_sum, MonoidalLinear.smul_whiskerRight, sum_whiskerRight,
    Linear.smul_comp, Preadditive.sum_comp, smul_smul, mul_inv_cancel₀ D.card_ne_zero, one_smul]

/-! ## The zigzag identities from a Galois coevaluation -/

variable [DecidableEq G] (coev : 𝟙_ C ⟶ A ⊗ A)
  (hcoev : ∀ g, coev ≫ A ◁ act g ≫ m =
    if g = 1 then (Fintype.card G : ℂ) • u else 0)
include hcoev

/-- `coev ≫ m = |G| • u`. -/
theorem coev_mul : coev ≫ m = (Fintype.card G : ℂ) • u := by
  have h := hcoev 1
  rw [D.act_one, MonoidalCategory.whiskerLeft_id, Category.id_comp, if_pos rfl] at h
  exact h

/-- The left-twisted products of `coev`. -/
theorem coev_whiskerRight_mul (g : G) :
    coev ≫ act g ▷ A ≫ m = if g = 1 then (Fintype.card G : ℂ) • u else 0 := by
  rw [D.act_whiskerRight, Category.assoc, D.act_mul, ← Category.assoc, ← Category.assoc,
    Category.assoc coev, hcoev g⁻¹]
  by_cases hg : g = 1
  · subst hg
    simp only [inv_one, if_true, Linear.smul_comp, D.unit_act]
  · rw [if_neg (by simpa using hg), if_neg hg, Limits.zero_comp]

/-- **First zigzag**: `(coev ▷ A) ≫ α ≫ (A ◁ (m ≫ e)) = λ ≫ ρ⁻¹`. -/
theorem evaluation_coevaluation :
    coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ (m ≫ e) = (λ_ A).hom ≫ (ρ_ A).inv := by
  rw [← cancel_mono (ρ_ A).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  have hc := D.card_ne_zero
  have h1 : A ◁ (m ≫ e) ≫ (ρ_ A).hom =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, A ◁ (m ≫ act g) ≫ m := by
    rw [← D.whiskerLeft_counit_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h1, Linear.comp_smul, Linear.comp_smul, Preadditive.comp_sum, Preadditive.comp_sum]
  simp only [D.whisker_mul_act, hcoev]
  rw [Finset.sum_eq_single (1 : G)]
  · rw [if_pos rfl, D.act_one, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp, D.one_mul, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  · intro g _ hg
    rw [if_neg hg, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Second zigzag**: `(A ◁ coev) ≫ α⁻¹ ≫ ((m ≫ e) ▷ A) = ρ ≫ λ⁻¹`. -/
theorem coevaluation_evaluation :
    A ◁ coev ≫ (α_ A A A).inv ≫ (m ≫ e) ▷ A = (ρ_ A).hom ≫ (λ_ A).inv := by
  rw [← cancel_mono (λ_ A).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  have hc := D.card_ne_zero
  have h1 : (m ≫ e) ▷ A ≫ (λ_ A).hom =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, (m ≫ act g) ▷ A ≫ m := by
    rw [← D.counit_whiskerRight_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : ∀ g : G, A ◁ coev ≫ (α_ A A A).inv ≫ (m ≫ act g) ▷ A ≫ m =
      act g ▷ 𝟙_ C ≫ A ◁ (coev ≫ act g ▷ A ≫ m) ≫ m := by
    intro g
    rw [← D.act_mul g, tensorHom_def]
    simp only [comp_whiskerRight, Category.assoc]
    rw [D.mul_assoc, associator_naturality_middle_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [whisker_exchange_assoc]
  rw [h1, Linear.comp_smul, Linear.comp_smul, Preadditive.comp_sum, Preadditive.comp_sum]
  simp only [h2, D.coev_whiskerRight_mul coev hcoev]
  rw [Finset.sum_eq_single (1 : G)]
  · rw [if_pos rfl, D.act_one, id_whiskerRight, Category.id_comp,
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, D.mul_one, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  · intro g _ hg
    rw [if_neg hg, MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Self-duality from a Galois coevaluation**: `A` is its own (left and right) dual, with
evaluation `m ≫ e` and coevaluation `coev`. -/
abbrev exactPairing : ExactPairing A A where
  coevaluation' := coev
  evaluation' := m ≫ e
  coevaluation_evaluation' := D.coevaluation_evaluation coev hcoev
  evaluation_coevaluation' := D.evaluation_coevaluation coev hcoev

omit hcoev in
/-- Unit law for the left action of `A` on `A ⊗ A`. -/
theorem unit_cancel :
    (λ_ (A ⊗ A)).inv ≫ u ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫ m ▷ A = 𝟙 (A ⊗ A) := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, D.one_mul]
  monoidal

omit hcoev in
/-- The two-fold twisted product, rewritten through the counit. -/
theorem theta_eq (h : G) :
    (A ◁ act h ≫ m) ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫ (A ◁ act h ≫ m) ▷ A =
      (α_ (A ⊗ A) A A).inv ≫ ((α_ A A A).hom ≫ A ◁ (m ≫ act h) ≫ m) ▷ A := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight]
  congr 2
  have := D.whisker_mul_act h (𝟙 (A ⊗ A))
  rw [id_whiskerRight, Category.id_comp, Category.id_comp] at this
  exact this.symm

omit hcoev in
/-- The `y`-twisted product with the third leg twisted back. -/
theorem twist_back (y : G) :
    (α_ A A A).inv ≫ (m ≫ act y) ▷ A ≫ m =
      A ◁ (A ◁ act y⁻¹ ≫ m) ≫ (act y ⊗ₘ act y) ≫ m := by
  have hinv : act y⁻¹ ≫ act y = 𝟙 A := D.act_inv y
  have hL : (α_ A A A).inv ≫ (m ≫ act y) ▷ A ≫ m =
      act y ▷ (A ⊗ A) ≫ A ◁ (act y ▷ A) ≫ A ◁ m ≫ m := by
    rw [← D.act_mul, tensorHom_def]
    simp only [comp_whiskerRight, Category.assoc]
    rw [D.mul_assoc, associator_naturality_middle_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc]
  have hm : A ◁ act y⁻¹ ≫ m ≫ act y = act y ▷ A ≫ m := by
    rw [← D.act_mul, tensorHom_def', Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      hinv, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hR : A ◁ (A ◁ act y⁻¹ ≫ m) ≫ (act y ⊗ₘ act y) ≫ m =
      act y ▷ (A ⊗ A) ≫ A ◁ (act y ▷ A ≫ m) ≫ m := by
    rw [tensorHom_def', Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc,
      hm, whisker_exchange_assoc]
  rw [hL, hR, MonoidalCategory.whiskerLeft_comp, Category.assoc]

omit hcoev in
/-- **The Θ identity.** On elements,
`Σ_h a·h(b)·h(c) ⊗ d = Σ_y a ⊗ y(b)·y(c·y⁻¹(d))`.
The right side factors through `(A ⊗ A) ◁ ψ_{y⁻¹}`. -/
theorem sum_theta :
    ∑ h, (A ◁ act h ≫ m) ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫ (A ◁ act h ≫ m) ▷ A =
      ∑ y, (A ⊗ A) ◁ (A ◁ act y⁻¹ ≫ m) ≫ (α_ A A A).hom ≫ A ◁ ((act y ⊗ₘ act y) ≫ m) := by
  simp only [D.theta_eq]
  rw [← Preadditive.comp_sum, ← sum_whiskerRight, ← Preadditive.comp_sum,
    ← D.whiskerLeft_counit_mul m]
  have hcoh : (α_ (A ⊗ A) A A).inv ≫
      ((α_ A A A).hom ≫ A ◁ (m ≫ e) ≫ (ρ_ A).hom) ▷ A =
      (α_ A A (A ⊗ A)).hom ≫ A ◁ ((α_ A A A).inv ≫ (m ≫ e) ▷ A ≫ (λ_ A).hom) := by
    monoidal
  rw [Linear.comp_smul, MonoidalLinear.smul_whiskerRight, Linear.comp_smul, hcoh,
    ← Linear.comp_smul, ← MonoidalLinear.whiskerLeft_smul, ← Linear.comp_smul,
    D.counit_whiskerRight_mul, Preadditive.comp_sum, whiskerLeft_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [D.twist_back y, MonoidalCategory.whiskerLeft_comp, ← associator_naturality_right_assoc]

end GaloisData

end VOA.Classification.COne.McRaeO4b
