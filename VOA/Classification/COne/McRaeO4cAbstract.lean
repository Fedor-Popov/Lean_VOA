/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO4bAbstract
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.CategoryTheory.Monoidal.Mod

/-! # O4c, abstract part: McRae's projections onto twisted summands (Theorem 3.3)

Pure category theory: McRae arXiv:1910.13226, Theorem 3.3 and its proof (Lemmas 3.6, 3.7 and
Appendix B), in a `ℂ`-linear braided monoidal category `C`.

## Setting (`McRaeData`)

`(A, m, u)` is a commutative algebra (`β_{A,A} ≫ m = m`) with a finite group `G` acting by
algebra automorphisms (`act (g * h) = act h ≫ act g`), an averaging map `e` with
`e ≫ u = |G|⁻¹ Σ_g act g`, and a coevaluation `ĩ : 𝟙 ⟶ A ⊗ A` with
`ĩ ≫ (1 ⊗ act g) ≫ m = δ_{g,1} |G| u` (the Galois form of Assumption 3.1 proved in O4b; it
implies both zigzags for `(A, m ≫ e, ĩ)` and `ĩ ≫ m = |G| u`).

Modules are `IsLeftModule m u a` for `a : A ⊗ X ⟶ X`, with Mathlib's `ModObj` axioms
(`isLeftModule_of_modObj`). The monodromy is `monodromy X Y = β_{X,Y} ≫ β_{Y,X}`, and McRae's
`g`-twisted condition (Def. 2.3) is `IsTwisted a g : M_{A,X} ≫ (g ⊗ 1) ≫ a = a`.

## McRae's projections

`bigProj ĩ a φ = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ M_{A,X}) ≫ (1 ⊗ (φ ⊗ 1)) ≫ (1 ⊗ a) ≫ a`
(`bigProj_eq`), and `proj = |G|⁻¹ • bigProj (act g)`.

* (1) `McRaeData.smul_proj`: `a ≫ π_g = (1 ⊗ π_g) ≫ a`.
* (2) `McRaeData.whiskerLeft_proj_twisted`: `(1 ⊗ π_g) ≫ M ≫ (g ⊗ 1) ≫ a = (1 ⊗ π_g) ≫ a`.
* (3) `McRaeData.proj_comp`: `π_g ≫ π_h = δ_{g,h} π_g`; `McRaeData.sum_proj`: `Σ_g π_g = 𝟙`.
* (4) `McRaeData.proj_natural`: module maps commute with every `π_g`.
* `McRaeData.proj_of_twisted`: on an `h`-twisted module, `π_g = δ_{g,h}`.
* `McRaeData.hom_eq_zero_of_twisted`: no nonzero maps between differently twisted modules.
* (5) `isLeftModule_induced`, `isModuleHom_induced`: induced modules `A ⊗ Y`.
* `McRaeData.theorem_3_3`: the bundled statement.

## Proof architecture (no braid diagrams)

* `braid_identity`: `(1 ⊗ M_{Z,X}) ≫ M_{Y,Z⊗X} = α⁻¹ ≫ M_{Y⊗Z,X} ≫ (M_{Y,Z} ⊗ 1) ≫ α`, the
  pure-braid relation `σ₂²σ₁σ₂²σ₁ = σ₂σ₁²σ₂σ₁²`, by two `yang_baxter` moves and `monoidal`.
* `monodromy_smul_assoc`: `a ∘ M` is again an associative action (braid identity +
  commutativity); `smul_monodromy_smul`: `a ∘ M` commutes with `a` up to `β_{A,A}`.
* `casimir_braid` (commutativity only) and `casimir_central` (McRae Lemma 3.7, from rigidity
  via `recover`, `pair_FL`, `pair_K`) move `A` across the Casimir element `ĩ`.
* `piOf_whiskerRight_smul` is the trace lemma (Lemma 3.8 form), and `McRaeData.coev_counit`
  is Lemma 3.6.

The orthogonality relation is proved without images (`LogModuleCat` has no cokernels): the
twisted-image identity (2) is used directly inside `bigProj_comp`.
-/

set_option linter.unusedSectionVars false

noncomputable section
namespace VOA.Classification.COne.McRaeO4c
open CategoryTheory MonoidalCategory BraidedCategory VOA.Classification.COne.McRaeO4b

universe v w
variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-! ## Monodromy -/

/-- The monodromy `M_{X,Y} = β_{Y,X} ∘ β_{X,Y} : X ⊗ Y ⟶ X ⊗ Y`. -/
def monodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y := (β_ X Y).hom ≫ (β_ Y X).hom

@[reassoc]
theorem monodromy_naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
    f ▷ Y ≫ monodromy X' Y = monodromy X Y ≫ f ▷ Y := by
  simp only [monodromy, braiding_naturality_left_assoc, braiding_naturality_right,
    Category.assoc]

@[reassoc]
theorem monodromy_naturality_right (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    X ◁ f ≫ monodromy X Y' = monodromy X Y ≫ X ◁ f := by
  simp only [monodromy, braiding_naturality_right_assoc, braiding_naturality_left,
    Category.assoc]

theorem monodromy_tensorUnit_left (Y : C) : monodromy (𝟙_ C) Y = 𝟙 _ := by
  simp only [monodromy, braiding_tensorUnit_left, braiding_tensorUnit_right, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- `M_{X, Y ⊗ Z}`: `X` passes `Y`, circles `Z`, and passes back. -/
theorem monodromy_tensor_right (X Y Z : C) :
    monodromy X (Y ⊗ Z) = (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
      Y ◁ monodromy X Z ≫ (α_ Y X Z).inv ≫ (β_ Y X).hom ▷ Z ≫ (α_ X Y Z).hom := by
  simp only [monodromy, braiding_tensor_left_hom, braiding_tensor_right_hom]
  monoidal

/-- **A pure-braid identity** (two Yang–Baxter moves): in the braid group on three strands,
`σ₂² σ₁ σ₂² σ₁ = σ₂ σ₁² σ₂ σ₁²` (time order). Categorically:
`(1 ⊗ M_{Z,X}) ≫ M_{Y, Z ⊗ X} = α⁻¹ ≫ M_{Y ⊗ Z, X} ≫ (M_{Y,Z} ⊗ 1) ≫ α`. -/
theorem braid_identity (Y Z X : C) :
    Y ◁ monodromy Z X ≫ monodromy Y (Z ⊗ X) =
      (α_ Y Z X).inv ≫ monodromy (Y ⊗ Z) X ≫ monodromy Y Z ▷ X ≫ (α_ Y Z X).hom := by
  have yb1 := yang_baxter Y X Z
  have yb2 := yang_baxter X Y Z
  have e1 : Y ◁ monodromy Z X ≫ monodromy Y (Z ⊗ X) =
      Y ◁ (β_ Z X).hom ≫ (Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫
        (α_ Z Y X).hom ≫ Z ◁ (β_ Y X).hom) ≫ Z ◁ (β_ X Y).hom ≫ (α_ Z Y X).inv ≫
        (β_ Z Y).hom ▷ X ≫ (α_ Y Z X).hom := by
    simp only [monodromy, braiding_tensor_left_hom, braiding_tensor_right_hom]
    monoidal
  have e2 : (α_ Y Z X).inv ≫ monodromy (Y ⊗ Z) X ≫ monodromy Y Z ▷ X ≫ (α_ Y Z X).hom =
      Y ◁ (β_ Z X).hom ≫ (α_ Y X Z).inv ≫ (β_ Y X).hom ▷ Z ≫ (α_ X Y Z).hom ≫
        ((α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫
          (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom) ≫
        (α_ Z Y X).inv ≫ (β_ Z Y).hom ▷ X ≫ (α_ Y Z X).hom := by
    simp only [monodromy, braiding_tensor_left_hom, braiding_tensor_right_hom]
    monoidal
  rw [e1, e2, ← yb1, yb2]
  simp only [Category.assoc]

/-! ## Modules over an algebra -/

section Module

variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A}

/-- A left module `(X, a)` over the algebra `(A, m, u)`, in the convention of Mathlib's
`ModObj`: `(u ⊗ 1) ≫ a = λ` and `(m ⊗ 1) ≫ a = α ≫ (1 ⊗ a) ≫ a`. -/
structure IsLeftModule (m : A ⊗ A ⟶ A) (u : 𝟙_ C ⟶ A) {X : C} (a : A ⊗ X ⟶ X) : Prop where
  one_smul : u ▷ X ≫ a = (λ_ X).hom
  mul_smul : m ▷ X ≫ a = (α_ A A X).hom ≫ A ◁ a ≫ a

/-- `f : X ⟶ Y` is a morphism of left `A`-modules: `a₁ ≫ f = (1 ⊗ f) ≫ a₂`. -/
def IsModuleHom {X Y : C} (a₁ : A ⊗ X ⟶ X) (a₂ : A ⊗ Y ⟶ Y) (f : X ⟶ Y) : Prop :=
  a₁ ≫ f = A ◁ f ≫ a₂

/-- McRae Def. 2.3: `(X, a)` is `φ`-twisted if `a ∘ (φ ⊗ 1) ∘ M_{A,X} = a`. -/
def IsTwisted {X : C} (a : A ⊗ X ⟶ X) (φ : A ⟶ A) : Prop :=
  monodromy A X ≫ φ ▷ X ≫ a = a

/-- Mathlib's `ModObj` (for the action of `C` on itself) gives an `IsLeftModule`. -/
theorem isLeftModule_of_modObj [MonObj A] (X : C) [ModObj A X] :
    IsLeftModule (MonObj.mul : A ⊗ A ⟶ A) MonObj.one (ModObj.smul (M := A) (X := X)) :=
  ⟨ModObj.one_smul (M := A) X, ModObj.mul_smul (M := A) X⟩

theorem IsLeftModule.assoc_inv {X : C} {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a) :
    A ◁ a ≫ a = (α_ A A X).inv ≫ m ▷ X ≫ a := by
  rw [hX.mul_smul, Iso.inv_hom_id_assoc]

@[reassoc]
theorem IsLeftModule.assoc_inv' {X : C} {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a) :
    A ◁ a ≫ a = (α_ A A X).inv ≫ m ▷ X ≫ a := hX.assoc_inv

/-- **Induced modules.** For an associative unital `(A, m, u)` and any object `Y`, `A ⊗ Y` is a
left `A`-module with action `α⁻¹ ≫ (m ⊗ 1)`. -/
theorem isLeftModule_induced (one_mul : u ▷ A ≫ m = (λ_ A).hom)
    (mul_assoc : m ▷ A ≫ m = (α_ A A A).hom ≫ A ◁ m ≫ m) (Y : C) :
    IsLeftModule m u ((α_ A A Y).inv ≫ m ▷ Y) where
  one_smul := by
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, one_mul]
    monoidal
  mul_smul := by
    have h : (m ▷ A ≫ m) ▷ Y = ((α_ A A A).hom ≫ A ◁ m ≫ m) ▷ Y := by rw [mul_assoc]
    have h1 : m ▷ (A ⊗ Y) ≫ (α_ A A Y).inv ≫ m ▷ Y =
        (α_ (A ⊗ A) A Y).inv ≫ (m ▷ A ≫ m) ▷ Y := by monoidal
    have h2 : (α_ A A (A ⊗ Y)).hom ≫ A ◁ ((α_ A A Y).inv ≫ m ▷ Y) ≫ (α_ A A Y).inv ≫ m ▷ Y =
        (α_ (A ⊗ A) A Y).inv ≫ ((α_ A A A).hom ≫ A ◁ m ≫ m) ▷ Y := by monoidal
    rw [h1, h2, h]

/-- `1 ⊗ f : A ⊗ Y ⟶ A ⊗ Y'` is a morphism of induced modules. -/
theorem isModuleHom_induced {Y Y' : C} (f : Y ⟶ Y') :
    IsModuleHom ((α_ A A Y).inv ≫ m ▷ Y) ((α_ A A Y').inv ≫ m ▷ Y') (A ◁ f) := by
  unfold IsModuleHom
  rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc]

end Module

/-! ## The monodromy action and its two key identities -/

section Monodromy

variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A} (hcomm : (β_ A A).hom ≫ m = m)
  {X : C} {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a)
include hcomm hX

/-- **The monodromy action is associative** (uses `braid_identity` and commutativity):
`(1 ⊗ (M ≫ a)) ≫ M ≫ a = α⁻¹ ≫ (m ⊗ 1) ≫ M ≫ a`. -/
theorem monodromy_smul_assoc :
    A ◁ (monodromy A X ≫ a) ≫ monodromy A X ≫ a =
      (α_ A A X).inv ≫ m ▷ X ≫ monodromy A X ≫ a := by
  have h1 : A ◁ (monodromy A X ≫ a) ≫ monodromy A X ≫ a =
      A ◁ monodromy A X ≫ monodromy A (A ⊗ X) ≫ A ◁ a ≫ a := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, monodromy_naturality_right_assoc]
  rw [h1, ← Category.assoc, braid_identity]
  simp only [Category.assoc]
  rw [← hX.mul_smul, ← comp_whiskerRight_assoc]
  have hmm : monodromy A A ≫ m = m := by
    rw [monodromy, Category.assoc, hcomm, hcomm]
  rw [hmm, ← monodromy_naturality_left_assoc]

/-- **The monodromy action commutes with the action, up to a braiding**:
`(1 ⊗ a) ≫ M ≫ a = α⁻¹ ≫ (β ⊗ 1) ≫ α ≫ (1 ⊗ (M ≫ a)) ≫ a`. -/
theorem smul_monodromy_smul :
    A ◁ a ≫ monodromy A X ≫ a =
      (α_ A A X).inv ≫ (β_ A A).hom ▷ X ≫ (α_ A A X).hom ≫ A ◁ (monodromy A X ≫ a) ≫ a := by
  rw [monodromy_naturality_right_assoc, monodromy_tensor_right]
  simp only [Category.assoc]
  rw [← hX.mul_smul, ← comp_whiskerRight_assoc, hcomm, hX.mul_smul, Iso.inv_hom_id_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc]

end Monodromy

/-! ## The twisted actions `θ_φ = M ≫ (φ ⊗ 1) ≫ a` -/

section Twist

variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A} {X : C}

/-- `θ_φ = M_{A,X} ≫ (φ ⊗ 1) ≫ a`, McRae's `μ_W (g ⊠ 1) M_{V,W}`. -/
def twistAct (a : A ⊗ X ⟶ X) (φ : A ⟶ A) : A ⊗ X ⟶ X :=
  monodromy A X ≫ φ ▷ X ≫ a

theorem twistAct_eq (a : A ⊗ X ⟶ X) (φ : A ⟶ A) :
    twistAct a φ = φ ▷ X ≫ monodromy A X ≫ a := by
  rw [twistAct, monodromy_naturality_left_assoc]

variable (hcomm : (β_ A A).hom ≫ m = m) {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a)
include hcomm hX

theorem smul_twistAct (φ : A ⟶ A) :
    A ◁ a ≫ twistAct a φ =
      (α_ A A X).inv ≫ (β_ A A).hom ▷ X ≫ (α_ A A X).hom ≫ A ◁ twistAct a φ ≫ a := by
  rw [twistAct_eq, whisker_exchange_assoc, smul_monodromy_smul hcomm hX,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

theorem twistAct_assoc (φ : A ⟶ A) (hφ : (φ ⊗ₘ φ) ≫ m = m ≫ φ) :
    A ◁ twistAct a φ ≫ twistAct a φ = (α_ A A X).inv ≫ m ▷ X ≫ twistAct a φ := by
  rw [twistAct_eq, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
    monodromy_smul_assoc hcomm hX]
  have h : A ◁ φ ▷ X ≫ φ ▷ (A ⊗ X) ≫ (α_ A A X).inv = (α_ A A X).inv ≫ (φ ⊗ₘ φ) ▷ X := by
    rw [tensorHom_def']
    monoidal
  rw [reassoc_of% h, ← comp_whiskerRight_assoc, hφ, comp_whiskerRight_assoc]

end Twist


/-! ## The maps `Π(θ) = μ_W ∘ (1 ⊠ θ) ∘ A⁻¹ ∘ (ĩ ⊠ 1) ∘ l⁻¹` -/

section Pi

variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A} {X : C}

/-- `Π(θ) = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ θ) ≫ a : X ⟶ X`. -/
def piOf (coev : 𝟙_ C ⟶ A ⊗ A) (a : A ⊗ X ⟶ X) (θ : A ⊗ X ⟶ X) : X ⟶ X :=
  (λ_ X).inv ≫ coev ▷ X ≫ (α_ A A X).hom ≫ A ◁ θ ≫ a

/-- McRae's `Π_φ = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ M_{A,X}) ≫ (1 ⊗ (φ ⊗ 1)) ≫ (1 ⊗ a) ≫ a`. -/
def bigProj (coev : 𝟙_ C ⟶ A ⊗ A) (a : A ⊗ X ⟶ X) (φ : A ⟶ A) : X ⟶ X :=
  piOf coev a (twistAct a φ)

theorem bigProj_eq (coev : 𝟙_ C ⟶ A ⊗ A) (a : A ⊗ X ⟶ X) (φ : A ⟶ A) :
    bigProj coev a φ = (λ_ X).inv ≫ coev ▷ X ≫ (α_ A A X).hom ≫ A ◁ monodromy A X ≫
      A ◁ (φ ▷ X) ≫ A ◁ a ≫ a := by
  simp only [bigProj, piOf, twistAct, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Precomposition: `f ≫ Π(θ) = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ ((1 ⊗ f) ≫ θ)) ≫ a`. -/
theorem comp_piOf (coev : 𝟙_ C ⟶ A ⊗ A) (a : A ⊗ X ⟶ X) (θ : A ⊗ X ⟶ X) {Y : C}
    (f : Y ⟶ X) :
    f ≫ piOf coev a θ =
      (λ_ Y).inv ≫ coev ▷ Y ≫ (α_ A A Y).hom ≫ A ◁ (A ◁ f ≫ θ) ≫ a := by
  rw [piOf, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, MonoidalCategory.whiskerLeft_comp_assoc]

variable (coev : 𝟙_ C ⟶ A ⊗ A) {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a)
include hX

/-- `(1 ⊗ Π(θ)) ≫ a = ((r⁻¹ ≫ (1 ⊗ ĩ) ≫ α⁻¹ ≫ (m ⊗ 1)) ⊗ 1) ≫ α ≫ (1 ⊗ θ) ≫ a`. -/
theorem whiskerLeft_piOf_smul (θ : A ⊗ X ⟶ X) :
    A ◁ piOf coev a θ ≫ a =
      ((ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A) ▷ X ≫ (α_ A A X).hom ≫ A ◁ θ ≫ a := by
  simp only [piOf, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [hX.assoc_inv, associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  monoidal

/-- If `θ` commutes with the action up to the braiding (as `θ_φ` does), then
`a ≫ Π(θ) = (K' ⊗ 1) ≫ α ≫ (1 ⊗ θ) ≫ a` with `K' = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ β) ≫ α⁻¹ ≫ (m ⊗ 1)`. -/
theorem smul_piOf (θ : A ⊗ X ⟶ X) (hθ : A ◁ a ≫ θ =
      (α_ A A X).inv ≫ (β_ A A).hom ▷ X ≫ (α_ A A X).hom ≫ A ◁ θ ≫ a) :
    a ≫ piOf coev a θ =
      ((λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ (β_ A A).hom ≫ (α_ A A A).inv ≫ m ▷ A) ▷ X ≫
        (α_ A A X).hom ≫ A ◁ θ ≫ a := by
  rw [comp_piOf, hθ]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [hX.assoc_inv, associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  monoidal

omit hX in
/-- If `θ` is associative (as `θ_φ` is), then
`θ ≫ Π(θ) = (F_L ⊗ 1) ≫ α ≫ (1 ⊗ θ) ≫ a` with `F_L = l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ m)`. -/
theorem twist_piOf (θ : A ⊗ X ⟶ X)
    (hθ : A ◁ θ ≫ θ = (α_ A A X).inv ≫ m ▷ X ≫ θ) :
    θ ≫ piOf coev a θ =
      ((λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ m) ▷ X ≫ (α_ A A X).hom ≫ A ◁ θ ≫ a := by
  rw [piOf, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hθ]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- **Trace lemma.** If `ĩ ≫ (1 ⊗ φ) ≫ m = c • u` then `Π((φ ⊗ 1) ≫ a) = c • 𝟙`. -/
theorem piOf_whiskerRight_smul [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
    [MonoidalLinear ℂ C] (φ : A ⟶ A) (c : ℂ) (hφ : coev ≫ A ◁ φ ≫ m = c • u) :
    piOf coev a (φ ▷ X ≫ a) = c • 𝟙 X := by
  rw [piOf, MonoidalCategory.whiskerLeft_comp_assoc, hX.assoc_inv]
  have h : coev ▷ X ≫ (α_ A A X).hom ≫ A ◁ φ ▷ X ≫ (α_ A A X).inv ≫ m ▷ X =
      (coev ≫ A ◁ φ ≫ m) ▷ X := by monoidal
  rw [reassoc_of% h, hφ, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul,
    hX.one_smul, Iso.inv_hom_id]

end Pi

/-! ## The Casimir identities (McRae Lemma 3.7 and its braided variant) -/

section Casimir

variable {A : C} {m : A ⊗ A ⟶ A} (coev : 𝟙_ C ⟶ A ⊗ A)

/-- **Braided Casimir identity** (commutativity only, no rigidity):
`l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ β) ≫ α⁻¹ ≫ (m ⊗ 1) = r⁻¹ ≫ (1 ⊗ ĩ) ≫ α⁻¹ ≫ (m ⊗ 1)`. -/
theorem casimir_braid (hcomm : (β_ A A).hom ≫ m = m) :
    (λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ (β_ A A).hom ≫ (α_ A A A).inv ≫ m ▷ A =
      (ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A := by
  conv_lhs => rw [← hcomm, comp_whiskerRight]
  have hb : (α_ A A A).hom ≫ A ◁ (β_ A A).hom ≫ (α_ A A A).inv ≫ (β_ A A).hom ▷ A =
      (β_ (A ⊗ A) A).hom ≫ (α_ A A A).inv := by
    rw [braiding_tensor_left_hom]; simp
  rw [reassoc_of% hb, braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc]

variable {e : A ⟶ 𝟙_ C}
  (Z1 : coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ (m ≫ e) = (λ_ A).hom ≫ (ρ_ A).inv)
  (Z2 : A ◁ coev ≫ (α_ A A A).inv ≫ (m ≫ e) ▷ A = (ρ_ A).hom ≫ (λ_ A).inv)

include Z1 in
/-- Rigidity: a map `F : A ⟶ A ⊗ A` is recovered from its pairing with the first leg. -/
theorem recover (F : A ⟶ A ⊗ A) :
    F = (λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫
      A ◁ (A ◁ F ≫ (α_ A A A).inv ≫ (m ≫ e) ▷ A ≫ (λ_ A).hom) := by
  symm
  rw [MonoidalCategory.whiskerLeft_comp, ← associator_naturality_right_assoc,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  have hz : (λ_ (A ⊗ A)).inv ≫ coev ▷ (A ⊗ A) ≫ (α_ A A (A ⊗ A)).hom ≫
      A ◁ ((α_ A A A).inv ≫ (m ≫ e) ▷ A ≫ (λ_ A).hom) =
      (λ_ (A ⊗ A)).inv ≫ (α_ (𝟙_ C) A A).inv ≫
        (coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ (m ≫ e)) ▷ A ≫
        (α_ A (𝟙_ C) A).hom ≫ A ◁ (λ_ A).hom := by
    monoidal
  rw [hz, Z1]
  have : (λ_ (A ⊗ A)).inv ≫ (α_ (𝟙_ C) A A).inv ≫ ((λ_ A).hom ≫ (ρ_ A).inv) ▷ A ≫
        (α_ A (𝟙_ C) A).hom ≫ A ◁ (λ_ A).hom = 𝟙 _ := by monoidal
  rw [this, Category.comp_id]

include Z2 in
theorem pair_FL :
    A ◁ ((λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ m) ≫ (α_ A A A).inv ≫
      (m ≫ e) ▷ A ≫ (λ_ A).hom = m := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]
  have hb : A ◁ (λ_ A).inv ≫ A ◁ coev ▷ A ≫ A ◁ (α_ A A A).hom ≫ (α_ A A (A ⊗ A)).inv ≫
      (m ≫ e) ▷ (A ⊗ A) ≫ (λ_ (A ⊗ A)).hom = 𝟙 _ := by
    have h : A ◁ (λ_ A).inv ≫ A ◁ coev ▷ A ≫ A ◁ (α_ A A A).hom ≫ (α_ A A (A ⊗ A)).inv ≫
        (m ≫ e) ▷ (A ⊗ A) ≫ (λ_ (A ⊗ A)).hom =
        ((ρ_ A).inv ≫ (A ◁ coev ≫ (α_ A A A).inv ≫ (m ≫ e) ▷ A) ≫ (λ_ A).hom) ▷ A := by
      monoidal
    rw [h, Z2]
    monoidal
  rw [reassoc_of% hb]

include Z2 in
theorem pair_K (mul_assoc : A ◁ m ≫ m = (α_ A A A).inv ≫ m ▷ A ≫ m) :
    A ◁ ((ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A) ≫ (α_ A A A).inv ≫
      (m ≫ e) ▷ A ≫ (λ_ A).hom = m := by
  have assoc4 : A ◁ (m ▷ A) ≫ (α_ A A A).inv ≫ m ▷ A =
      A ◁ (α_ A A A).hom ≫ (α_ A A (A ⊗ A)).inv ≫ m ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫ m ▷ A := by
    have h1 : A ◁ (m ▷ A) ≫ (α_ A A A).inv ≫ m ▷ A = (α_ A (A ⊗ A) A).inv ≫ (A ◁ m ≫ m) ▷ A := by
      monoidal
    have h2 : A ◁ (α_ A A A).hom ≫ (α_ A A (A ⊗ A)).inv ≫ m ▷ (A ⊗ A) ≫ (α_ A A A).inv ≫
        m ▷ A = (α_ A (A ⊗ A) A).inv ≫ ((α_ A A A).inv ≫ m ▷ A ≫ m) ▷ A := by
      monoidal
    rw [h1, h2, mul_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% assoc4, MonoidalCategory.whiskerLeft_inv_hom_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  have hb : A ◁ (ρ_ A).inv ≫ (α_ A A (𝟙_ C)).inv ≫ m ▷ 𝟙_ C ≫ A ◁ coev ≫ (α_ A A A).inv ≫
      m ▷ A ≫ e ▷ A ≫ (λ_ A).hom =
      m ≫ (ρ_ A).inv ≫ (A ◁ coev ≫ (α_ A A A).inv ≫ (m ≫ e) ▷ A) ≫ (λ_ A).hom := by
    monoidal
  rw [hb, Z2]
  simp

include Z1 Z2 in
/-- **McRae Lemma 3.7**: `l⁻¹ ≫ (ĩ ⊗ 1) ≫ α ≫ (1 ⊗ m) = r⁻¹ ≫ (1 ⊗ ĩ) ≫ α⁻¹ ≫ (m ⊗ 1)`
(uses rigidity of `A` and associativity). -/
theorem casimir_central (mul_assoc : A ◁ m ≫ m = (α_ A A A).inv ≫ m ▷ A ≫ m) :
    (λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ m =
      (ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A := by
  rw [recover coev Z1 ((λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ m),
    recover coev Z1 ((ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A),
    pair_FL coev Z2, pair_K coev Z2 mul_assoc]

end Casimir


/-! ## McRae's Assumption 3.1 and Theorem 3.3 -/

section Main

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- **McRae's Assumption 3.1** (minus the parity clause, vacuous for an even algebra), in the
Galois form established by O4b: `(A, m, u)` is a commutative algebra with a finite group `G`
of algebra automorphisms (`act (g * h) = act h ≫ act g`), `e ≫ u = |G|⁻¹ Σ_g act g`,
`u ≫ e = 1` is not needed, and `ĩ = coev` satisfies `ĩ ≫ (1 ⊗ g) ≫ m = δ_{g,1} |G| u`. By
`GaloisData.exactPairing` this makes `(A, m ≫ e, ĩ)` a dual of `A` with `ĩ ≫ m = |G| u`;
conversely McRae's Lemma 3.8 derives the Galois condition from rigidity, `dim A = |G|` and
haploidity. -/
structure McRaeData (A : C) (m : A ⊗ A ⟶ A) (u : 𝟙_ C ⟶ A) (e : A ⟶ 𝟙_ C)
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] (act : G → (A ⟶ A))
    (coev : 𝟙_ C ⟶ A ⊗ A) : Prop extends GaloisData A m u e G act where
  mul_comm : (β_ A A).hom ≫ m = m
  act_comp : ∀ g h, act (g * h) = act h ≫ act g
  coev_psi : ∀ g, coev ≫ A ◁ act g ≫ m = if g = 1 then (Fintype.card G : ℂ) • u else 0

namespace McRaeData

variable {A : C} {m : A ⊗ A ⟶ A} {u : 𝟙_ C ⟶ A} {e : A ⟶ 𝟙_ C}
  {G : Type*} [Group G] [Fintype G] [DecidableEq G] {act : G → (A ⟶ A)}
  {coev : 𝟙_ C ⟶ A ⊗ A} (D : McRaeData A m u e G act coev)
include D

/-- McRae Lemma 3.7 in this setting. -/
theorem casimir :
    (λ_ A).inv ≫ coev ▷ A ≫ (α_ A A A).hom ≫ A ◁ m =
      (ρ_ A).inv ≫ A ◁ coev ≫ (α_ A A A).inv ≫ m ▷ A :=
  casimir_central coev (D.evaluation_coevaluation coev D.coev_psi)
    (D.coevaluation_evaluation coev D.coev_psi) D.assoc_inv

theorem coev_psi' (g : G) :
    coev ≫ A ◁ act g ≫ m = (if g = 1 then (Fintype.card G : ℂ) else 0) • u := by
  rw [D.coev_psi]
  split_ifs <;> simp

/-- McRae Lemma 3.6 in this setting: `ĩ ≫ (1 ⊗ (e ≫ u)) ≫ m = u`. -/
theorem coev_counit : coev ≫ A ◁ (e ≫ u) ≫ m = u := by
  have h1 : ∑ g, coev ≫ A ◁ act g ≫ m = (Fintype.card G : ℂ) • u := by
    simp only [D.coev_psi, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∑ g, coev ≫ A ◁ act g ≫ m = coev ≫ A ◁ (∑ g, act g) ≫ m := by
    rw [whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  rw [h2, D.sum_act, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul] at h1
  have h3 := congrArg (fun f => (Fintype.card G : ℂ)⁻¹ • f) h1
  simpa only [smul_smul, inv_mul_cancel₀ D.card_ne_zero, one_smul] using h3

theorem piOf_smul {X : C} (a : A ⊗ X ⟶ X) (θ : A ⊗ X ⟶ X) (c : ℂ) :
    piOf coev a (c • θ) = c • piOf coev a θ := by
  simp only [piOf, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

variable {X : C} {a : A ⊗ X ⟶ X} (hX : IsLeftModule m u a)
include hX

/-- **(1) `Π_g` is a morphism of `A`-modules**: `a ≫ Π_g = (1 ⊗ Π_g) ≫ a`. -/
theorem smul_bigProj (g : G) :
    a ≫ bigProj coev a (act g) = A ◁ bigProj coev a (act g) ≫ a := by
  rw [bigProj, smul_piOf coev hX _ (smul_twistAct D.mul_comm hX _),
    whiskerLeft_piOf_smul coev hX, casimir_braid coev D.mul_comm]

theorem twistAct_bigProj (g : G) :
    twistAct a (act g) ≫ bigProj coev a (act g) = A ◁ bigProj coev a (act g) ≫ a := by
  rw [bigProj, twist_piOf coev _ (twistAct_assoc D.mul_comm hX _ (D.act_mul g)), D.casimir,
    ← whiskerLeft_piOf_smul coev hX]

/-- **(2) The image of `Π_g` is `g`-twisted**:
`(1 ⊗ Π_g) ≫ M_{A,X} ≫ (g ⊗ 1) ≫ a = (1 ⊗ Π_g) ≫ a`. -/
theorem whiskerLeft_bigProj_twisted (g : G) :
    A ◁ bigProj coev a (act g) ≫ monodromy A X ≫ act g ▷ X ≫ a =
      A ◁ bigProj coev a (act g) ≫ a := by
  rw [← D.twistAct_bigProj hX, twistAct, monodromy_naturality_right_assoc,
    whisker_exchange_assoc]
  simp only [Category.assoc]
  rw [D.smul_bigProj hX]

/-- On an `h`-twisted module, `Π_g = δ_{g,h} |G|`. -/
theorem bigProj_of_twisted (h : G) (htw : IsTwisted a (act h)) (g : G) :
    bigProj coev a (act g) = if g = h then (Fintype.card G : ℂ) • 𝟙 X else 0 := by
  unfold IsTwisted at htw
  have hg : act g = act (h⁻¹ * g) ≫ act h := by rw [← D.act_comp, mul_inv_cancel_left]
  have key : twistAct a (act g) = act (h⁻¹ * g) ▷ X ≫ a := by
    rw [twistAct, hg, comp_whiskerRight_assoc, ← monodromy_naturality_left_assoc, htw]
  rw [bigProj, key, piOf_whiskerRight_smul coev hX _ _ (D.coev_psi' _)]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg (by rwa [inv_mul_eq_one, eq_comm]), if_neg hgh, zero_smul]

/-- **(3a) Orthogonality**: `Π_h ≫ Π_g = δ_{g,h} |G| Π_h`. -/
theorem bigProj_comp (g h : G) :
    bigProj coev a (act h) ≫ bigProj coev a (act g) =
      if g = h then (Fintype.card G : ℂ) • bigProj coev a (act h) else 0 := by
  have hg : act g = act (h⁻¹ * g) ≫ act h := by rw [← D.act_comp, mul_inv_cancel_left]
  have e1 : A ◁ bigProj coev a (act h) ≫ twistAct a (act g) =
      act (h⁻¹ * g) ▷ X ≫ a ≫ bigProj coev a (act h) := by
    rw [twistAct, hg, comp_whiskerRight_assoc, monodromy_naturality_right_assoc,
      whisker_exchange_assoc, ← monodromy_naturality_left_assoc]
    congr 1
    rw [← monodromy_naturality_right_assoc, D.whiskerLeft_bigProj_twisted hX, D.smul_bigProj hX]
  have e2 : bigProj coev a (act h) ≫ bigProj coev a (act g) =
      piOf coev a (act (h⁻¹ * g) ▷ X ≫ a) ≫ bigProj coev a (act h) := by
    change bigProj coev a (act h) ≫ piOf coev a (twistAct a (act g)) = _
    rw [comp_piOf, e1, piOf]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [D.smul_bigProj hX]
  rw [e2, piOf_whiskerRight_smul coev hX _ _ (D.coev_psi' _), Linear.smul_comp,
    Category.id_comp]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg (by rwa [inv_mul_eq_one, eq_comm]), if_neg hgh, zero_smul]

/-- **(3b) Completeness**: `Σ_g Π_g = |G| • 𝟙`. -/
theorem sum_bigProj : ∑ g, bigProj coev a (act g) = (Fintype.card G : ℂ) • 𝟙 X := by
  have hsum : ∑ g, bigProj coev a (act g) =
      piOf coev a (monodromy A X ≫ (∑ g, act g) ▷ X ≫ a) := by
    simp only [bigProj, piOf, twistAct, sum_whiskerRight, Preadditive.sum_comp,
      Preadditive.comp_sum, whiskerLeft_sum]
  have htriv : monodromy A X ≫ (e ≫ u) ▷ X ≫ a = (e ≫ u) ▷ X ≫ a := by
    rw [comp_whiskerRight_assoc, ← monodromy_naturality_left_assoc, monodromy_tensorUnit_left,
      Category.id_comp]
  have h1 : coev ≫ A ◁ (e ≫ u) ≫ m = (1 : ℂ) • u := by rw [D.coev_counit, one_smul]
  rw [hsum, D.sum_act, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul,
    D.piOf_smul, htriv, piOf_whiskerRight_smul coev hX _ _ h1, one_smul]

/-! ### The normalized projections `π_g = |G|⁻¹ Π_g` -/

/-- McRae's projection `π_g = |G|⁻¹ Π_g` onto the `g`-twisted summand. -/
def proj (_D : McRaeData A m u e G act coev) (a : A ⊗ X ⟶ X) (g : G) : X ⟶ X :=
  (Fintype.card G : ℂ)⁻¹ • bigProj coev a (act g)

omit hX in
theorem proj_def (g : G) : D.proj a g = (Fintype.card G : ℂ)⁻¹ • bigProj coev a (act g) := rfl

/-- **(1)** `π_g` is a module map. -/
theorem smul_proj (g : G) : a ≫ D.proj a g = A ◁ D.proj a g ≫ a := by
  rw [proj, Linear.comp_smul, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp,
    D.smul_bigProj hX]

/-- **(2)** The image of `π_g` is `g`-twisted. -/
theorem whiskerLeft_proj_twisted (g : G) :
    A ◁ D.proj a g ≫ monodromy A X ≫ act g ▷ X ≫ a = A ◁ D.proj a g ≫ a := by
  rw [proj, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.smul_comp,
    D.whiskerLeft_bigProj_twisted hX]

/-- **(3a)** `π_g ≫ π_h = δ_{g,h} π_g`. -/
theorem proj_comp (g h : G) : D.proj a g ≫ D.proj a h = if g = h then D.proj a g else 0 := by
  rw [proj, proj, Linear.smul_comp, Linear.comp_smul, D.bigProj_comp hX h g]
  by_cases hgh : g = h
  · subst hgh
    rw [if_pos rfl, if_pos rfl, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ D.card_ne_zero, mul_one]
  · rw [if_neg (Ne.symm hgh), if_neg hgh, smul_zero, smul_zero]

/-- **(3b)** `Σ_g π_g = 𝟙`. -/
theorem sum_proj : ∑ g, D.proj a g = 𝟙 X := by
  simp only [proj]
  rw [← Finset.smul_sum, D.sum_bigProj hX, smul_smul, inv_mul_cancel₀ D.card_ne_zero, one_smul]

/-- On an `h`-twisted module, `π_g = δ_{g,h}`. -/
theorem proj_of_twisted (h : G) (htw : IsTwisted a (act h)) (g : G) :
    D.proj a g = if g = h then 𝟙 X else 0 := by
  rw [proj, D.bigProj_of_twisted hX h htw g]
  split_ifs
  · rw [smul_smul, inv_mul_cancel₀ D.card_ne_zero, one_smul]
  · rw [smul_zero]

omit hX in
/-- **(4) Naturality**: module maps commute with the projections. -/
theorem proj_natural {Y : C} {b : A ⊗ Y ⟶ Y} (f : X ⟶ Y) (hf : IsModuleHom a b f) (g : G) :
    D.proj a g ≫ f = f ≫ D.proj b g := by
  unfold IsModuleHom at hf
  have ht : twistAct a (act g) ≫ f = A ◁ f ≫ twistAct b (act g) := by
    rw [twistAct, twistAct, Category.assoc, Category.assoc, hf, ← whisker_exchange_assoc,
      ← monodromy_naturality_right_assoc]
  rw [proj, proj, Linear.smul_comp, Linear.comp_smul, bigProj, bigProj, comp_piOf, piOf]
  simp only [Category.assoc]
  rw [hf, ← MonoidalCategory.whiskerLeft_comp_assoc, ht]

omit hX in
/-- **Corollary 3.4 (Hom-vanishing)**: there are no nonzero module maps from a `g₁`-twisted
to a `g₂`-twisted module when `g₁ ≠ g₂`. -/
theorem hom_eq_zero_of_twisted {Y : C} {b : A ⊗ Y ⟶ Y} (hY : IsLeftModule m u b)
    (hX : IsLeftModule m u a) {g₁ g₂ : G} (h₁ : IsTwisted a (act g₁)) (h₂ : IsTwisted b (act g₂))
    (hne : g₁ ≠ g₂) (f : X ⟶ Y) (hf : IsModuleHom a b f) : f = 0 := by
  have e1 := D.proj_of_twisted hX g₁ h₁ g₁
  have e2 := D.proj_of_twisted hY g₂ h₂ g₁
  rw [if_pos rfl] at e1
  rw [if_neg hne] at e2
  rw [← Category.id_comp f, ← e1, D.proj_natural f hf, e2, Limits.comp_zero]

/-- **McRae, Theorem 3.3** (arXiv:1910.13226), in projection form. Under Assumption 3.1
(`McRaeData`), every left `A`-module `(X, a)` carries a complete family of orthogonal
idempotent module endomorphisms `π_g` (`g ∈ G`) whose images are `g`-twisted. -/
theorem theorem_3_3 :
    ∃ π : G → (X ⟶ X),
      (∀ g, a ≫ π g = A ◁ π g ≫ a) ∧
      (∀ g, A ◁ π g ≫ monodromy A X ≫ act g ▷ X ≫ a = A ◁ π g ≫ a) ∧
      (∀ g h, π g ≫ π h = if g = h then π g else 0) ∧
      ∑ g, π g = 𝟙 X :=
  ⟨D.proj a, D.smul_proj hX, D.whiskerLeft_proj_twisted hX, D.proj_comp hX, D.sum_proj hX⟩

end McRaeData

end Main

end VOA.Classification.COne.McRaeO4c
