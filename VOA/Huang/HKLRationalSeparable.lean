/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Separable algebras in a monoidal category: the Maschke averaging argument

Pure monoidal category theory (Mathlib only), the categorical half of Kirillov–Ostrik 2002
Thm 3.3 (semisimplicity of `Rep A` for a rigid algebra with `dim A ≠ 0`).

## Layer 1: averaging with a separability idempotent

A morphism `e : 𝟙 ⟶ A ⊗ A` is a **separability idempotent** for the monoid `A` if it is
**central** (`a e¹ ⊗ e² = e¹ ⊗ e² a`, `IsCentralCopairing`) and **normalized** (`e ≫ μ = η`).
For left `A`-modules `(X, aX)`, `(Y, aY)` and any morphism `h : X ⟶ Y` of `C` the average

  `avg e aX aY h = λ⁻¹ ≫ (e ▷ X) ≫ α ≫ (A ◁ (aX ≫ h)) ≫ aY`        (`x ↦ e¹ · h(e² · x)`)

is `A`-linear (`avg_isLinear`), equals `h` when `h` is already `A`-linear (`avg_of_isLinear`), and
is compatible with `A`-linear pre/post-composition.  Hence

* `exists_linear_retraction` — **Maschke**: an `A`-linear morphism with a retraction in `C`
  has an `A`-linear retraction;
* `exists_linear_section` — an `A`-linear morphism with a section in `C` has an `A`-linear
  section; in particular every module is an `A`-linear retract of the free module `A ⊗ X`
  (`act_isLinear_free`, `exists_linear_section_act`).

## Layer 2: Frobenius counits in a braided category

For a **commutative** monoid in a braided category and `q : A ⟶ 𝟙` with a copairing `c`
satisfying the single zig-zag identity of `IsFrobeniusCounit` (`VOA/Huang/HKLExtRigid.lean`):

* `zigzag₂_braid` — the other zig-zag holds for `c ≫ β` (braiding naturality + hexagons; uses
  `p ∘ β^{±1} = p` for `p = μ ≫ q`);
* `copairing_unique` — copairings are unique, so `c ≫ β = c` and both zig-zags hold for `c`;
* `isCentral_of_frobenius` — the copairing is central.

## Layer 3: normalization

`exists_linear_retraction_of_frobenius` — over a field `𝕜`, if `c ≫ μ = t • η` with
`t ≠ 0` (for haploid `A` this is `dim A ≠ 0`), then `t⁻¹ • c` is a separability idempotent and
Maschke holds for `A`-modules.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory BraidedCategory Category

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ## Layer 1 -/

section Averaging

variable {A : C} [MonObj A]

/-- `act : A ⊗ X ⟶ X` is a left `A`-module structure (Mathlib's `ModObj` axioms, unbundled). -/
structure IsLeftAct {X : C} (act : A ⊗ X ⟶ X) : Prop where
  one_act : (MonObj.one ▷ X) ≫ act = (λ_ X).hom
  mul_act : (MonObj.mul ▷ X) ≫ act = (α_ A A X).hom ≫ (A ◁ act) ≫ act

/-- `f : X ⟶ Y` is `A`-linear for the actions `aX`, `aY`. -/
def IsLinear {X Y : C} (aX : A ⊗ X ⟶ X) (aY : A ⊗ Y ⟶ Y) (f : X ⟶ Y) : Prop :=
  (A ◁ f) ≫ aY = aX ≫ f

/-- `e` is **central**: `a e¹ ⊗ e² = e¹ ⊗ e² a`, as maps `A ⟶ A ⊗ A`. -/
def IsCentralCopairing (A : C) [MonObj A] (e : 𝟙_ C ⟶ A ⊗ A) : Prop :=
  (ρ_ A).inv ≫ (A ◁ e) ≫ (α_ A A A).inv ≫ (MonObj.mul ▷ A) =
    (λ_ A).inv ≫ (e ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ MonObj.mul)

/-- The **average** of `h : X ⟶ Y` along `e`: `x ↦ e¹ · h(e² · x)`. -/
def avg (e : 𝟙_ C ⟶ A ⊗ A) {X Y : C} (aX : A ⊗ X ⟶ X) (aY : A ⊗ Y ⟶ Y) (h : X ⟶ Y) :
    X ⟶ Y :=
  (λ_ X).inv ≫ (e ▷ X) ≫ (α_ A A X).hom ≫ (A ◁ (aX ≫ h)) ≫ aY

theorem isLinear_id {X : C} (aX : A ⊗ X ⟶ X) : IsLinear aX aX (𝟙 X) := by
  simp [IsLinear]

theorem isLinear_comp {X Y Z : C} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y} {aZ : A ⊗ Z ⟶ Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsLinear aX aY f) (hg : IsLinear aY aZ g) :
    IsLinear aX aZ (f ≫ g) := by
  unfold IsLinear at *
  rw [MonoidalCategory.whiskerLeft_comp, assoc, hg, ← assoc, hf, assoc]

variable (e : 𝟙_ C ⟶ A ⊗ A)

/-- An `A`-linear map is its own average. -/
theorem avg_of_isLinear (hn : e ≫ MonObj.mul = MonObj.one) {X Y : C} {aX : A ⊗ X ⟶ X}
    {aY : A ⊗ Y ⟶ Y} (hX : IsLeftAct aX) {h : X ⟶ Y} (hh : IsLinear aX aY h) :
    avg e aX aY h = h := by
  unfold avg
  unfold IsLinear at hh
  rw [MonoidalCategory.whiskerLeft_comp, assoc, hh, reassoc_of% hX.mul_act.symm,
    ← comp_whiskerRight_assoc, hn, reassoc_of% hX.one_act, Iso.inv_hom_id_assoc]

/-- Pre-composition by an `A`-linear map. -/
theorem comp_avg {X' X Y : C} {aX' : A ⊗ X' ⟶ X'} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y}
    {f : X' ⟶ X} (hf : IsLinear aX' aX f) (h : X ⟶ Y) :
    f ≫ avg e aX aY h = avg e aX' aY (f ≫ h) := by
  unfold avg
  unfold IsLinear at hf
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← assoc (A ◁ f), hf, assoc]

/-- Post-composition by an `A`-linear map. -/
theorem avg_comp {X Y Z : C} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y} {aZ : A ⊗ Z ⟶ Z}
    {g : Y ⟶ Z} (hg : IsLinear aY aZ g) (h : X ⟶ Y) :
    avg e aX aY h ≫ g = avg e aX aZ (h ≫ g) := by
  unfold avg
  unfold IsLinear at hg
  simp only [assoc]
  rw [← hg, ← MonoidalCategory.whiskerLeft_comp_assoc, assoc]

/-- The left action of `a` on an average, rewritten through `a e¹ ⊗ e²`. -/
theorem whiskerLeft_avg_act {X Y : C} (aX : A ⊗ X ⟶ X) {aY : A ⊗ Y ⟶ Y} (hY : IsLeftAct aY)
    (h : X ⟶ Y) :
    (A ◁ avg e aX aY h) ≫ aY =
      (((ρ_ A).inv ≫ (A ◁ e) ≫ (α_ A A A).inv ≫ (MonObj.mul ▷ A)) ▷ X) ≫ (α_ A A X).hom ≫
        (A ◁ (aX ≫ h)) ≫ aY := by
  unfold avg
  generalize aX ≫ h = k
  have key : (A ◁ (A ◁ k)) ≫ (A ◁ aY) ≫ aY =
      (α_ A A (A ⊗ X)).inv ≫ (MonObj.mul ▷ (A ⊗ X)) ≫ (A ◁ k) ≫ aY := by
    have hm := hY.mul_act
    rw [← Iso.inv_comp_eq] at hm
    rw [← hm, ← whisker_exchange_assoc, associator_inv_naturality_right_assoc]
  have hs : (A ◁ (λ_ X).inv) ≫ (A ◁ (e ▷ X)) ≫ (A ◁ (α_ A A X).hom) ≫ (α_ A A (A ⊗ X)).inv ≫
      (MonObj.mul ▷ (A ⊗ X)) =
      (((ρ_ A).inv ≫ (A ◁ e) ≫ (α_ A A A).inv ≫ (MonObj.mul ▷ A)) ▷ X) ≫ (α_ A A X).hom := by
    monoidal
  simp only [MonoidalCategory.whiskerLeft_comp, assoc]
  rw [key, reassoc_of% hs]

/-- An average after the action, rewritten through `e¹ ⊗ e² a`. -/
theorem act_avg {X Y : C} {aX : A ⊗ X ⟶ X} (hX : IsLeftAct aX) (aY : A ⊗ Y ⟶ Y)
    (h : X ⟶ Y) :
    aX ≫ avg e aX aY h =
      (((λ_ A).inv ≫ (e ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ MonObj.mul)) ▷ X) ≫ (α_ A A X).hom ≫
        (A ◁ (aX ≫ h)) ≫ aY := by
  have hm := hX.mul_act
  rw [← Iso.inv_comp_eq] at hm
  unfold avg
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, associator_naturality_right_assoc]
  have h2 : (A ◁ (A ◁ aX)) ≫ (A ◁ (aX ≫ h)) =
      (A ◁ ((α_ A A X).inv ≫ (MonObj.mul ▷ X))) ≫ (A ◁ (aX ≫ h)) := by
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, ← assoc,
      ← assoc, assoc _ _ aX, hm]
  have hs : (λ_ (A ⊗ X)).inv ≫ (e ▷ (A ⊗ X)) ≫ (α_ A A (A ⊗ X)).hom ≫
      (A ◁ ((α_ A A X).inv ≫ (MonObj.mul ▷ X))) =
      (((λ_ A).inv ≫ (e ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ MonObj.mul)) ▷ X) ≫ (α_ A A X).hom := by
    monoidal
  rw [reassoc_of% h2, reassoc_of% hs]

/-- **Averages are `A`-linear** (for a central `e`). -/
theorem avg_isLinear (hc : IsCentralCopairing A e) {X Y : C} {aX : A ⊗ X ⟶ X}
    {aY : A ⊗ Y ⟶ Y} (hX : IsLeftAct aX) (hY : IsLeftAct aY) (h : X ⟶ Y) :
    IsLinear aX aY (avg e aX aY h) := by
  unfold IsLinear
  rw [whiskerLeft_avg_act e aX hY, act_avg e hX aY, hc]

/-- **Maschke for a separable algebra**: an `A`-linear `f : Y ⟶ X` with a retraction `r` in
`C` has an `A`-linear retraction. -/
theorem exists_linear_retraction (hc : IsCentralCopairing A e) (hn : e ≫ MonObj.mul = MonObj.one)
    {X Y : C} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y} (hX : IsLeftAct aX) (hY : IsLeftAct aY)
    {f : Y ⟶ X} (hf : IsLinear aY aX f) {r : X ⟶ Y} (hr : f ≫ r = 𝟙 Y) :
    ∃ r' : X ⟶ Y, IsLinear aX aY r' ∧ f ≫ r' = 𝟙 Y :=
  ⟨avg e aX aY r, avg_isLinear e hc hX hY r, by
    rw [comp_avg e hf, hr, avg_of_isLinear e hn hY (isLinear_id aY)]⟩

/-- **Dual Maschke**: an `A`-linear `g : X ⟶ Y` with a section `s` in `C` has an `A`-linear
section. -/
theorem exists_linear_section (hc : IsCentralCopairing A e) (hn : e ≫ MonObj.mul = MonObj.one)
    {X Y : C} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y} (hX : IsLeftAct aX) (hY : IsLeftAct aY)
    {g : X ⟶ Y} (hg : IsLinear aX aY g) {s : Y ⟶ X} (hs : s ≫ g = 𝟙 Y) :
    ∃ s' : Y ⟶ X, IsLinear aY aX s' ∧ s' ≫ g = 𝟙 Y :=
  ⟨avg e aY aX s, avg_isLinear e hc hY hX s, by
    rw [avg_comp e hg, hs, avg_of_isLinear e hn hY (isLinear_id aY)]⟩

/-- The free module `A ⊗ X`, with action `α⁻¹ ≫ (μ ▷ X)`. -/
theorem isLeftAct_free (X : C) :
    IsLeftAct ((α_ A A X).inv ≫ (MonObj.mul ▷ X)) := by
  constructor
  · have h := MonObj.one_mul A
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, h]
    monoidal
  · have h := MonObj.mul_assoc A
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, h]
    monoidal

end Averaging


/-! ## Layer 2 -/

section Frobenius

variable {A : C}

/-- The zig-zag identity of `IsFrobeniusCounit` (`A ⟶ A ⊗ A ⊗ A ⟶ A`). -/
def Zig₁ (c : 𝟙_ C ⟶ A ⊗ A) (p : A ⊗ A ⟶ 𝟙_ C) : Prop :=
  (λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ p) ≫ (ρ_ A).hom = 𝟙 A

/-- The other zig-zag identity. -/
def Zig₂ (c : 𝟙_ C ⟶ A ⊗ A) (p : A ⊗ A ⟶ 𝟙_ C) : Prop :=
  (ρ_ A).inv ≫ (A ◁ c) ≫ (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom = 𝟙 A

/-- **Copairings are unique**: `Zig₁ c p` and `Zig₂ c' p` force `c = c'`. -/
theorem copairing_unique {c c' : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (h₁ : Zig₁ c p)
    (h₂ : Zig₂ c' p) : c = c' := by
  unfold Zig₁ at h₁
  unfold Zig₂ at h₂
  have key : c ≫ (ρ_ (A ⊗ A)).inv ≫ ((A ⊗ A) ◁ c') =
      c' ≫ (λ_ (A ⊗ A)).inv ≫ (c ▷ (A ⊗ A)) := by
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange, leftUnitor_inv_naturality_assoc,
      unitors_inv_equal]
  set P : (A ⊗ A) ⊗ (A ⊗ A) ⟶ A ⊗ A := (α_ A A (A ⊗ A)).hom ≫ (A ◁ (α_ A A A).inv) ≫
    (A ◁ (p ▷ A)) ≫ (A ◁ (λ_ A).hom) with hP
  have hL : c ≫ (A ◁ ((ρ_ A).inv ≫ (A ◁ c') ≫ (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom)) =
      c ≫ (ρ_ (A ⊗ A)).inv ≫ ((A ⊗ A) ◁ c') ≫ P := by
    rw [hP]; monoidal
  have hR : c' ≫ (((λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ p) ≫ (ρ_ A).hom) ▷ A) =
      c' ≫ (λ_ (A ⊗ A)).inv ≫ (c ▷ (A ⊗ A)) ≫ P := by
    rw [hP]; monoidal
  rw [h₂, MonoidalCategory.whiskerLeft_id, comp_id] at hL
  rw [h₁, id_whiskerRight, comp_id] at hR
  calc c = c ≫ (ρ_ (A ⊗ A)).inv ≫ ((A ⊗ A) ◁ c') ≫ P := hL
    _ = c' ≫ (λ_ (A ⊗ A)).inv ≫ (c ▷ (A ⊗ A)) ≫ P := by rw [reassoc_of% key]
    _ = c' := hR.symm

/-- **Injectivity from `Zig₁`**: a map `g : X ⟶ A ⊗ A` is recovered from its left contraction
`(A ◁ g) ≫ α⁻¹ ≫ (p ▷ A) ≫ λ : A ⊗ X ⟶ A`. -/
theorem eq_of_zig₁ {c : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (h₁ : Zig₁ c p) {X : C}
    (g : X ⟶ A ⊗ A) :
    g = (λ_ X).inv ≫ (c ▷ X) ≫ (α_ A A X).hom ≫
      (A ◁ ((A ◁ g) ≫ (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom)) := by
  unfold Zig₁ at h₁
  set P : (A ⊗ A) ⊗ (A ⊗ A) ⟶ A ⊗ A := (α_ A A (A ⊗ A)).hom ≫ (A ◁ (α_ A A A).inv) ≫
    (A ◁ (p ▷ A)) ≫ (A ◁ (λ_ A).hom) with hP
  have hR : (((λ_ A).inv ≫ (c ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ p) ≫ (ρ_ A).hom) ▷ A) =
      (λ_ (A ⊗ A)).inv ≫ (c ▷ (A ⊗ A)) ≫ P := by
    rw [hP]; monoidal
  rw [h₁, id_whiskerRight] at hR
  have hX : (λ_ X).inv ≫ (c ▷ X) ≫ (α_ A A X).hom ≫
      (A ◁ ((A ◁ g) ≫ (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom)) =
      (λ_ X).inv ≫ (c ▷ X) ≫ ((A ⊗ A) ◁ g) ≫ P := by
    rw [hP]; monoidal
  rw [hX, ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc, ← hR, comp_id]

/-- **Central copairing**: if `Zig₁ c p`, `Zig₂ c p` and `p` is invariant
(`p(a, bc) = p(ab, c)`), then `c` is central. -/
theorem isCentral_of_zig [MonObj A] {c : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (h₁ : Zig₁ c p)
    (h₂ : Zig₂ c p)
    (hinv : (A ◁ MonObj.mul) ≫ p = (α_ A A A).inv ≫ (MonObj.mul ▷ A) ≫ p) :
    IsCentralCopairing A c := by
  unfold IsCentralCopairing
  have hK : (A ◁ ((ρ_ A).inv ≫ (A ◁ c) ≫ (α_ A A A).inv ≫ (MonObj.mul ▷ A))) ≫
      (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom = MonObj.mul := by
    unfold Zig₂ at h₂
    calc _ = (A ◁ (ρ_ A).inv) ≫ (A ◁ (A ◁ c)) ≫ (A ◁ (α_ A A A).inv) ≫
          (α_ A (A ⊗ A) A).inv ≫ (((A ◁ MonObj.mul) ≫ p) ▷ A) ≫ (λ_ A).hom := by monoidal
      _ = (A ◁ (ρ_ A).inv) ≫ (A ◁ (A ◁ c)) ≫ (A ◁ (α_ A A A).inv) ≫
          (α_ A (A ⊗ A) A).inv ≫ (((α_ A A A).inv ≫ (MonObj.mul ▷ A) ≫ p) ▷ A) ≫
            (λ_ A).hom := by rw [hinv]
      _ = (ρ_ (A ⊗ A)).inv ≫ ((A ⊗ A) ◁ c) ≫ (MonObj.mul ▷ (A ⊗ A)) ≫ (α_ A A A).inv ≫
          (p ▷ A) ≫ (λ_ A).hom := by monoidal
      _ = MonObj.mul ≫ (ρ_ A).inv ≫ (A ◁ c) ≫ (α_ A A A).inv ≫ (p ▷ A) ≫ (λ_ A).hom := by
          rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
      _ = MonObj.mul := by rw [h₂, comp_id]
  conv_lhs => rw [eq_of_zig₁ h₁ ((ρ_ A).inv ≫ (A ◁ c) ≫ (α_ A A A).inv ≫ (MonObj.mul ▷ A)), hK]

section Braided

variable [BraidedCategory C]

theorem rightUnitor_inv_braiding_inv (X : C) :
    (ρ_ X).inv ≫ (β_ (𝟙_ C) X).inv = (λ_ X).inv := by
  rw [← cancel_epi (λ_ X).hom, ← braiding_rightUnitor]
  simp

/-- **The other zig-zag, after braiding**: in a braided category, `Zig₁ c p` for a pairing
invariant under the braiding gives `Zig₂ (c ≫ β) p`. -/
theorem zig₂_braid {c : 𝟙_ C ⟶ A ⊗ A} {p : A ⊗ A ⟶ 𝟙_ C} (hp : (β_ A A).hom ≫ p = p)
    (h₁ : Zig₁ c p) : Zig₂ (c ≫ (β_ A A).hom) p := by
  unfold Zig₁ at h₁
  unfold Zig₂
  have hpi : (β_ A A).inv ≫ p = p := by
    conv_lhs => rw [← hp]
    rw [Iso.inv_hom_id_assoc]
  have ha : (λ_ A).inv ≫ (c ▷ A) = (ρ_ A).inv ≫ (A ◁ c) ≫ (β_ (A ⊗ A) A).inv := by
    rw [braiding_inv_naturality_right, ← assoc, rightUnitor_inv_braiding_inv]
  have hc : (A ◁ p) ≫ (ρ_ A).hom = (β_ A (A ⊗ A)).hom ≫ (p ▷ A) ≫ (λ_ A).hom := by
    rw [← braiding_leftUnitor, ← braiding_naturality_right_assoc]
  rw [← assoc, ha] at h₁
  simp only [braiding_tensor_left_inv, assoc, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hpi] at h₁
  rw [hc] at h₁
  simp only [braiding_tensor_right_hom, assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    inv_hom_whiskerRight_assoc] at h₁
  simpa only [MonoidalCategory.whiskerLeft_comp, assoc] using h₁

/-- **A Frobenius copairing of a commutative algebra is central and two-sided**: in a braided
category, for `A` commutative and `c` satisfying the zig-zag of `IsFrobeniusCounit` for
`p = μ ≫ q`, both zig-zags hold for `c` and `c` is central. -/
theorem isCentral_of_frobenius [MonObj A] [IsCommMonObj A] {q : A ⟶ 𝟙_ C}
    {c : 𝟙_ C ⟶ A ⊗ A} (h₁ : Zig₁ c (MonObj.mul ≫ q)) :
    Zig₂ c (MonObj.mul ≫ q) ∧ IsCentralCopairing A c := by
  have hp : (β_ A A).hom ≫ MonObj.mul ≫ q = MonObj.mul ≫ q := by
    rw [← assoc, IsCommMonObj.mul_comm]
  have h₂' := zig₂_braid hp h₁
  have hcc : c = c ≫ (β_ A A).hom := copairing_unique h₁ h₂'
  rw [← hcc] at h₂'
  refine ⟨h₂', isCentral_of_zig h₁ h₂' ?_⟩
  have h := MonObj.mul_assoc A
  rw [reassoc_of% h, Iso.inv_hom_id_assoc]

end Braided

end Frobenius

/-! ## Layer 3: normalization over a field -/

section Linear

variable {𝕜 : Type*} [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] {A : C} [MonObj A]

/-- Rescaling a central copairing keeps it central. -/
theorem isCentral_smul {c : 𝟙_ C ⟶ A ⊗ A} (hc : IsCentralCopairing A c) (s : 𝕜) :
    IsCentralCopairing A (s • c) := by
  unfold IsCentralCopairing at *
  simp only [MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
    Linear.comp_smul, hc]

/-- If `c ≫ μ = t • η` with `t ≠ 0`, then `t⁻¹ • c` is normalized. -/
theorem smul_inv_normalized {c : 𝟙_ C ⟶ A ⊗ A} {t : 𝕜} (ht : t ≠ 0)
    (hct : c ≫ MonObj.mul = t • MonObj.one) : (t⁻¹ • c) ≫ MonObj.mul = MonObj.one := by
  rw [Linear.smul_comp, hct, smul_smul, inv_mul_cancel₀ ht, one_smul]

variable [BraidedCategory C] [IsCommMonObj A]

/-- **Kirillov–Ostrik Maschke** (KO 2002 Thm 3.3, the categorical core): for a commutative
algebra `A` in a braided `𝕜`-linear monoidal category with a Frobenius counit `q` (copairing `c`,
zig-zag `Zig₁ c (μ ≫ q)`) and `c ≫ μ = t • η`, `t ≠ 0` (for haploid `A`: `dim A ≠ 0`), every
`A`-linear map with a retraction in `C` has an `A`-linear retraction. -/
theorem exists_linear_retraction_of_frobenius {q : A ⟶ 𝟙_ C} {c : 𝟙_ C ⟶ A ⊗ A}
    (h₁ : Zig₁ c (MonObj.mul ≫ q)) {t : 𝕜} (ht : t ≠ 0)
    (hct : c ≫ MonObj.mul = t • MonObj.one) {X Y : C} {aX : A ⊗ X ⟶ X} {aY : A ⊗ Y ⟶ Y}
    (hX : IsLeftAct aX) (hY : IsLeftAct aY) {f : Y ⟶ X} (hf : IsLinear aY aX f) {r : X ⟶ Y}
    (hr : f ≫ r = 𝟙 Y) : ∃ r' : X ⟶ Y, IsLinear aX aY r' ∧ f ≫ r' = 𝟙 Y :=
  exists_linear_retraction (t⁻¹ • c) (isCentral_smul (isCentral_of_frobenius h₁).2 t⁻¹)
    (smul_inv_normalized ht hct) hX hY hf hr

/-- **Every module is a retract of a free module** (same hypotheses): the action
`A ⊗ X ⟶ X` has an `A`-linear section from the free module. -/
theorem exists_linear_section_act_of_frobenius {q : A ⟶ 𝟙_ C} {c : 𝟙_ C ⟶ A ⊗ A}
    (h₁ : Zig₁ c (MonObj.mul ≫ q)) {t : 𝕜} (ht : t ≠ 0)
    (hct : c ≫ MonObj.mul = t • MonObj.one) {X : C} {aX : A ⊗ X ⟶ X} (hX : IsLeftAct aX) :
    ∃ s : X ⟶ A ⊗ X, IsLinear aX ((α_ A A X).inv ≫ (MonObj.mul ▷ X)) s ∧ s ≫ aX = 𝟙 X := by
  refine exists_linear_section (t⁻¹ • c) (isCentral_smul (isCentral_of_frobenius h₁).2 t⁻¹)
    (smul_inv_normalized ht hct) (isLeftAct_free X) hX (g := aX) ?_ (s := (λ_ X).inv ≫
      (MonObj.one ▷ X)) ?_
  · unfold IsLinear
    rw [assoc, hX.mul_act, Iso.inv_hom_id_assoc]
  · rw [assoc, hX.one_act, Iso.inv_hom_id]

end Linear

end VOA.Huang.HKLRational
