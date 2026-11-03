import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Abstract rigidity lemmas (monoidal category theory only)

* `snake_eval` — in any monoidal category, for `η : 𝟙 ⟶ X ⊗ Y`, `ε : Y ⊗ X ⟶ 𝟙`, with
  `f` the zig-zag endomorphism of `X` and `g` that of `Y`: `(g ▷ X) ≫ ε = (Y ◁ f) ≫ ε`.
* `exactPairingOfZigzag` — in a `ℂ`-linear monoidal category: if the `X`-zig-zag is the
  identity, the `Y`-zig-zag is a scalar, and `ε ≠ 0`, then `(η, ε)` is an exact pairing.
* `exactPairingBiproduct` — duals of finite biproducts in a monoidal preadditive category.
* `rightRigidOfDecomposition` — if every object is isomorphic to a finite biproduct of
  objects with right duals, the category is right rigid.
-/

noncomputable section

namespace VOA.Huang.HuangRigid

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe v u

section Snake

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The zig-zag endomorphism of `X`. -/
def zigX {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) : X ⟶ X :=
  (λ_ X).inv ≫ η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom

/-- The zig-zag endomorphism of `Y`. -/
def zigY {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) : Y ⟶ Y :=
  (ρ_ Y).inv ≫ Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom

/-- The snake identity: both zig-zags give the same pairing. -/
theorem snake_eval {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    (zigY η ε ▷ X) ≫ ε = (Y ◁ zigX η ε) ≫ ε := by
  let E0 : Y ⊗ X ⟶ (Y ⊗ X) ⊗ (Y ⊗ X) :=
    (ρ_ Y).inv ▷ X ≫ (Y ◁ η) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom
  have hA : (zigY η ε ▷ X) ≫ ε = E0 ≫ (ε ▷ (Y ⊗ X)) ≫ (𝟙_ C ◁ ε) ≫ (λ_ (𝟙_ C)).hom := by
    simp only [zigY, E0]
    monoidal
  have hB : (Y ◁ zigX η ε) ≫ ε = E0 ≫ ((Y ⊗ X) ◁ ε) ≫ (ε ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom := by
    simp only [zigX, E0]
    monoidal
  rw [hA, hB, ← whisker_exchange_assoc, unitors_equal]

theorem zigX_eq_id_iff {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    zigX η ε = 𝟙 X ↔ η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε = (λ_ X).hom ≫ (ρ_ X).inv := by
  constructor
  · intro h
    have := congrArg (fun k => (λ_ X).hom ≫ k ≫ (ρ_ X).inv) h
    simpa [zigX] using this
  · intro h
    simp only [zigX]
    rw [reassoc_of% h]
    simp

theorem zigY_eq_id_iff {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    zigY η ε = 𝟙 Y ↔ Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv := by
  constructor
  · intro h
    have := congrArg (fun k => (ρ_ Y).hom ≫ k ≫ (λ_ Y).inv) h
    simpa [zigY] using this
  · intro h
    simp only [zigY]
    rw [reassoc_of% h]
    simp

end Snake

section Linear

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- If the `X`-zig-zag is the identity and the `Y`-zig-zag is a scalar, the scalar is `1`
(provided `ε ≠ 0`). -/
theorem zigY_scalar_eq_one {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (h1 : zigX η ε = 𝟙 X) (t : ℂ) (h2 : zigY η ε = t • 𝟙 Y) (hε : ε ≠ 0) : t = 1 := by
  have h := snake_eval η ε
  rw [h1, h2, MonoidalLinear.smul_whiskerRight, id_whiskerRight, whiskerLeft_id,
    Linear.smul_comp, Category.id_comp] at h
  have h0 : (t - 1) • ε = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with ht | ht
  · exact (sub_eq_zero.mp ht)
  · exact absurd ht hε

/-- **An exact pairing from one exact zig-zag, one scalar zig-zag and `ε ≠ 0`.** -/
@[implicit_reducible]
def exactPairingOfZigzag {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (h1 : zigX η ε = 𝟙 X) (t : ℂ) (h2 : zigY η ε = t • 𝟙 Y) (hε : ε ≠ 0) :
    ExactPairing X Y where
  coevaluation' := η
  evaluation' := ε
  coevaluation_evaluation' := by
    have ht := zigY_scalar_eq_one η ε h1 t h2 hε
    rw [ht, one_smul] at h2
    exact (zigY_eq_id_iff η ε).mp h2
  evaluation_coevaluation' := (zigX_eq_id_iff η ε).mp h1

end Linear

section Biproduct

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]
variable {J : Type} [Fintype J] (f g : J → C) [∀ j, ExactPairing (f j) (g j)]

/-- Coevaluation of the biproduct pairing. -/
def coevBiprod : 𝟙_ C ⟶ (⨁ f) ⊗ (⨁ g) :=
  ∑ j, η_ (f j) (g j) ≫ (biproduct.ι f j ⊗ₘ biproduct.ι g j)

/-- Evaluation of the biproduct pairing. -/
def evBiprod : (⨁ g) ⊗ (⨁ f) ⟶ 𝟙_ C :=
  ∑ j, (biproduct.π g j ⊗ₘ biproduct.π f j) ≫ ε_ (f j) (g j)

theorem whiskerLeft_ι_evBiprod (j : J) :
    ((⨁ g) ◁ biproduct.ι f j) ≫ evBiprod f g = (biproduct.π g j ▷ f j) ≫ ε_ (f j) (g j) := by
  simp only [evBiprod, Preadditive.comp_sum]
  rw [Finset.sum_eq_single j]
  · rw [whiskerLeft_comp_tensorHom_assoc, biproduct.ι_π_self, tensorHom_id]
  · intro m _ hm
    rw [whiskerLeft_comp_tensorHom_assoc, biproduct.ι_π_ne _ (Ne.symm hm),
      MonoidalPreadditive.tensor_zero, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem ι_whiskerRight_evBiprod (j : J) :
    (biproduct.ι g j ▷ (⨁ f)) ≫ evBiprod f g = (g j ◁ biproduct.π f j) ≫ ε_ (f j) (g j) := by
  simp only [evBiprod, Preadditive.comp_sum]
  rw [Finset.sum_eq_single j]
  · rw [whiskerRight_comp_tensorHom_assoc, biproduct.ι_π_self, id_tensorHom]
  · intro m _ hm
    rw [whiskerRight_comp_tensorHom_assoc, biproduct.ι_π_ne _ (Ne.symm hm),
      MonoidalPreadditive.zero_tensor, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem coevBiprod_whiskerLeft_π (j : J) :
    coevBiprod f g ≫ ((⨁ f) ◁ biproduct.π g j) = η_ (f j) (g j) ≫ (biproduct.ι f j ▷ g j) := by
  simp only [coevBiprod, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [tensorHom_comp_whiskerLeft, biproduct.ι_π_self, tensorHom_id]
  · intro m _ hm
    rw [tensorHom_comp_whiskerLeft, biproduct.ι_π_ne _ hm,
      MonoidalPreadditive.tensor_zero, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem coevBiprod_π_whiskerRight (j : J) :
    coevBiprod f g ≫ (biproduct.π f j ▷ (⨁ g)) = η_ (f j) (g j) ≫ (f j ◁ biproduct.ι g j) := by
  simp only [coevBiprod, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [tensorHom_comp_whiskerRight, biproduct.ι_π_self, id_tensorHom]
  · intro m _ hm
    rw [tensorHom_comp_whiskerRight, biproduct.ι_π_ne _ hm,
      MonoidalPreadditive.zero_tensor, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem evaluation_coevaluation_biprod :
    coevBiprod f g ▷ (⨁ f) ≫ (α_ _ _ _).hom ≫ (⨁ f) ◁ evBiprod f g =
      (λ_ (⨁ f)).hom ≫ (ρ_ (⨁ f)).inv := by
  apply leftDistributor_ext_left
  intro j
  rw [whisker_exchange_assoc, associator_naturality_right_assoc, ← whiskerLeft_comp,
    whiskerLeft_ι_evBiprod, whiskerLeft_comp, ← associator_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, coevBiprod_whiskerLeft_π, comp_whiskerRight_assoc,
    associator_naturality_left_assoc, ← whisker_exchange,
    ExactPairing.evaluation_coevaluation_assoc]
  simp

theorem coevaluation_evaluation_biprod :
    (⨁ g) ◁ coevBiprod f g ≫ (α_ _ _ _).inv ≫ evBiprod f g ▷ (⨁ g) =
      (ρ_ (⨁ g)).hom ≫ (λ_ (⨁ g)).inv := by
  apply rightDistributor_ext_left
  intro j
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    ι_whiskerRight_evBiprod, comp_whiskerRight, ← associator_inv_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, coevBiprod_π_whiskerRight, whiskerLeft_comp_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange,
    ExactPairing.coevaluation_evaluation_assoc]
  simp

/-- **Duals of finite biproducts.** -/
@[implicit_reducible]
def exactPairingBiprod : ExactPairing (⨁ f) (⨁ g) where
  coevaluation' := coevBiprod f g
  evaluation' := evBiprod f g
  coevaluation_evaluation' := coevaluation_evaluation_biprod f g
  evaluation_coevaluation' := evaluation_coevaluation_biprod f g

/-- **Right rigidity from a decomposition into dualizable objects.** -/
@[implicit_reducible]
def rightRigidOfDecomposition
    (h : ∀ X : C, ∃ (n : ℕ) (f : Fin n → C), (∀ j, Nonempty (HasRightDual (f j))) ∧
      Nonempty (X ≅ ⨁ f)) : RightRigidCategory C where
  rightDual X := by
    classical
    let n := (h X).choose
    let f := (h X).choose_spec.choose
    have hf := (h X).choose_spec.choose_spec
    letI : ∀ j, HasRightDual (f j) := fun j => (hf.1 j).some
    letI : ExactPairing (⨁ f) (⨁ fun j => (f j)ᘁ) := exactPairingBiprod f (fun j => (f j)ᘁ)
    exact { rightDual := ⨁ fun j => (f j)ᘁ
            exact := exactPairingCongrLeft hf.2.some }

end Biproduct

end VOA.Huang.HuangRigid
