/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberStrong
import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# Deligne's fiber functor — base change to a point and the frame-functor reduction

**The reduction.**  Deligne's proof of `SymmetricFiberFunctorExists` builds a commutative algebra
`A` in `Ind(D)` over which a generator `X` becomes free (`A ⊗ X ≅ A^n`), with `A ≠ 0`, and then
passes to a quotient with `Hom(𝟙, A) = ℂ`.  We encode `A` as the lax braided functor
`G Y = Hom(𝟙, A ⊗ Y)` (`DeligneFiberQuotient`), so no Ind-category is needed, and replace the
maximal ideal of `A` by a maximal ideal of the commutative ring `R = G 𝟙` (legitimate since only
freeness of `A ⊗ X` has to survive the quotient).  This file proves

* `FrameFunctorExists` (Prop) — for every symmetric fusion `D` with positive dimensions there is a
  lax braided, additive, `ℂ`-linear `G : D ⥤ ModuleCat ℂ`, an object `X` containing every simple
  as a retract, and `e : Fin n → G X`, such that `G 𝟙` is a **nonzero** ring of **countable**
  dimension and `(a_j) ↦ Σ_j e_j · a_j : G(Z)^n → G(X ⊗ Z)` is bijective for every `Z`
  (a *frame*: `A ⊗ X ≅ A^n` as `A`-modules);
* `symmetricFiberFunctorExists_of_frameFunctorExists` — `FrameFunctorExists →
  SymmetricFiberFunctorExists`;
* `frameFunctorExists_of_symmetricFiberFunctorExists` — the converse (so the Prop is TRUE and not
  stronger than the target).

Ingredients: the ring `G 𝟙` (Mathlib's `MonObj.toRing` on the image of the monoid `𝟙`), its
action `act` on every `G Y` (natural, central: `μ(act r y ⊗ z) = act r μ(y ⊗ z) = μ(y ⊗ act r z)`),
a character `χ : G 𝟙 → ℂ` (`exists_algHom_of_rank_le_aleph0`), the ideal
`I Y = span {act r y | χ r = 0}`, and the quotient `G ⧸ I` (`LaxIdeal.quot`), for which
`ε` is bijective and the frame survives; then `exists_fiberFunctor_of_generator`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Cardinal
open scoped TensorProduct

universe v u

section Frame

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxMonoidal]

/-- The frame map `(a_j) ↦ Σ_j μ(e_j ⊗ a_j)`. -/
def frameMap {X : D} {n : ℕ} (e : Fin n → G.obj X) (Z : D) : (Fin n → G.obj Z) →ₗ[ℂ] G.obj (X ⊗ Z) :=
  ∑ j, (μ G X Z).hom ∘ₗ TensorProduct.mk ℂ (G.obj X) (G.obj Z) (e j) ∘ₗ LinearMap.proj j

theorem frameMap_apply {X : D} {n : ℕ} (e : Fin n → G.obj X) (Z : D) (a : Fin n → G.obj Z) :
    frameMap G e Z a = ∑ j, (μ G X Z).hom (e j ⊗ₜ a j) := by
  simp [frameMap]
  rfl

/-- With `ε` bijective, a frame on `X` makes `G X` finite-dimensional and `μ_{X,Z}` bijective. -/
theorem finite_and_bijective_of_frame (hε : Function.Bijective (ε G).hom) {X : D} {n : ℕ}
    (e : Fin n → G.obj X) (hΦ : ∀ Z, Function.Bijective (frameMap G e Z)) :
    Module.Finite ℂ (G.obj X) ∧ ∀ Z, Function.Bijective (μ G X Z).hom := by
  -- `G X` is spanned by the `e j`
  have hspan : ∀ x : G.obj X, ∃ c : Fin n → ℂ, x = ∑ j, c j • e j := by
    intro x
    obtain ⟨a, ha⟩ := (hΦ (𝟙_ D)).2 ((G.map (ρ_ X).inv).hom x)
    choose c hc using fun j => hε.2 (a j)
    refine ⟨c, ?_⟩
    have hx : x = (G.map (ρ_ X).hom).hom ((G.map (ρ_ X).inv).hom x) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, Iso.inv_hom_id, G.map_id]
      rfl
    rw [hx, ← ha, frameMap_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrArg (fun φ => φ.hom (e j ⊗ₜ c j)) (Functor.LaxMonoidal.right_unitality G X)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply] at h
    rw [← hc j]
    exact h.symm
  refine ⟨?_, fun Z => ?_⟩
  · refine Module.Finite.of_surjective (∑ j, LinearMap.smulRight (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) (e j)) fun x => ?_
    obtain ⟨c, rfl⟩ := hspan x
    exact ⟨c, by simp⟩
  · let T : (Fin n → G.obj Z) →ₗ[ℂ] (G.obj X ⊗ G.obj Z : ModuleCat ℂ) :=
      ∑ j, TensorProduct.mk ℂ (G.obj X) (G.obj Z) (e j) ∘ₗ LinearMap.proj j
    have hT : ∀ a, T a = ∑ j, e j ⊗ₜ a j := fun a => by simp [T]; rfl
    have hcomp : ∀ a, (μ G X Z).hom (T a) = frameMap G e Z a := fun a => by
      rw [hT, map_sum, frameMap_apply]
    have hTs : Function.Surjective T := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero T⟩
      | tmul x z =>
        obtain ⟨c, rfl⟩ := hspan x
        refine ⟨fun j => c j • z, ?_⟩
        rw [hT, TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun j _ => (TensorProduct.smul_tmul _ _ _).symm
      | add a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add T a' b'⟩
    constructor
    · intro t t' htt
      obtain ⟨a, rfl⟩ := hTs t
      obtain ⟨b, rfl⟩ := hTs t'
      rw [hcomp, hcomp] at htt
      rw [(hΦ Z).1 htt]
    · intro w
      obtain ⟨a, rfl⟩ := (hΦ Z).2 w
      exact ⟨T a, hcomp a⟩

end Frame

section Act

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxBraided]

/-- The action of `R = G 𝟙` on `G Y`. -/
def act {Y : D} (r : G.obj (𝟙_ D)) (y : G.obj Y) : G.obj Y :=
  (μ G (𝟙_ D) Y ≫ G.map (λ_ Y).hom).hom (r ⊗ₜ y)

theorem act_add_right {Y : D} (r : G.obj (𝟙_ D)) (y y' : G.obj Y) :
    act G r (y + y') = act G r y + act G r y' := by
  simp [act, TensorProduct.tmul_add]

theorem act_smul_right {Y : D} (r : G.obj (𝟙_ D)) (c : ℂ) (y : G.obj Y) :
    act G r (c • y) = c • act G r y := by
  simp [act, TensorProduct.tmul_smul]

theorem act_zero_right {Y : D} (r : G.obj (𝟙_ D)) : act G r (0 : G.obj Y) = 0 := by
  simp [act]

theorem act_sub_left {Y : D} (r s : G.obj (𝟙_ D)) (y : G.obj Y) :
    act G (r - s) y = act G r y - act G s y := by
  simp [act, TensorProduct.sub_tmul]

theorem act_unit {Y : D} (y : G.obj Y) : act G ((ε G).hom 1) y = y := by
  have h := congrArg (fun φ => φ.hom ((1 : ℂ) ⊗ₜ y)) (Functor.LaxMonoidal.left_unitality G Y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul] at h
  exact h.symm

theorem act_natural {Y Y' : D} (f : Y ⟶ Y') (r : G.obj (𝟙_ D)) (y : G.obj Y) :
    (G.map f).hom (act G r y) = act G r ((G.map f).hom y) := by
  have key : (G.obj (𝟙_ D) ◁ G.map f) ≫ μ G (𝟙_ D) Y' ≫ G.map (λ_ Y').hom =
      (μ G (𝟙_ D) Y ≫ G.map (λ_ Y).hom) ≫ G.map f := by
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← G.map_comp, leftUnitor_naturality, G.map_comp,
      Category.assoc]
  have h := congrArg (fun φ => φ.hom (r ⊗ₜ y)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  simp only [act, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact h.symm

theorem μ_act_left {Y Z : D} (r : G.obj (𝟙_ D)) (y : G.obj Y) (z : G.obj Z) :
    (μ G Y Z).hom (act G r y ⊗ₜ z) = act G r ((μ G Y Z).hom (y ⊗ₜ z)) := by
  have key : (μ G (𝟙_ D) Y ≫ G.map (λ_ Y).hom) ▷ G.obj Z ≫ μ G Y Z =
      (α_ (G.obj (𝟙_ D)) (G.obj Y) (G.obj Z)).hom ≫ (G.obj (𝟙_ D) ◁ μ G Y Z) ≫
        μ G (𝟙_ D) (Y ⊗ Z) ≫ G.map (λ_ (Y ⊗ Z)).hom := by
    rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left,
      ← Functor.LaxMonoidal.associativity_assoc, ← G.map_comp, leftUnitor_tensor_hom,
      Iso.hom_inv_id_assoc]
  have h := congrArg (fun φ => φ.hom ((r ⊗ₜ y) ⊗ₜ z)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply] at h
  simp only [act, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact h

theorem μ_act_right {Y Z : D} (r : G.obj (𝟙_ D)) (y : G.obj Y) (z : G.obj Z) :
    (μ G Y Z).hom (y ⊗ₜ act G r z) = act G r ((μ G Y Z).hom (y ⊗ₜ z)) := by
  have hB : ∀ (w : G.obj Z), (μ G Y Z).hom (y ⊗ₜ w) = (G.map (β_ Z Y).hom).hom ((μ G Z Y).hom (w ⊗ₜ y)) :=
    fun w => by
      have := congrArg (fun φ => φ.hom (w ⊗ₜ y)) (Functor.LaxBraided.braided (F := G) Z Y)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.braiding_hom_apply] at this
      exact this.symm
  rw [hB, hB, μ_act_left, act_natural]

end Act

section Ring

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxBraided]

/-- The monoid structure on `G 𝟙` (image of the trivial monoid `𝟙`). -/
abbrev unitMonObj : MonObj (G.obj (𝟙_ D)) := Functor.monObjObj (F := G) (𝟙_ D)

/-- The commutative ring `R = G 𝟙` (`= Hom(𝟙, A)`). -/
abbrev unitRing : CommRing (G.obj (𝟙_ D)) :=
  letI := unitMonObj G
  { ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing (G.obj (𝟙_ D)) with
    mul_comm := fun r s => by
      change act G r s = act G s r
      have key : μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom =
          (β_ (G.obj (𝟙_ D)) (G.obj (𝟙_ D))).hom ≫ μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom := by
        rw [← Functor.LaxBraided.braided_assoc, ← G.map_comp, braiding_leftUnitor, unitors_equal]
      have h := congrArg (fun φ => φ.hom (s ⊗ₜ r)) key
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.braiding_hom_apply] at h
      simp only [act, ModuleCat.hom_comp, LinearMap.comp_apply]
      exact h.symm }

/-- The `ℂ`-algebra structure on `R = G 𝟙`. -/
abbrev unitAlgebra : @Algebra ℂ (G.obj (𝟙_ D)) _ (unitRing G).toSemiring :=
  letI := unitMonObj G
  ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (G.obj (𝟙_ D))

theorem unitRing_mul (r s : G.obj (𝟙_ D)) : (letI := unitRing G; r * s) = act G r s := rfl

theorem unitRing_one : (letI := unitRing G; (1 : G.obj (𝟙_ D))) = (ε G).hom 1 := by
  change (ε G ≫ G.map (𝟙 _)).hom 1 = _
  rw [G.map_id, Category.comp_id]

end Ring

section BaseChange

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxBraided]

/-- `act` as a linear map in its second argument. -/
def actLin {Y : D} (r : G.obj (𝟙_ D)) : G.obj Y →ₗ[ℂ] G.obj Y :=
  (μ G (𝟙_ D) Y ≫ G.map (λ_ Y).hom).hom ∘ₗ TensorProduct.mk ℂ (G.obj (𝟙_ D)) (G.obj Y) r

theorem actLin_apply {Y : D} (r : G.obj (𝟙_ D)) (y : G.obj Y) : actLin G r y = act G r y := rfl

theorem act_unit_right (r : G.obj (𝟙_ D)) : act G r ((ε G).hom 1) = r := by
  have h := congrArg (fun φ => φ.hom (r ⊗ₜ (1 : ℂ))) (Functor.LaxMonoidal.right_unitality G (𝟙_ D))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul] at h
  calc act G r ((ε G).hom 1) = (G.map (ρ_ (𝟙_ D)).hom).hom
        ((μ G (𝟙_ D) (𝟙_ D)).hom (r ⊗ₜ (ε G).hom 1)) := by rw [← unitors_equal]; rfl
    _ = r := h.symm

theorem act_frameMap {X : D} {n : ℕ} (e : Fin n → G.obj X) (Z : D) (r : G.obj (𝟙_ D))
    (a : Fin n → G.obj Z) :
    act G r (frameMap G e Z a) = frameMap G e Z (fun j => act G r (a j)) := by
  rw [frameMap_apply, frameMap_apply, ← actLin_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => (μ_act_right G r (e j) (a j)).symm

variable (χ : G.obj (𝟙_ D) →ₗ[ℂ] ℂ) (hmul : ∀ r s, χ (act G r s) = χ r * χ s)
  (hone : χ ((ε G).hom 1) = 1)

/-- The generators `act r y`, `χ r = 0`, of the base-change ideal. -/
def chiGen (Y : D) : Set (G.obj Y) := {w | ∃ r y, χ r = 0 ∧ w = act G r y}

/-- The ideal `I Y = span {act r y | χ r = 0}` (base change along `χ : G 𝟙 → ℂ`). -/
def chiIdeal : LaxIdeal G where
  I Y := Submodule.span ℂ (chiGen G χ Y)
  map_mem {Y Y'} f y hy := by
    have : Submodule.span ℂ (chiGen G χ Y) ≤ (Submodule.span ℂ (chiGen G χ Y')).comap (G.map f).hom :=
      Submodule.span_le.2 (by
        rintro w ⟨r, y, hr, rfl⟩
        exact Submodule.subset_span ⟨r, _, hr, act_natural G f r y⟩)
    exact this hy
  mul_mem_left Y Z y z hz := by
    have : Submodule.span ℂ (chiGen G χ Z) ≤ (Submodule.span ℂ (chiGen G χ (Y ⊗ Z))).comap
        ((μ G Y Z).hom ∘ₗ TensorProduct.mk ℂ (G.obj Y) (G.obj Z) y) :=
      Submodule.span_le.2 (by
        rintro w ⟨r, z, hr, rfl⟩
        exact Submodule.subset_span ⟨r, _, hr, μ_act_right G r y z⟩)
    exact this hz
  mul_mem_right Y Z y z hy := by
    have : Submodule.span ℂ (chiGen G χ Y) ≤ (Submodule.span ℂ (chiGen G χ (Y ⊗ Z))).comap
        ((μ G Y Z).hom ∘ₗ (TensorProduct.mk ℂ (G.obj Y) (G.obj Z)).flip z) :=
      Submodule.span_le.2 (by
        rintro w ⟨r, y, hr, rfl⟩
        exact Submodule.subset_span ⟨r, _, hr, μ_act_left G r y z⟩)
    exact this hy

include hmul in
theorem chi_eq_zero_of_mem {w : G.obj (𝟙_ D)} (hw : w ∈ (chiIdeal G χ).I (𝟙_ D)) : χ w = 0 := by
  have : Submodule.span ℂ (chiGen G χ (𝟙_ D)) ≤ LinearMap.ker χ :=
    Submodule.span_le.2 (by
      rintro w ⟨r, y, hr, rfl⟩
      simp [LinearMap.mem_ker, hmul, hr])
  exact this hw

include hmul hone in
/-- After base change, `ε : ℂ → G 𝟙 ⧸ I 𝟙` is bijective (`Hom(𝟙, A) = ℂ`). -/
theorem quot_ε_bijective : Function.Bijective (ε (chiIdeal G χ).quot).hom := by
  have hεc : ∀ c : ℂ, (ε G).hom c = c • (ε G).hom 1 := fun c => by
    rw [← map_smul, smul_eq_mul, mul_one]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    rw [LaxIdeal.quot_ε_apply] at hc
    have := chi_eq_zero_of_mem G χ hmul ((Submodule.Quotient.mk_eq_zero _).1 hc)
    rwa [hεc, map_smul, hone, smul_eq_mul, mul_one] at this
  · intro x
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨χ r, ?_⟩
    rw [LaxIdeal.quot_ε_apply]
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ?_)
    refine ⟨(ε G).hom (χ r) - r, (ε G).hom 1, ?_, ?_⟩
    · rw [map_sub, hεc, map_smul, hone, smul_eq_mul, mul_one, sub_self]
    · rw [act_unit_right]

theorem frameMap_quot (J : LaxIdeal G) {X : D} {n : ℕ} (e : Fin n → G.obj X) (Z : D)
    (a : Fin n → G.obj Z) :
    frameMap J.quot (fun j => (Submodule.Quotient.mk (e j) : G.obj X ⧸ J.I X)) Z
      (fun j => (Submodule.Quotient.mk (a j) : G.obj Z ⧸ J.I Z)) =
      (Submodule.Quotient.mk (frameMap G e Z a) : G.obj (X ⊗ Z) ⧸ J.I (X ⊗ Z)) := by
  rw [frameMap_apply, frameMap_apply, ← Submodule.mkQ_apply, map_sum]
  rfl

/-- After base change the frame survives. -/
theorem quot_frame_bijective {X : D} {n : ℕ} (e : Fin n → G.obj X)
    (hΦ : ∀ Z, Function.Bijective (frameMap G e Z)) (Z : D) :
    Function.Bijective (frameMap (chiIdeal G χ).quot
      (fun j => (Submodule.Quotient.mk (e j) : G.obj X ⧸ (chiIdeal G χ).I X)) Z) := by
  set J := chiIdeal G χ
  have hI : J.I (X ⊗ Z) ≤ (Submodule.pi Set.univ (fun _ : Fin n => J.I Z)).map (frameMap G e Z) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨r, w', hr, rfl⟩
    obtain ⟨c, rfl⟩ := (hΦ Z).2 w'
    refine ⟨fun j => act G r (c j), fun j _ => Submodule.subset_span ⟨r, c j, hr, rfl⟩, ?_⟩
    exact (act_frameMap G e Z r c).symm
  constructor
  · intro a b hab
    choose a₀ ha₀ using fun j => Submodule.Quotient.mk_surjective (J.I Z) (a j)
    choose b₀ hb₀ using fun j => Submodule.Quotient.mk_surjective (J.I Z) (b j)
    have ea : a = fun j => (Submodule.Quotient.mk (a₀ j) : G.obj Z ⧸ J.I Z) := funext fun j => (ha₀ j).symm
    have eb : b = fun j => (Submodule.Quotient.mk (b₀ j) : G.obj Z ⧸ J.I Z) := funext fun j => (hb₀ j).symm
    subst ea eb
    rw [frameMap_quot, frameMap_quot] at hab
    have hab' := (Submodule.Quotient.eq _).1 hab
    rw [← map_sub] at hab'
    obtain ⟨c, hc, hc'⟩ := hI hab'
    have := (hΦ Z).1 hc'
    funext j
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Pi.sub_apply, ← this]
    exact hc j (Set.mem_univ _)
  · intro w
    obtain ⟨w₀, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨a, rfl⟩ := (hΦ Z).2 w₀
    exact ⟨_, frameMap_quot G J e Z a⟩

end BaseChange

section Main

/-- **Frame functors** (named TRUE input; Deligne's commutative algebra in `Ind(D)` with a frame on a
generator, encoded as a lax braided functor `G Y = Hom(𝟙, A ⊗ Y)`): for every symmetric fusion
category over `ℂ` with positive dimensions there are a lax braided, additive, `ℂ`-linear
`G : D ⥤ ModuleCat ℂ`, an object `X` containing every simple as a retract and `e : Fin n → G X`
such that `G 𝟙` is nonzero (`ε 1 ≠ 0`) of countable dimension and the frame map
`(a_j) ↦ Σ_j μ(e_j ⊗ a_j) : G(Z)^n → G(X ⊗ Z)` is bijective for every `Z`.

TRUE: implied by `SymmetricFiberFunctorExists` (`frameFunctorExists_of_symmetricFiberFunctorExists`).
**Proved** (all universes) as `frameFunctorExists_holds` in `DeligneFiberMain` (Gram–Schmidt).
Source of the construction: Deligne, *Catégories tannakiennes* (1990) §7; EGNO §9.9 — the frame
algebra `Sym(X^∨ ⊗ ℂ^n ⊕ X ⊗ ℂ^{n∨}) ⧸ (frame relations)`. -/
def FrameFunctorExists : Prop :=
  ∀ (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
    [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D],
    (∀ i, 0 < (symDim (F.simple i)).re) →
    ∃ (G : D ⥤ ModuleCat.{0} ℂ) (_ : G.LaxBraided) (_ : G.Additive) (_ : G.Linear ℂ)
      (X : D) (n : ℕ) (e : Fin n → G.obj X),
      (∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _) ∧
      (ε G).hom 1 ≠ 0 ∧ Module.rank ℂ (G.obj (𝟙_ D)) ≤ ℵ₀ ∧
      ∀ Z, Function.Bijective (frameMap G e Z)

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

/-- **A frame functor yields a fiber functor** (base change to a `ℂ`-point of `G 𝟙`). -/
theorem exists_fiberFunctor_of_frame (hpos : ∀ i, 0 < (symDim (F.simple i)).re)
    (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ] {X : D} {n : ℕ}
    (e : Fin n → G.obj X) (hX : ∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _)
    (hne : (ε G).hom 1 ≠ 0) (hrank : Module.rank ℂ (G.obj (𝟙_ D)) ≤ ℵ₀)
    (hΦ : ∀ Z, Function.Bijective (frameMap G e Z)) :
    ∃ ω : D ⥤ FGModuleCat ℂ, Nonempty ω.Braided ∧ ω.Linear ℂ ∧ ω.Faithful := by
  letI := unitRing G
  letI := unitAlgebra G
  haveI : Nontrivial (G.obj (𝟙_ D)) := ⟨⟨1, 0, by rw [unitRing_one]; exact hne⟩⟩
  obtain ⟨χ⟩ := exists_algHom_of_rank_le_aleph0 (R := G.obj (𝟙_ D)) hrank
  let χl : G.obj (𝟙_ D) →ₗ[ℂ] ℂ :=
    { toFun := χ
      map_add' := χ.map_add
      map_smul' := fun c r => map_smul χ c r }
  have hmul : ∀ r s, χl (act G r s) = χl r * χl s := fun r s => χ.map_mul r s
  have hone : χl ((ε G).hom 1) = 1 := by
    change χ _ = 1
    rw [← unitRing_one]
    exact χ.map_one
  set J := chiIdeal G χl
  have hε' := quot_ε_bijective G χl hmul hone
  have hfr := finite_and_bijective_of_frame J.quot hε' _ (quot_frame_bijective G χl e hΦ)
  exact exists_fiberFunctor_of_generator J.quot hpos hε' hX hfr.2 hfr.1

end Main

/-- **Reduction**: frame functors give Deligne's existence theorem. -/
theorem symmetricFiberFunctorExists_of_frameFunctorExists (h : FrameFunctorExists.{v, u}) :
    SymmetricFiberFunctorExists.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ _ hpos
  obtain ⟨G, _, _, _, X, n, e, hX, hne, hrank, hΦ⟩ := h D hpos
  exact exists_fiberFunctor_of_frame hpos G e hX hne hrank hΦ

/-- The converse: `SymmetricFiberFunctorExists → FrameFunctorExists` (a fiber functor is a frame
functor with `G 𝟙 = ℂ`, `X = ⨁ X_i` and `e` a basis of `ω X`).  So `FrameFunctorExists` is TRUE
and exactly as strong as the target. -/
theorem frameFunctorExists_of_symmetricFiberFunctorExists (h : SymmetricFiberFunctorExists.{v, u}) :
    FrameFunctorExists.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ F hpos
  obtain ⟨ω, ⟨hω⟩, hlin, hfaith⟩ := h D hpos
  letI := hω
  haveI := Reconstruction.additive_of_braided ω
  let G := ω ⋙ (ModuleCat.isFG ℂ).ι
  haveI hfin : ∀ Y, Module.Finite ℂ (G.obj Y) := fun Y => (ω.obj Y).property
  let X : D := ⨁ (fun i => F.simple i)
  let b := Module.finBasis ℂ (G.obj X)
  refine ⟨G, inferInstance, inferInstance, inferInstance, X, _, b, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨biproduct.ι _ i, biproduct.π _ i, biproduct.ι_π_self _ i⟩
  · intro h0
    have hb := (ConcreteCategory.isIso_iff_bijective (ε G)).1 inferInstance
    exact one_ne_zero (α := ℂ) (hb.1 (h0.trans (map_zero _).symm))
  · exact (Module.rank_lt_aleph0 ℂ (G.obj (𝟙_ D))).le
  · intro Z
    have hμ := (ConcreteCategory.isIso_iff_bijective (μ G X Z)).1 inferInstance
    let E := (Finsupp.linearEquivFunOnFinite ℂ (G.obj Z) (Fin (Module.finrank ℂ (G.obj X)))).symm.trans
      (TensorProduct.equivFinsuppOfBasisLeft (N := G.obj Z) b).symm
    have hE : ∀ a, E a = ∑ j, b j ⊗ₜ a j := fun a => by
      simp [E, Finsupp.sum_fintype]
    have hcomp : ⇑(frameMap G b Z) = (μ G X Z).hom ∘ E := by
      funext a
      rw [frameMap_apply, Function.comp_apply, hE, map_sum]
    rw [hcomp]
    exact hμ.comp E.bijective

end VOA.Huang.TensorCat.DeligneFiber
