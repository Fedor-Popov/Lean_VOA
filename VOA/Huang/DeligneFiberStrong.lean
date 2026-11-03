/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberQuotient
import VOA.Huang.ReconstructionSemisimple

/-!
# Deligne's fiber functor — from a lax functor with a free generator to a fiber functor

Let `D` be a symmetric fusion category over `ℂ` whose simples have positive dimension, and
`G : D ⥤ ModuleCat ℂ` a lax braided, additive, `ℂ`-linear functor (= a commutative algebra `A` in
`Ind(D)`, `G Y = Hom(𝟙, A ⊗ Y)`).  Suppose

* `ε : ℂ → G 𝟙` is bijective (`Hom(𝟙, A) = ℂ`), and
* there is an object `X` containing every simple as a retract such that `μ : G X ⊗ G Z → G(X ⊗ Z)`
  is bijective for every `Z` and `G X` is finite-dimensional (`A ⊗ X` is a free `A`-module of
  finite rank).

Then `G` is a fiber functor:

* `bijective_μ_of_generator` — `μ_{Y,Z}` is bijective for **all** `Y, Z` (retracts and direct
  sums of objects with bijective `μ_{-,Z}` again have it);
* `finite_of_generator` — every `G Y` is finite-dimensional;
* `nontrivial_simple` — `G X_i ≠ 0` (else `G` kills `trMor (𝟙 X_i) = d_i • 𝟙`, `d_i ≠ 0`);
* `faithful_of_generator` — `G` is faithful (Schur + decompositions);
* `liftFG` — the corestriction to `FGModuleCat ℂ`, with its lax monoidal / braided structure;
* `exists_fiberFunctor_of_generator` — `∃ ω : D ⥤ FGModuleCat ℂ` braided, linear, faithful.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal
open scoped TensorProduct

universe v u

section Lift

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (G : D ⥤ ModuleCat.{0} ℂ) (hfin : ∀ Y, Module.Finite ℂ (G.obj Y))

/-- The corestriction of `G` to finite-dimensional spaces. -/
abbrev liftFG : D ⥤ FGModuleCat ℂ := (ModuleCat.isFG ℂ).lift G hfin

instance [G.LaxMonoidal] : (liftFG G hfin).LaxMonoidal where
  ε := ObjectProperty.homMk (ε G)
  μ X Y := ObjectProperty.homMk (μ G X Y)
  μ_natural_left f X' := by
    apply ObjectProperty.hom_ext
    simp
  μ_natural_right X' f := by
    apply ObjectProperty.hom_ext
    simp
  associativity X Y Z := by
    apply ObjectProperty.hom_ext
    simp
  left_unitality X := by
    apply ObjectProperty.hom_ext
    simp
  right_unitality X := by
    apply ObjectProperty.hom_ext
    simp

instance [G.LaxBraided] : (liftFG G hfin).LaxBraided where
  braided X Y := by
    apply ObjectProperty.hom_ext
    simpa using Functor.LaxBraided.braided (F := G) X Y

theorem isIso_liftFG_ε [G.LaxMonoidal] (h : IsIso (ε G)) : IsIso (ε (liftFG G hfin)) := by
  have : IsIso ((ModuleCat.isFG ℂ).ι.map (ε (liftFG G hfin))) := h
  exact isIso_of_reflects_iso _ (ModuleCat.isFG ℂ).ι

theorem isIso_liftFG_μ [G.LaxMonoidal] (X Y : D) (h : IsIso (μ G X Y)) :
    IsIso (μ (liftFG G hfin) X Y) := by
  have : IsIso ((ModuleCat.isFG ℂ).ι.map (μ (liftFG G hfin) X Y)) := h
  exact isIso_of_reflects_iso _ (ModuleCat.isFG ℂ).ι

/-- A lax braided functor into `ModuleCat ℂ` with invertible `ε, μ` and finite-dimensional values
corestricts to a braided functor into `FGModuleCat ℂ`. -/
theorem nonempty_braided_liftFG [G.LaxBraided] (hε : IsIso (ε G)) (hμ : ∀ X Y, IsIso (μ G X Y)) :
    Nonempty (liftFG G hfin).Braided := by
  haveI := isIso_liftFG_ε G hfin hε
  haveI := fun X Y => isIso_liftFG_μ G hfin X Y (hμ X Y)
  letI : (liftFG G hfin).Monoidal := Functor.Monoidal.ofLaxMonoidal _
  exact ⟨{ braided := Functor.LaxBraided.braided }⟩

instance [Preadditive D] [Linear ℂ D] [G.Linear ℂ] : (liftFG G hfin).Linear ℂ where
  map_smul f c := by
    apply ObjectProperty.hom_ext
    exact Functor.Linear.map_smul (F := G) f c

instance [G.Faithful] : (liftFG G hfin).Faithful where
  map_injective {_ _} _ _ h := G.map_injective (congrArg (fun φ => φ.hom) h)

end Lift

section Fusion

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]
  (G : D ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive]

open Reconstruction

theorem μ_nat_apply {A B : D} (f : A ⟶ B) (Z : D) (t : ↑(G.obj A ⊗ G.obj Z)) :
    (μ G B Z).hom ((G.map f ▷ G.obj Z).hom t) = (G.map (f ▷ Z)).hom ((μ G A Z).hom t) := by
  have := congrArg (fun φ => φ.hom t) (μ_natural_left G f Z)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

/-- Retracts inherit bijectivity of `μ_{-,Z}`. -/
theorem bijective_μ_of_retract {X Y : D} (s : Y ⟶ X) (r : X ⟶ Y) (hsr : s ≫ r = 𝟙 Y) (Z : D)
    (h : Function.Bijective (μ G X Z).hom) : Function.Bijective (μ G Y Z).hom := by
  have key : ∀ t, (G.map r ▷ G.obj Z).hom ((G.map s ▷ G.obj Z).hom t) = t := fun t => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← comp_whiskerRight, ← G.map_comp, hsr,
      G.map_id, id_whiskerRight]
    rfl
  have key2 : ∀ w, (G.map (r ▷ Z)).hom ((G.map (s ▷ Z)).hom w) = w := fun w => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, ← comp_whiskerRight, hsr,
      id_whiskerRight, G.map_id]
    rfl
  constructor
  · intro t t' htt
    have e := congrArg (G.map (s ▷ Z)).hom htt
    rw [← μ_nat_apply, ← μ_nat_apply] at e
    rw [← key t, ← key t', h.1 e]
  · intro w
    obtain ⟨t, ht⟩ := h.2 ((G.map (s ▷ Z)).hom w)
    refine ⟨(G.map r ▷ G.obj Z).hom t, ?_⟩
    rw [μ_nat_apply, ht, key2]

/-- Direct sums of simples with bijective `μ_{-,Z}` have it. -/
theorem bijective_μ_of_decomp {Y : D} (d : Decomp Y) (Z : D)
    (h : ∀ k, Function.Bijective (μ G (F.simple (d.f k)) Z).hom) :
    Function.Bijective (μ G Y Z).hom := by
  have tot1 : ∑ k, (G.map (d.π k) ▷ G.obj Z) ≫ (G.map (d.ι k) ▷ G.obj Z) = 𝟙 _ := by
    simp_rw [← comp_whiskerRight, ← G.map_comp]
    rw [← sum_whiskerRight, ← G.map_sum, d.total, G.map_id, id_whiskerRight]
  have tot2 : ∑ k, G.map (d.π k ▷ Z) ≫ G.map (d.ι k ▷ Z) = 𝟙 _ := by
    simp_rw [← G.map_comp, ← comp_whiskerRight]
    rw [← G.map_sum, ← sum_whiskerRight, d.total, id_whiskerRight, G.map_id]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
    have ht' : t = ∑ k, (G.map (d.ι k) ▷ G.obj Z).hom ((G.map (d.π k) ▷ G.obj Z).hom t) := by
      have := congrArg (fun φ => φ.hom t) tot1
      simpa using this.symm
    rw [ht']
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : (μ G _ Z).hom ((G.map (d.π k) ▷ G.obj Z).hom t) = (μ G _ Z).hom 0 := by
      rw [μ_nat_apply, ht, map_zero, map_zero]
    rw [(h k).1 e, map_zero]
  · intro w
    choose t ht using fun k => (h k).2 ((G.map (d.π k ▷ Z)).hom w)
    refine ⟨∑ k, (G.map (d.ι k) ▷ G.obj Z).hom (t k), ?_⟩
    rw [map_sum]
    simp_rw [μ_nat_apply, ht]
    have := congrArg (fun φ => φ.hom w) tot2
    simpa using this

/-- If `μ_{X,-}` is bijective for an object `X` containing every simple as a retract, then
`μ_{Y,Z}` is bijective for all `Y, Z`. -/
theorem bijective_μ_of_generator {X : D}
    (hX : ∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _)
    (hμ : ∀ Z, Function.Bijective (μ G X Z).hom) (Y Z : D) :
    Function.Bijective (μ G Y Z).hom :=
  bijective_μ_of_decomp G (decomp Y) Z fun k => by
    obtain ⟨s, r, hsr⟩ := hX ((decomp Y).f k)
    exact bijective_μ_of_retract G s r hsr Z (hμ Z)

/-- Every `G Y` is finite-dimensional once `G X` is. -/
theorem finite_of_generator {X : D}
    (hX : ∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _)
    (hfin : Module.Finite ℂ (G.obj X)) (Y : D) : Module.Finite ℂ (G.obj Y) := by
  have hS : ∀ i, Module.Finite ℂ (G.obj (F.simple i)) := fun i => by
    obtain ⟨s, r, hsr⟩ := hX i
    refine Module.Finite.of_surjective (G.map r).hom fun y => ⟨(G.map s).hom y, ?_⟩
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, hsr, G.map_id]
    rfl
  let d := decomp Y
  let Φ : (∀ k, G.obj (F.simple (d.f k))) →ₗ[ℂ] G.obj Y :=
    ∑ k, (G.map (d.ι k)).hom ∘ₗ LinearMap.proj k
  refine Module.Finite.of_surjective Φ fun y => ⟨fun k => (G.map (d.π k)).hom y, ?_⟩
  have := congrArg (fun φ => φ.hom y) (show ∑ k, G.map (d.π k) ≫ G.map (d.ι k) = 𝟙 _ by
    simp_rw [← G.map_comp]; rw [← G.map_sum, d.total, G.map_id])
  simpa [Φ] using this

variable [G.Linear ℂ]

/-- `G X_i ≠ 0` for every simple: otherwise `G` kills `trMor (𝟙 X_i) = d_i • 𝟙`. -/
theorem nontrivial_simple (hpos : ∀ i, 0 < (symDim (F.simple i)).re)
    (hε : Function.Bijective (ε G).hom) (hμ : ∀ Y Z, Function.Bijective (μ G Y Z).hom)
    (i : F.ι) : Nontrivial (G.obj (F.simple i)) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  set X := F.simple i
  have h0 : ∀ w : G.obj (X ⊗ Xᘁ), w = 0 := fun w => by
    obtain ⟨t, rfl⟩ := (hμ X Xᘁ).2 w
    have : t = 0 := by
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [this, map_zero]
  have htr := trMor_id_eq_smul X
  have e := congrArg (fun φ => (G.map φ).hom ((ε G).hom 1)) htr
  simp only [trMor, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [h0 ((G.map (η_ X Xᘁ)).hom ((ε G).hom 1)), map_zero, map_zero, map_zero,
    Functor.Linear.map_smul, G.map_id] at e
  have e' : symDim X • (ε G).hom 1 = 0 := by simpa using e.symm
  rcases smul_eq_zero.1 e' with h | h
  · have := hpos i
    rw [h] at this
    simp at this
  · exact one_ne_zero (α := ℂ) (hε.1 (h.trans (map_zero _).symm))

/-- Schur: a morphism between simples killed by `G` vanishes. -/
theorem simple_hom_eq_zero_of_map {i j : F.ι} (hnt : Nontrivial (G.obj (F.simple i)))
    (c : F.simple i ⟶ F.simple j) (hc : G.map c = 0) : c = 0 := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨t, rfl⟩ := simple_end_eq_smul c
    rw [Functor.Linear.map_smul, G.map_id] at hc
    obtain ⟨x, hx⟩ := exists_ne (0 : G.obj (F.simple i))
    have := congrArg (fun φ => φ.hom x) hc
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] at this
    rcases smul_eq_zero.1 this with h | h
    · rw [h, zero_smul]
    · exact absurd h hx
  · exact simple_hom_eq_zero hij c

/-- `G` is faithful. -/
theorem faithful_of_simple (hnt : ∀ i, Nontrivial (G.obj (F.simple i))) : G.Faithful where
  map_injective {Y Y'} f g hfg := by
    rw [← sub_eq_zero]
    have hφ : G.map (f - g) = 0 := by rw [G.map_sub, hfg, sub_self]
    set φ := f - g
    let d := decomp Y
    let d' := decomp Y'
    have hc : ∀ k l, d.ι k ≫ φ ≫ d'.π l = 0 := fun k l =>
      simple_hom_eq_zero_of_map G (hnt _) _ (by simp [hφ])
    calc φ = (∑ k, d.π k ≫ d.ι k) ≫ φ ≫ (∑ l, d'.π l ≫ d'.ι l) := by
            rw [d.total, d'.total, Category.id_comp, Category.comp_id]
      _ = ∑ k, ∑ l, d.π k ≫ (d.ι k ≫ φ ≫ d'.π l) ≫ d'.ι l := by
            simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
            exact Finset.sum_comm
      _ = 0 := by simp [hc]

/-- **A lax braided functor with `Hom(𝟙, A) = ℂ` that is free on a generator is a fiber
functor.** -/
theorem exists_fiberFunctor_of_generator (hpos : ∀ i, 0 < (symDim (F.simple i)).re)
    (hε : Function.Bijective (ε G).hom) {X : D}
    (hX : ∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _)
    (hμ : ∀ Z, Function.Bijective (μ G X Z).hom) (hfin : Module.Finite ℂ (G.obj X)) :
    ∃ ω : D ⥤ FGModuleCat ℂ, Nonempty ω.Braided ∧ ω.Linear ℂ ∧ ω.Faithful := by
  have hμ' := bijective_μ_of_generator G hX hμ
  have hfin' := finite_of_generator G hX hfin
  haveI := faithful_of_simple G (nontrivial_simple G hpos hε hμ')
  refine ⟨liftFG G hfin', nonempty_braided_liftFG G hfin' ?_ ?_, inferInstance, inferInstance⟩
  · exact (ConcreteCategory.isIso_iff_bijective _).2 hε
  · exact fun Y Z => (ConcreteCategory.isIso_iff_bijective _).2 (hμ' Y Z)

end Fusion

end VOA.Huang.TensorCat.DeligneFiber
