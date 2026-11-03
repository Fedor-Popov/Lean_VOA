/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.Character
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Exact sequences of ordinary VOA modules

This file supplies the small amount of non-categorical exact-sequence infrastructure needed by
ordinary-module resolutions.  A morphism is a weak-module homomorphism together with an explicit
proof that it preserves every conformal-weight space.  Exactness is stated pointwise on the
underlying linear maps; no exactness or splitting is inferred from the module structures.

For a short exact sequence, the internal weight decompositions show that the sequence restricts to
a short exact sequence on every finite-dimensional weight space.  Rank-nullity then gives
coefficientwise additivity of `gradedDim`.

There are deliberately no category instances and no VOA-specific examples in this file.
-/

namespace VOA

open scoped BigOperators

universe u v w x

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

namespace OrdVModule

variable {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {N : Type w} [AddCommGroup N] [Module ℂ N]
variable {P : Type x} [AddCommGroup P] [Module ℂ P]
variable {A : OrdVModule W M} {B : OrdVModule W N} {C : OrdVModule W P}

/-! ## Ordinary-module morphisms -/

/-- A morphism of ordinary VOA modules: a weak-module homomorphism which explicitly preserves
each conformal-weight space. -/
structure Hom (A : OrdVModule W M) (B : OrdVModule W N) where
  /-- The underlying weak-module homomorphism. -/
  toWeakHom : A.toWeakModule.Hom B.toWeakModule
  /-- Preservation of conformal weights. -/
  map_weight : ∀ (α : ℂ) {m : M}, m ∈ A.weight α →
    toWeakHom.toLinearMap m ∈ B.weight α

namespace Hom

/-- The underlying linear map of an ordinary-module morphism. -/
def toLinearMap (f : Hom A B) : M →ₗ[ℂ] N := f.toWeakHom.toLinearMap

@[simp] theorem toLinearMap_apply (f : Hom A B) (m : M) :
    f.toLinearMap m = f.toWeakHom.toLinearMap m := rfl

/-- An ordinary-module morphism intertwines every mode action. -/
theorem map_act (f : Hom A B) (a : 𝒱) (n : ℤ) (m : M) :
    f.toLinearMap (A.toWeakModule.act a n m) =
      B.toWeakModule.act a n (f.toLinearMap m) :=
  f.toWeakHom.map_act a n m

/-- The identity ordinary-module morphism. -/
def refl (A : OrdVModule W M) : Hom A A where
  toWeakHom :=
    { toLinearMap := LinearMap.id
      map_act := fun _ _ _ => rfl }
  map_weight := fun _ {_} hm => hm

/-- Composition of ordinary-module morphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toWeakHom :=
    { toLinearMap := g.toLinearMap.comp f.toLinearMap
      map_act := by
        intro a n m
        simp only [LinearMap.comp_apply, f.map_act, g.map_act] }
  map_weight := fun α {_} hm => g.map_weight α (f.map_weight α hm)

@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (m : M) :
    (g.comp f).toLinearMap m = g.toLinearMap (f.toLinearMap m) := rfl

/-- The restriction of an ordinary-module morphism to a conformal-weight space. -/
def weightMap (f : Hom A B) (α : ℂ) : A.weight α →ₗ[ℂ] B.weight α where
  toFun m := ⟨f.toLinearMap (m : M), f.map_weight α m.2⟩
  map_add' m n := by
    apply Subtype.ext
    exact map_add f.toLinearMap (m : M) (n : M)
  map_smul' c m := by
    apply Subtype.ext
    exact map_smul f.toLinearMap c (m : M)

@[simp] theorem weightMap_coe (f : Hom A B) (α : ℂ) (m : A.weight α) :
    ((f.weightMap α m : B.weight α) : N) = f.toLinearMap (m : M) := rfl

/-! ## Kernel and range -/

/-- The kernel as a weak VOA submodule of the source. -/
def ker (f : Hom A B) : WeakModule.Submodule' A.toWeakModule where
  carrier := LinearMap.ker f.toLinearMap
  act_mem := by
    intro a n m hm
    rw [LinearMap.mem_ker] at hm ⊢
    rw [f.map_act, hm, WeakModule.act_zero_right]

@[simp] theorem ker_carrier (f : Hom A B) : f.ker.carrier = LinearMap.ker f.toLinearMap := rfl

/-- The range as a weak VOA submodule of the target. -/
def range (f : Hom A B) : WeakModule.Submodule' B.toWeakModule where
  carrier := LinearMap.range f.toLinearMap
  act_mem := by
    intro a n m hm
    obtain ⟨y, rfl⟩ := hm
    refine ⟨A.toWeakModule.act a n y, ?_⟩
    exact f.map_act a n y

@[simp] theorem range_carrier (f : Hom A B) :
    f.range.carrier = LinearMap.range f.toLinearMap := rfl

/-- The kernel on the `α`-weight space. -/
def gradedKernel (f : Hom A B) (α : ℂ) : Submodule ℂ (A.weight α) :=
  LinearMap.ker (f.weightMap α)

/-- The range on the `α`-weight space. -/
def gradedRange (f : Hom A B) (α : ℂ) : Submodule ℂ (B.weight α) :=
  LinearMap.range (f.weightMap α)

@[simp] theorem mem_gradedKernel (f : Hom A B) (α : ℂ) (m : A.weight α) :
    m ∈ f.gradedKernel α ↔ f.weightMap α m = 0 := LinearMap.mem_ker

theorem mem_gradedRange (f : Hom A B) (α : ℂ) (n : B.weight α) :
    n ∈ f.gradedRange α ↔ ∃ m : A.weight α, f.weightMap α m = n := by
  exact LinearMap.mem_range

/-! ## Weight projections and naturality -/

/-- Projection to a conformal-weight space, obtained from the internal direct sum. -/
noncomputable def weightProj (A : OrdVModule W M) (α : ℂ) : M →ₗ[ℂ] A.weight α :=
  internalProjTo A.isInternal α

/-- Projection is the identity on its own weight space. -/
@[simp] theorem weightProj_coe (A : OrdVModule W M) (α : ℂ) (m : A.weight α) :
    weightProj A α (m : M) = m :=
  internalProjTo_coe A.isInternal α m

/-- Projection to `α` vanishes on a distinct `β`-weight space. -/
theorem weightProj_eq_zero_of_mem (A : OrdVModule W M) {α β : ℂ} (hαβ : α ≠ β)
    {m : M} (hm : m ∈ A.weight β) : weightProj A α m = 0 := by
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  apply Subtype.ext
  unfold weightProj internalProjTo
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    ← DirectSum.apply_eq_component]
  rw [DirectSum.decompose_of_mem_ne A.weight hm (Ne.symm hαβ)]
  rfl

/-- Weight projection commutes with an ordinary-module morphism.  This is the key fact which
allows global pointwise exactness to be restricted to each homogeneous piece. -/
theorem weightProj_naturality (f : Hom A B) (α : ℂ) (m : M) :
    f.weightMap α (weightProj A α m) = weightProj B α (f.toLinearMap m) := by
  have hm : m ∈ ⨆ β : ℂ, A.weight β := by
    rw [A.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction A.weight hm
    (motive := fun m => f.weightMap α (weightProj A α m) =
      weightProj B α (f.toLinearMap m)) ?_ ?_ ?_
  · intro β y hy
    by_cases h : α = β
    · subst β
      have hfy : f.toLinearMap y ∈ B.weight α := f.map_weight α hy
      have hA : weightProj A α y = (⟨y, hy⟩ : A.weight α) :=
        weightProj_coe A α ⟨y, hy⟩
      have hB : weightProj B α (f.toLinearMap y) =
          (⟨f.toLinearMap y, hfy⟩ : B.weight α) :=
        weightProj_coe B α ⟨f.toLinearMap y, hfy⟩
      apply Subtype.ext
      rw [hA, hB]
      rfl
    · have hfy : f.toLinearMap y ∈ B.weight β := f.map_weight β hy
      rw [weightProj_eq_zero_of_mem A h hy, weightProj_eq_zero_of_mem B h hfy]
      exact map_zero (f.weightMap α)
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]

/-! ## Pointwise exactness -/

/-- Pointwise exactness at the middle ordinary module: an element is killed by `g` exactly when
it is the image of `f`. -/
def ExactAt (f : Hom A B) (g : Hom B C) : Prop :=
  ∀ n : N, g.toLinearMap n = 0 ↔ ∃ m : M, f.toLinearMap m = n

/-- A short exact sequence of ordinary-module morphisms, stated without category machinery. -/
structure ShortExact (f : Hom A B) (g : Hom B C) : Prop where
  injective : Function.Injective f.toLinearMap
  exactAt : ExactAt f g
  surjective : Function.Surjective g.toLinearMap

/-- Pointwise exactness is equivalent to equality of the ordinary linear range and kernel. -/
theorem exactAt_iff_range_eq_ker (f : Hom A B) (g : Hom B C) :
    ExactAt f g ↔ LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap := by
  constructor
  · intro h
    ext n
    change (∃ m : M, f.toLinearMap m = n) ↔ g.toLinearMap n = 0
    exact (h n).symm
  · intro h n
    have hn := SetLike.ext_iff.mp h n
    change g.toLinearMap n = 0 ↔ ∃ m : M, f.toLinearMap m = n
    exact hn.symm

namespace ShortExact

variable {f : Hom A B} {g : Hom B C}

/-- Injectivity restricts to every conformal-weight space. -/
theorem weight_injective (h : ShortExact f g) (α : ℂ) :
    Function.Injective (f.weightMap α) := by
  intro m n hmn
  apply Subtype.ext
  apply h.injective
  exact congrArg Subtype.val hmn

/-- Surjectivity restricts to every conformal-weight space. -/
theorem weight_surjective (h : ShortExact f g) (α : ℂ) :
    Function.Surjective (g.weightMap α) := by
  intro p
  obtain ⟨n, hn⟩ := h.surjective (p : P)
  refine ⟨weightProj B α n, ?_⟩
  rw [g.weightProj_naturality]
  apply Subtype.ext
  rw [hn, weightProj_coe]

/-- Exactness restricts to every conformal-weight space. -/
theorem exactAt_weight (h : ShortExact f g) (α : ℂ) (n : B.weight α) :
    g.weightMap α n = 0 ↔ ∃ m : A.weight α, f.weightMap α m = n := by
  constructor
  · intro hn
    have hgn : g.toLinearMap (n : N) = 0 := by
      exact congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (h.exactAt (n : N)).mp hgn
    refine ⟨weightProj A α m, ?_⟩
    rw [f.weightProj_naturality]
    apply Subtype.ext
    rw [hm, weightProj_coe]
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    change g.toLinearMap (f.toLinearMap (m : M)) = 0
    exact (h.exactAt (f.toLinearMap (m : M))).mpr ⟨m, rfl⟩

/-- On every weight, the middle dimension is the sum of the outer dimensions. -/
theorem finrank_weight_eq (h : ShortExact f g) (α : ℂ) :
    Module.finrank ℂ (B.weight α) =
      Module.finrank ℂ (A.weight α) + Module.finrank ℂ (C.weight α) := by
  letI := A.finrank α
  letI := B.finrank α
  letI := C.finrank α
  have hexact : LinearMap.range (f.weightMap α) = LinearMap.ker (g.weightMap α) := by
    ext n
    change (∃ m : A.weight α, f.weightMap α m = n) ↔ g.weightMap α n = 0
    exact (h.exactAt_weight α n).symm
  have hf : Module.finrank ℂ (LinearMap.range (f.weightMap α)) =
      Module.finrank ℂ (A.weight α) :=
    LinearMap.finrank_range_of_inj (h.weight_injective α)
  have hg : LinearMap.range (g.weightMap α) = ⊤ :=
    LinearMap.range_eq_top.mpr (h.weight_surjective α)
  have hrank := LinearMap.finrank_range_add_finrank_ker (g.weightMap α)
  rw [hg, finrank_top, ← hexact, hf] at hrank
  omega

/-- Graded dimensions are additive in a short exact sequence. -/
theorem gradedDim_eq_add (h : ShortExact f g) :
    gradedDim B = gradedDim A + gradedDim C := by
  funext e
  change (Module.finrank ℂ (B.weight (e + W.centralCharge / 24)) : ℂ) =
    (Module.finrank ℂ (A.weight (e + W.centralCharge / 24)) : ℂ) +
      (Module.finrank ℂ (C.weight (e + W.centralCharge / 24)) : ℂ)
  exact_mod_cast h.finrank_weight_eq (e + W.centralCharge / 24)

end ShortExact

end Hom

end OrdVModule

end VOA
