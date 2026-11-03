/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ReconstructionPairing
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Tannaka reconstruction — the algebra `End(ω) = ∏ End(ω X_i)`

Let `D` be a fusion category over `ℂ` (T1 `FusionCategory`) and `ω : D ⥤ FGModuleCat ℂ` an
additive `ℂ`-linear functor.

* `Decomp X` — a decomposition `𝟙 X = Σ_k π_k ≫ ι_k` through simple objects; `decomp X` a chosen
  one (from `FusionCategory.semisimple`);
* `RAlg ω := ∀ i, End (ω X_i)` — the (finite-dimensional) algebra of natural endomorphisms of `ω`;
* `extMor a X` — the natural extension of `a ∈ RAlg ω` to every object;
  `extMor_natural` (`ω h ≫ ext a Y = ext a X ≫ ω h`), `extMor_simple` (`ext a X_i = a_i`),
  `extMor_mul`, `extMor_one`, `extMor_add`, `extMor_smul`; packaged as `extAlgHom`;
* `exists_map_eq_of_commute` — **fullness criterion**: a linear map `ω X ⟶ ω Y` commuting with
  every `ext a` is `ω h` for some `h : X ⟶ Y`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open CategoryTheory MonoidalCategory Limits Module

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [HasKernels D] [HasFiniteBiproducts D] [RightRigidCategory D] [F : FusionCategory D]

/-- A decomposition `𝟙 X = Σ_k π_k ≫ ι_k` through the simple objects. -/
structure Decomp (X : D) where
  n : ℕ
  f : Fin n → F.ι
  π : ∀ k, X ⟶ F.simple (f k)
  ι : ∀ k, F.simple (f k) ⟶ X
  total : ∑ k, π k ≫ ι k = 𝟙 X

theorem exists_decomp (X : D) : Nonempty (Decomp X) := by
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
  refine ⟨⟨n, f, fun k => e.hom ≫ biproduct.π _ k, fun k => biproduct.ι (fun k => F.simple (f k)) k ≫ e.inv, ?_⟩⟩
  simp only [Category.assoc]
  rw [← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, e.hom_inv_id]

/-- A chosen decomposition through simples. -/
def decomp (X : D) : Decomp X := Classical.choice (exists_decomp X)

/-- The trivial decomposition of a simple object. -/
def decompSimple (i : F.ι) : Decomp (F.simple i) where
  n := 1
  f := fun _ => i
  π := fun _ => 𝟙 _
  ι := fun _ => 𝟙 _
  total := by simp

/-- Schur: morphisms between non-isomorphic simples vanish. -/
theorem simple_hom_eq_zero {i j : F.ι} (h : i ≠ j) (c : F.simple i ⟶ F.simple j) : c = 0 := by
  by_contra hc
  haveI := F.isSimple i
  haveI := F.isSimple j
  haveI := isIso_of_hom_simple hc
  exact h (F.inequivalent i j ⟨asIso c⟩)

/-- Schur: endomorphisms of a simple are scalars. -/
theorem simple_end_eq_smul {i : F.ι} (c : F.simple i ⟶ F.simple i) : ∃ t : ℂ, c = t • 𝟙 _ := by
  haveI := F.isSimple i
  haveI := F.finiteDimensional (F.simple i) (F.simple i)
  obtain ⟨t, ht⟩ := endomorphism_simple_eq_smul_id ℂ c
  exact ⟨t, ht.symm⟩

variable (ω : D ⥤ FGModuleCat ℂ)

/-- The algebra `∏_i End(ω X_i)` of natural endomorphisms of `ω`. -/
def RAlg := ∀ i : F.ι, (ω.obj (F.simple i) ⟶ ω.obj (F.simple i))

instance : Ring (RAlg ω) := inferInstanceAs (Ring (∀ i : F.ι, End (ω.obj (F.simple i))))
instance : Algebra ℂ (RAlg ω) := inferInstanceAs (Algebra ℂ (∀ i : F.ι, End (ω.obj (F.simple i))))
instance : Module.Finite ℂ (RAlg ω) :=
  inferInstanceAs (Module.Finite ℂ (∀ i : F.ι, (ω.obj (F.simple i) ⟶ ω.obj (F.simple i))))

@[simp] theorem RAlg.mul_apply (a b : RAlg ω) (i : F.ι) : (a * b) i = b i ≫ a i := rfl
@[simp] theorem RAlg.one_apply (i : F.ι) : (1 : RAlg ω) i = 𝟙 _ := rfl
@[simp] theorem RAlg.add_apply (a b : RAlg ω) (i : F.ι) : (a + b) i = a i + b i := rfl
@[simp] theorem RAlg.smul_apply (t : ℂ) (a : RAlg ω) (i : F.ι) : (t • a) i = t • a i := rfl
@[simp] theorem RAlg.zero_apply (i : F.ι) : (0 : RAlg ω) i = 0 := rfl
@[simp] theorem RAlg.sum_apply {J : Type*} (s : Finset J) (a : J → RAlg ω) (i : F.ι) :
    (∑ j ∈ s, a j) i = ∑ j ∈ s, a j i := Finset.sum_apply i s a

@[ext] theorem RAlg.ext {a b : RAlg ω} (h : ∀ i, a i = b i) : a = b := funext h

theorem end_add_comp {V W : FGModuleCat ℂ} (x y : End V) (g : V ⟶ W) :
    (x + y) ≫ g = x ≫ g + y ≫ g := Preadditive.add_comp _ _ _ _ _ _
theorem end_smul_comp {V W : FGModuleCat ℂ} (t : ℂ) (x : End V) (g : V ⟶ W) :
    (t • x) ≫ g = t • (x ≫ g) := Linear.smul_comp _ _ _ _ _ _

variable [ω.Additive] [ω.Linear ℂ]

/-- Schur, transported: every `a ∈ RAlg ω` commutes with `ω` of a morphism between simples. -/
theorem comm_map_simple (a : RAlg ω) {i j : F.ι} (c : F.simple i ⟶ F.simple j) :
    a i ≫ ω.map c = ω.map c ≫ a j := by
  by_cases h : i = j
  · subst h
    obtain ⟨t, rfl⟩ := simple_end_eq_smul c
    rw [Functor.map_smul, ω.map_id]
    simp
  · rw [simple_hom_eq_zero h c, Functor.map_zero]
    simp

/-- The sum attached to a decomposition. -/
def extWith (a : RAlg ω) {X : D} (d : Decomp X) : ω.obj X ⟶ ω.obj X :=
  ∑ k, ω.map (d.π k) ≫ a (d.f k) ≫ ω.map (d.ι k)

theorem map_total {X : D} (d : Decomp X) : ∑ k, ω.map (d.π k) ≫ ω.map (d.ι k) = 𝟙 _ := by
  simp_rw [← ω.map_comp]
  rw [← ω.map_sum, d.total, ω.map_id]

/-- Naturality of the decomposition sums, for any two decompositions. -/
theorem extWith_natural (a : RAlg ω) {X Y : D} (d : Decomp X) (d' : Decomp Y) (h : X ⟶ Y) :
    extWith ω a d ≫ ω.map h = ω.map h ≫ extWith ω a d' := by
  unfold extWith
  have e1 : ∀ k, ω.map (d.ι k) ≫ ω.map h =
      ∑ l, ω.map (d.ι k ≫ h ≫ d'.π l) ≫ ω.map (d'.ι l) := fun k => by
    conv_lhs => rw [← Category.comp_id (ω.map h), ← map_total ω d', Preadditive.comp_sum,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Functor.map_comp, Category.assoc]
  have e2 : ∀ l, ω.map h ≫ ω.map (d'.π l) =
      ∑ k, ω.map (d.π k) ≫ ω.map (d.ι k ≫ h ≫ d'.π l) := fun l => by
    conv_lhs => rw [← Category.id_comp (ω.map h), ← map_total ω d]
    simp only [Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Functor.map_comp, Category.assoc]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  simp_rw [Category.assoc, e1, Preadditive.comp_sum]
  conv_rhs => arg 2; ext l; rw [← Category.assoc, e2, Preadditive.sum_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Category.assoc]
  rw [← Category.assoc (a _), comm_map_simple]
  simp only [Category.assoc]

/-- The natural extension of `a ∈ RAlg ω` to the object `X`. -/
def extMor (a : RAlg ω) (X : D) : ω.obj X ⟶ ω.obj X := extWith ω a (decomp X)

theorem extMor_eq_extWith (a : RAlg ω) {X : D} (d : Decomp X) : extMor ω a X = extWith ω a d := by
  have := extWith_natural ω a (decomp X) d (𝟙 X)
  rwa [ω.map_id, Category.comp_id, Category.id_comp] at this

/-- **Naturality** of `ext a`. -/
@[reassoc]
theorem extMor_natural (a : RAlg ω) {X Y : D} (h : X ⟶ Y) :
    extMor ω a X ≫ ω.map h = ω.map h ≫ extMor ω a Y :=
  extWith_natural ω a _ _ h

@[simp] theorem extMor_simple (a : RAlg ω) (i : F.ι) : extMor ω a (F.simple i) = a i := by
  rw [extMor_eq_extWith ω a (decompSimple i)]
  simp [extWith, decompSimple]

/-- Any endomorphism family is recovered from its values on simples through a decomposition. -/
theorem extMor_eq_sum (a : RAlg ω) {X : D} (d : Decomp X) :
    extMor ω a X = ∑ k, ω.map (d.π k) ≫ a (d.f k) ≫ ω.map (d.ι k) :=
  extMor_eq_extWith ω a d

@[simp] theorem extMor_mul (a b : RAlg ω) (X : D) :
    extMor ω (a * b) X = extMor ω b X ≫ extMor ω a X := by
  rw [extMor_eq_sum ω (a * b) (decomp X), extMor_eq_sum ω b (decomp X), Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Category.assoc, Category.assoc, ← extMor_natural, extMor_simple, RAlg.mul_apply, Category.assoc]

@[simp] theorem extMor_one (X : D) : extMor ω 1 X = 𝟙 _ := by
  rw [extMor_eq_sum ω 1 (decomp X)]
  simp only [RAlg.one_apply, Category.id_comp]
  exact map_total ω _

@[simp] theorem extMor_add (a b : RAlg ω) (X : D) :
    extMor ω (a + b) X = extMor ω a X + extMor ω b X := by
  simp only [extMor_eq_sum ω _ (decomp X), RAlg.add_apply, Preadditive.add_comp,
    Preadditive.comp_add, Finset.sum_add_distrib]

@[simp] theorem extMor_smul (t : ℂ) (a : RAlg ω) (X : D) :
    extMor ω (t • a) X = t • extMor ω a X := by
  simp only [extMor_eq_sum ω _ (decomp X), RAlg.smul_apply, Linear.smul_comp, Linear.comp_smul,
    Finset.smul_sum]

@[simp] theorem extMor_zero (X : D) : extMor ω 0 X = 0 := by
  simpa using extMor_smul ω 0 0 X

@[simp] theorem extMor_sum {J : Type*} (s : Finset J) (a : J → RAlg ω) (X : D) :
    extMor ω (∑ j ∈ s, a j) X = ∑ j ∈ s, extMor ω (a j) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, extMor_add, ih]

/-- `ext` as an algebra homomorphism `RAlg ω →ₐ[ℂ] End (ω X)`. -/
def extAlgHom (X : D) : RAlg ω →ₐ[ℂ] End (ω.obj X) where
  toFun a := extMor ω a X
  map_one' := extMor_one ω X
  map_mul' a b := by rw [extMor_mul, End.mul_def]
  map_zero' := extMor_zero ω X
  map_add' a b := extMor_add ω a b X
  commutes' t := by
    change extMor ω (t • 1) X = t • (1 : End (ω.obj X))
    rw [extMor_smul, extMor_one]; rfl

/-- `ext` as a linear map. -/
def extLin (X : D) : RAlg ω →ₗ[ℂ] (ω.obj X ⟶ ω.obj X) where
  toFun a := extMor ω a X
  map_add' a b := extMor_add ω a b X
  map_smul' t a := extMor_smul ω t a X

@[simp] theorem extLin_apply (X : D) (a : RAlg ω) : extLin ω X a = extMor ω a X := rfl

theorem eq_of_extMor_simple {a b : RAlg ω} (h : ∀ i, extMor ω a (F.simple i) = extMor ω b (F.simple i)) :
    a = b := RAlg.ext ω fun i => by simpa using h i

/-- The element of `RAlg ω` supported at one simple. -/
def single (i : F.ι) (x : ω.obj (F.simple i) ⟶ ω.obj (F.simple i)) : RAlg ω :=
  Pi.single (M := fun j => ω.obj (F.simple j) ⟶ ω.obj (F.simple j)) i x

@[simp] theorem single_apply_self (i : F.ι) (x : ω.obj (F.simple i) ⟶ ω.obj (F.simple i)) :
    single ω i x i = x := by
  simp [single]

theorem single_apply_ne {i j : F.ι} (h : j ≠ i) (x : ω.obj (F.simple i) ⟶ ω.obj (F.simple i)) :
    single ω i x j = 0 := by
  simp [single, Pi.single_apply, h]

/-- A linear map commuting with all of `End V` is a scalar. -/
theorem exists_smul_of_commute {V : FGModuleCat ℂ} (ψ : V ⟶ V)
    (h : ∀ x : V ⟶ V, x ≫ ψ = ψ ≫ x) : ∃ t : ℂ, ψ = t • 𝟙 V := by
  have hc : ψ.hom.hom ∈ Set.center (Module.End ℂ V) := by
    rw [Semigroup.mem_center_iff]
    intro g
    have := congrArg (fun m : V ⟶ V => m.hom.hom) (h (FGModuleCat.ofHom g))
    simp only [FGModuleCat.hom_hom_comp] at this
    simpa [Module.End.mul_eq_comp] using this.symm
  obtain ⟨t, _, ht⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨t, ?_⟩
  ext v
  have := LinearMap.congr_fun ht v
  simpa using this

/-- Schur for the fiber: a map `ω X_i ⟶ ω X_j` intertwining all of `RAlg ω` comes from `D`. -/
theorem exists_map_eq_of_commute_simple {i j : F.ι} (ψ : ω.obj (F.simple i) ⟶ ω.obj (F.simple j))
    (h : ∀ a : RAlg ω, a i ≫ ψ = ψ ≫ a j) : ∃ c : F.simple i ⟶ F.simple j, ω.map c = ψ := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨t, rfl⟩ := exists_smul_of_commute ψ fun x => by
      simpa using h (single ω i x)
    exact ⟨t • 𝟙 _, by rw [Functor.map_smul, ω.map_id]⟩
  · refine ⟨0, ?_⟩
    have := h (single ω i (𝟙 _))
    rw [single_apply_self, single_apply_ne ω (Ne.symm hij), Category.id_comp] at this
    have h0 : ψ = 0 := this.trans Limits.comp_zero
    rw [h0, Functor.map_zero]

/-- **Fullness criterion.** A linear map `ω X ⟶ ω Y` commuting with `ext a` for every
`a ∈ RAlg ω` is `ω.map h` for a morphism `h : X ⟶ Y`. -/
theorem exists_map_eq_of_commute {X Y : D} (φ : ω.obj X ⟶ ω.obj Y)
    (h : ∀ a : RAlg ω, extMor ω a X ≫ φ = φ ≫ extMor ω a Y) : ∃ g : X ⟶ Y, ω.map g = φ := by
  let d := decomp X
  let d' := decomp Y
  have hψ : ∀ k l, ∃ c : F.simple (d.f k) ⟶ F.simple (d'.f l),
      ω.map c = ω.map (d.ι k) ≫ φ ≫ ω.map (d'.π l) := fun k l => by
    apply exists_map_eq_of_commute_simple
    intro a
    rw [← extMor_simple ω a (d.f k), ← extMor_simple ω a (d'.f l), extMor_natural_assoc,
      reassoc_of% (h a), extMor_natural]
    simp only [Category.assoc]
  choose c hc using hψ
  refine ⟨∑ k, ∑ l, d.π k ≫ c k l ≫ d'.ι l, ?_⟩
  rw [ω.map_sum]
  simp_rw [ω.map_sum, Functor.map_comp, hc]
  have : φ = (∑ k, ω.map (d.π k) ≫ ω.map (d.ι k)) ≫ φ ≫ ∑ l, ω.map (d'.π l) ≫ ω.map (d'.ι l) := by
    rw [map_total, map_total, Category.id_comp, Category.comp_id]
  conv_rhs => rw [this]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Preadditive.comp_sum, Category.assoc]

end VOA.Huang.TensorCat.Reconstruction
