/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Foundations.FormalDist3

/-!
# Four-variable formal distributions

This is the low-level four-variable companion to `FormalDist₃`.  Its immediate purpose is to
support the double-residue calculation in Li's local-system theorem, but nothing in this file
mentions fields or vertex algebras.

The file provides:

* `FormalDist₄ W = ℤ → ℤ → ℤ → ℤ → W`, with coefficient extensionality;
* the four coordinate shifts and all six pairwise difference operators, together with powers;
* the four single-coordinate and six double-coordinate formal residues;
* coefficientwise finite-support predicates for one- and two-parameter families;
* coefficientwise `finsum` constructions, residue-commutation lemmas, and a jointly-finite
  Fubini theorem proved through product-index reindexing.

Formal residue itself is coefficient extraction and needs no convergence assumption.  The
finite-support hypotheses enter exactly when auxiliary coefficient families are summed; this
keeps later double-delta calculations algebraic and prevents an infinite-support `finsum` from
silently collapsing to zero.
-/

namespace VOA

open scoped BigOperators

universe u v w

/-- A four-variable formal distribution.  `f i j k l` is the coefficient of
`z₁ⁱ z₂ʲ z₃ᵏ z₄ˡ`. -/
def FormalDist₄ (W : Type*) : Type _ := ℤ → ℤ → ℤ → ℤ → W

namespace FormalDist₄

variable {W : Type u}

instance instAddCommGroup [AddCommGroup W] : AddCommGroup (FormalDist₄ W) :=
  inferInstanceAs (AddCommGroup (ℤ → ℤ → ℤ → ℤ → W))

instance instModule {R : Type v} [Semiring R] [AddCommGroup W] [Module R W] :
    Module R (FormalDist₄ W) := inferInstanceAs (Module R (ℤ → ℤ → ℤ → ℤ → W))

@[ext]
theorem ext {f g : FormalDist₄ W} (h : ∀ i j k l, f i j k l = g i j k l) : f = g :=
  funext fun i => funext fun j => funext fun k => funext (h i j k)

section ComplexModule

variable [AddCommGroup W] [Module ℂ W]

/-! ## Coordinate shifts -/

/-- Multiplication by `z₁`. -/
def shift₁ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W where
  toFun f := fun i j k l => f (i - 1) j k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₂`. -/
def shift₂ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W where
  toFun f := fun i j k l => f i (j - 1) k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₃`. -/
def shift₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W where
  toFun f := fun i j k l => f i j (k - 1) l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₄`. -/
def shift₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W where
  toFun f := fun i j k l => f i j k (l - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift₁_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    shift₁ f i j k l = f (i - 1) j k l := rfl

@[simp] theorem shift₂_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    shift₂ f i j k l = f i (j - 1) k l := rfl

@[simp] theorem shift₃_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    shift₃ f i j k l = f i j (k - 1) l := rfl

@[simp] theorem shift₄_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    shift₄ f i j k l = f i j k (l - 1) := rfl

/-! ## Pairwise differences -/

/-- Multiplication by `z₁-z₂`. -/
def mulBySub₁₂ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₁ - shift₂

/-- Multiplication by `z₁-z₃`. -/
def mulBySub₁₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₁ - shift₃

/-- Multiplication by `z₁-z₄`. -/
def mulBySub₁₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₁ - shift₄

/-- Multiplication by `z₂-z₃`. -/
def mulBySub₂₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₂ - shift₃

/-- Multiplication by `z₂-z₄`. -/
def mulBySub₂₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₂ - shift₄

/-- Multiplication by `z₃-z₄`. -/
def mulBySub₃₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := shift₃ - shift₄

@[simp] theorem mulBySub₁₂_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₁₂ f i j k l = f (i - 1) j k l - f i (j - 1) k l := rfl

@[simp] theorem mulBySub₁₃_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₁₃ f i j k l = f (i - 1) j k l - f i j (k - 1) l := rfl

@[simp] theorem mulBySub₁₄_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₁₄ f i j k l = f (i - 1) j k l - f i j k (l - 1) := rfl

@[simp] theorem mulBySub₂₃_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₂₃ f i j k l = f i (j - 1) k l - f i j (k - 1) l := rfl

@[simp] theorem mulBySub₂₄_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₂₄ f i j k l = f i (j - 1) k l - f i j k (l - 1) := rfl

@[simp] theorem mulBySub₃₄_apply (f : FormalDist₄ W) (i j k l : ℤ) :
    mulBySub₃₄ f i j k l = f i j (k - 1) l - f i j k (l - 1) := rfl

/-! ## Powers of pairwise differences -/

def mulBySub₁₂Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₁₂ ^ N
def mulBySub₁₃Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₁₃ ^ N
def mulBySub₁₄Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₁₄ ^ N
def mulBySub₂₃Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₂₃ ^ N
def mulBySub₂₄Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₂₄ ^ N
def mulBySub₃₄Pow (N : ℕ) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W := mulBySub₃₄ ^ N

@[simp] theorem mulBySub₁₂Pow_zero :
    (mulBySub₁₂Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl
@[simp] theorem mulBySub₁₃Pow_zero :
    (mulBySub₁₃Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl
@[simp] theorem mulBySub₁₄Pow_zero :
    (mulBySub₁₄Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl
@[simp] theorem mulBySub₂₃Pow_zero :
    (mulBySub₂₃Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl
@[simp] theorem mulBySub₂₄Pow_zero :
    (mulBySub₂₄Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl
@[simp] theorem mulBySub₃₄Pow_zero :
    (mulBySub₃₄Pow 0 : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) = LinearMap.id := rfl

theorem mulBySub₁₂Pow_succ (N : ℕ) :
    (mulBySub₁₂Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₁₂.comp (mulBySub₁₂Pow N) := by
  rw [mulBySub₁₂Pow, mulBySub₁₂Pow, pow_succ']
  rfl

theorem mulBySub₁₃Pow_succ (N : ℕ) :
    (mulBySub₁₃Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₁₃.comp (mulBySub₁₃Pow N) := by
  rw [mulBySub₁₃Pow, mulBySub₁₃Pow, pow_succ']
  rfl

theorem mulBySub₁₄Pow_succ (N : ℕ) :
    (mulBySub₁₄Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₁₄.comp (mulBySub₁₄Pow N) := by
  rw [mulBySub₁₄Pow, mulBySub₁₄Pow, pow_succ']
  rfl

theorem mulBySub₂₃Pow_succ (N : ℕ) :
    (mulBySub₂₃Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₂₃.comp (mulBySub₂₃Pow N) := by
  rw [mulBySub₂₃Pow, mulBySub₂₃Pow, pow_succ']
  rfl

theorem mulBySub₂₄Pow_succ (N : ℕ) :
    (mulBySub₂₄Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₂₄.comp (mulBySub₂₄Pow N) := by
  rw [mulBySub₂₄Pow, mulBySub₂₄Pow, pow_succ']
  rfl

theorem mulBySub₃₄Pow_succ (N : ℕ) :
    (mulBySub₃₄Pow (N + 1) : FormalDist₄ W →ₗ[ℂ] FormalDist₄ W) =
      mulBySub₃₄.comp (mulBySub₃₄Pow N) := by
  rw [mulBySub₃₄Pow, mulBySub₃₄Pow, pow_succ']
  rfl

/-! ## Single and double formal residues -/

/-- Residue in the first coordinate; the remaining order is `(z₂,z₃,z₄)`. -/
def res₁ : FormalDist₄ W →ₗ[ℂ] FormalDist₃ W where
  toFun f := fun j k l => f (-1) j k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residue in the second coordinate; the remaining order is `(z₁,z₃,z₄)`. -/
def res₂ : FormalDist₄ W →ₗ[ℂ] FormalDist₃ W where
  toFun f := fun i k l => f i (-1) k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residue in the third coordinate; the remaining order is `(z₁,z₂,z₄)`. -/
def res₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₃ W where
  toFun f := fun i j l => f i j (-1) l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residue in the fourth coordinate; the remaining order is `(z₁,z₂,z₃)`. -/
def res₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₃ W where
  toFun f := fun i j k => f i j k (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem res₁_apply (f : FormalDist₄ W) (j k l : ℤ) : res₁ f j k l = f (-1) j k l := rfl
@[simp] theorem res₂_apply (f : FormalDist₄ W) (i k l : ℤ) : res₂ f i k l = f i (-1) k l := rfl
@[simp] theorem res₃_apply (f : FormalDist₄ W) (i j l : ℤ) : res₃ f i j l = f i j (-1) l := rfl
@[simp] theorem res₄_apply (f : FormalDist₄ W) (i j k : ℤ) : res₄ f i j k = f i j k (-1) := rfl

/-- Residues in coordinates `1,2`; the remaining order is `(z₃,z₄)`. -/
def res₁₂ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun k l => f (-1) (-1) k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residues in coordinates `1,3`; the remaining order is `(z₂,z₄)`. -/
def res₁₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun j l => f (-1) j (-1) l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residues in coordinates `1,4`; the remaining order is `(z₂,z₃)`. -/
def res₁₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun j k => f (-1) j k (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residues in coordinates `2,3`; the remaining order is `(z₁,z₄)`. -/
def res₂₃ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun i l => f i (-1) (-1) l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residues in coordinates `2,4`; the remaining order is `(z₁,z₃)`. -/
def res₂₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun i k => f i (-1) k (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Residues in coordinates `3,4`; the remaining order is `(z₁,z₂)`. -/
def res₃₄ : FormalDist₄ W →ₗ[ℂ] FormalDist₂ W where
  toFun f := fun i j => f i j (-1) (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem res₁₂_apply (f : FormalDist₄ W) (k l : ℤ) :
    res₁₂ f k l = f (-1) (-1) k l := rfl
@[simp] theorem res₁₃_apply (f : FormalDist₄ W) (j l : ℤ) :
    res₁₃ f j l = f (-1) j (-1) l := rfl
@[simp] theorem res₁₄_apply (f : FormalDist₄ W) (j k : ℤ) :
    res₁₄ f j k = f (-1) j k (-1) := rfl
@[simp] theorem res₂₃_apply (f : FormalDist₄ W) (i l : ℤ) :
    res₂₃ f i l = f i (-1) (-1) l := rfl
@[simp] theorem res₂₄_apply (f : FormalDist₄ W) (i k : ℤ) :
    res₂₄ f i k = f i (-1) k (-1) := rfl
@[simp] theorem res₃₄_apply (f : FormalDist₄ W) (i j : ℤ) :
    res₃₄ f i j = f i j (-1) (-1) := rfl

end ComplexModule

/-! ## Coefficientwise algebraic summability -/

variable [AddCommMonoid W]

/-- Every coefficient of a one-parameter family has finite parameter support. -/
def CoeffFinite {ι : Type v} (F : ι → FormalDist₄ W) : Prop :=
  ∀ i j k l, (Function.support fun a => F a i j k l).Finite

/-- Every coefficient of a two-parameter family has jointly finite support. -/
def CoeffJointFinite {ι : Type v} {κ : Type w} (F : ι → κ → FormalDist₄ W) : Prop :=
  ∀ i j k l, (Function.support fun p : ι × κ => F p.1 p.2 i j k l).Finite

/-- Coefficientwise algebraic sum of a family of four-variable distributions. -/
noncomputable def coeffFinsum {ι : Type v} (F : ι → FormalDist₄ W) : FormalDist₄ W :=
  fun i j k l => ∑ᶠ a, F a i j k l

@[simp] theorem coeffFinsum_apply {ι : Type v} (F : ι → FormalDist₄ W) (i j k l : ℤ) :
    coeffFinsum F i j k l = ∑ᶠ a, F a i j k l := rfl

/-- Iterated coefficientwise algebraic sum of a two-parameter family. -/
noncomputable def coeffFinsum₂ {ι : Type v} {κ : Type w} (F : ι → κ → FormalDist₄ W) :
    FormalDist₄ W := coeffFinsum fun a => coeffFinsum (F a)

@[simp] theorem coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ W) (i j k l : ℤ) :
    coeffFinsum₂ F i j k l = ∑ᶠ a, ∑ᶠ b, F a b i j k l := rfl

theorem CoeffFinite.res₁ {ι : Type v} {F : ι → FormalDist₄ W} (hF : CoeffFinite F) :
    ∀ j k l, (Function.support fun a => F a (-1) j k l).Finite :=
  fun j k l => hF (-1) j k l

theorem CoeffFinite.res₂ {ι : Type v} {F : ι → FormalDist₄ W} (hF : CoeffFinite F) :
    ∀ i k l, (Function.support fun a => F a i (-1) k l).Finite :=
  fun i k l => hF i (-1) k l

theorem CoeffFinite.res₃ {ι : Type v} {F : ι → FormalDist₄ W} (hF : CoeffFinite F) :
    ∀ i j l, (Function.support fun a => F a i j (-1) l).Finite :=
  fun i j l => hF i j (-1) l

theorem CoeffFinite.res₄ {ι : Type v} {F : ι → FormalDist₄ W} (hF : CoeffFinite F) :
    ∀ i j k, (Function.support fun a => F a i j k (-1)).Finite :=
  fun i j k => hF i j k (-1)

theorem CoeffJointFinite.res₁₂ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ k l, (Function.support fun p : ι × κ => F p.1 p.2 (-1) (-1) k l).Finite :=
  fun k l => hF (-1) (-1) k l

theorem CoeffJointFinite.res₁₃ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ j l, (Function.support fun p : ι × κ => F p.1 p.2 (-1) j (-1) l).Finite :=
  fun j l => hF (-1) j (-1) l

theorem CoeffJointFinite.res₁₄ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ j k, (Function.support fun p : ι × κ => F p.1 p.2 (-1) j k (-1)).Finite :=
  fun j k => hF (-1) j k (-1)

theorem CoeffJointFinite.res₂₃ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ i l, (Function.support fun p : ι × κ => F p.1 p.2 i (-1) (-1) l).Finite :=
  fun i l => hF i (-1) (-1) l

theorem CoeffJointFinite.res₂₄ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ i k, (Function.support fun p : ι × κ => F p.1 p.2 i (-1) k (-1)).Finite :=
  fun i k => hF i (-1) k (-1)

theorem CoeffJointFinite.res₃₄ {ι : Type v} {κ : Type w}
    {F : ι → κ → FormalDist₄ W} (hF : CoeffJointFinite F) :
    ∀ i j, (Function.support fun p : ι × κ => F p.1 p.2 i j (-1) (-1)).Finite :=
  fun i j => hF i j (-1) (-1)

/-! Residues commute coefficientwise with the sanctioned finite algebraic sums.  The
support argument is carried explicitly even though coefficient extraction makes the displayed
equalities definitional; later users can therefore retain the finiteness certificate needed by
`finsum` algebra. -/

section ResidueSummation

variable {X : Type u} [AddCommGroup X] [Module ℂ X]

theorem res₁_coeffFinsum_apply {ι : Type v} (F : ι → FormalDist₄ X)
    (_hF : CoeffFinite F) (j k l : ℤ) :
    res₁ (coeffFinsum F) j k l = ∑ᶠ a, res₁ (F a) j k l := rfl

theorem res₂_coeffFinsum_apply {ι : Type v} (F : ι → FormalDist₄ X)
    (_hF : CoeffFinite F) (i k l : ℤ) :
    res₂ (coeffFinsum F) i k l = ∑ᶠ a, res₂ (F a) i k l := rfl

theorem res₃_coeffFinsum_apply {ι : Type v} (F : ι → FormalDist₄ X)
    (_hF : CoeffFinite F) (i j l : ℤ) :
    res₃ (coeffFinsum F) i j l = ∑ᶠ a, res₃ (F a) i j l := rfl

theorem res₄_coeffFinsum_apply {ι : Type v} (F : ι → FormalDist₄ X)
    (_hF : CoeffFinite F) (i j k : ℤ) :
    res₄ (coeffFinsum F) i j k = ∑ᶠ a, res₄ (F a) i j k := rfl

theorem res₁₂_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (k l : ℤ) :
    res₁₂ (coeffFinsum₂ F) k l = ∑ᶠ a, ∑ᶠ b, res₁₂ (F a b) k l := rfl

theorem res₁₃_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (j l : ℤ) :
    res₁₃ (coeffFinsum₂ F) j l = ∑ᶠ a, ∑ᶠ b, res₁₃ (F a b) j l := rfl

theorem res₁₄_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (j k : ℤ) :
    res₁₄ (coeffFinsum₂ F) j k = ∑ᶠ a, ∑ᶠ b, res₁₄ (F a b) j k := rfl

theorem res₂₃_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (i l : ℤ) :
    res₂₃ (coeffFinsum₂ F) i l = ∑ᶠ a, ∑ᶠ b, res₂₃ (F a b) i l := rfl

theorem res₂₄_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (i k : ℤ) :
    res₂₄ (coeffFinsum₂ F) i k = ∑ᶠ a, ∑ᶠ b, res₂₄ (F a b) i k := rfl

theorem res₃₄_coeffFinsum₂_apply {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ X) (_hF : CoeffJointFinite F) (i j : ℤ) :
    res₃₄ (coeffFinsum₂ F) i j = ∑ᶠ a, ∑ᶠ b, res₃₄ (F a b) i j := rfl

end ResidueSummation

/-! ## Fubini and reindexing -/

/-- Joint finite support makes the two orders of algebraic summation agree. -/
theorem finsum_finsum_comm_of_joint_finite {ι : Type v} {κ : Type w}
    (F : ι → κ → W)
    (hF : (Function.support fun p : ι × κ => F p.1 p.2).Finite) :
    (∑ᶠ b, ∑ᶠ a, F a b) = ∑ᶠ a, ∑ᶠ b, F a b := by
  have hswap : (Function.support fun q : κ × ι => F q.2 q.1).Finite := by
    have hpre : (Function.support fun q : κ × ι => F q.2 q.1) =
        (Equiv.prodComm κ ι) ⁻¹' (Function.support fun p : ι × κ => F p.1 p.2) := rfl
    rw [hpre]
    exact hF.preimage ((Equiv.prodComm κ ι).injective.injOn)
  calc
    (∑ᶠ b, ∑ᶠ a, F a b) = ∑ᶠ q : κ × ι, F q.2 q.1 :=
      (finsum_curry (fun q : κ × ι => F q.2 q.1) hswap).symm
    _ = ∑ᶠ p : ι × κ, F p.1 p.2 :=
      finsum_comp_equiv (Equiv.prodComm κ ι) (f := fun p : ι × κ => F p.1 p.2)
    _ = ∑ᶠ a, ∑ᶠ b, F a b := finsum_curry (fun p : ι × κ => F p.1 p.2) hF

/-- Reindex both variables of an iterated algebraic sum by equivalences. -/
theorem finsum_finsum_reindex {ι ι' : Type v} {κ κ' : Type w}
    (eι : ι ≃ ι') (eκ : κ ≃ κ') (F : ι' → κ' → W) :
    (∑ᶠ a, ∑ᶠ b, F (eι a) (eκ b)) = ∑ᶠ a', ∑ᶠ b', F a' b' := by
  rw [show (fun a => ∑ᶠ b, F (eι a) (eκ b)) =
      (fun a => ∑ᶠ b', F a b') ∘ eι from by
        funext a
        exact finsum_comp_equiv eκ (f := fun b' => F (eι a) b')]
  exact finsum_comp_equiv eι (f := fun a' => ∑ᶠ b', F a' b')

/-- Coefficientwise Fubini for four-variable distributions. -/
theorem coeffFinsum₂_comm {ι : Type v} {κ : Type w}
    (F : ι → κ → FormalDist₄ W) (hF : CoeffJointFinite F) :
    coeffFinsum₂ F = coeffFinsum₂ (fun b a => F a b) := by
  ext i j k l
  rw [coeffFinsum₂_apply, coeffFinsum₂_apply]
  exact (finsum_finsum_comm_of_joint_finite
    (fun a b => F a b i j k l) (hF i j k l)).symm

end FormalDist₄

end VOA
