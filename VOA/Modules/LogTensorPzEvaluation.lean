/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinGraded

/-!
# Evaluation of logarithmic intertwiners in the completed generalized module

At the insertion point `z = 1` with the branch `log 1 = 0`, homogeneous input weights
`a,b` and output weight `c` select the single mode `a+b-c-1` and its zeroth logarithmic
coefficient. This file constructs that evaluation as an actual bilinear map to
`∏ c, W₃_[c]`, with arbitrary inputs assembled from their finite homogeneous decompositions.
It proves that this evaluation is faithful even when `L(0)` is not semisimple.
-/

namespace VOA.LogTensor.Pz

open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} {X : Type*} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup X] [Module ℂ X]

/-- The genuine generalized-weight completion. Its elements may have infinitely many
nonzero homogeneous components. -/
abbrev Completion (N : LogVModule W M₃) := ∀ a : ℂ, N.weight a

/-- A bilinear map assembled from its homogeneous blocks, using the actual internal
weight decompositions of its source modules. -/
noncomputable def fromBlocks (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (F : ∀ a b : ℂ, N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] X) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] X :=
  ((DFinsupp.lsum ℂ fun a =>
    (DFinsupp.lsum ℂ (M := fun b => N₂.weight b) (N := X)).toLinearMap ∘ₗ
      LinearMap.pi fun b => F a b) ∘ₗ (LogFin.gradEquiv N₁).symm.toLinearMap).compl₂
    (LogFin.gradEquiv N₂).symm.toLinearMap

@[simp] theorem fromBlocks_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (F : ∀ a b : ℂ, N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] X)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) :
    fromBlocks N₁ N₂ F x y = F a b ⟨x,hx⟩ ⟨y,hy⟩ := by
  classical
  have e1 := LogFin.gradEquiv_symm_of_mem N₁ hx
  have e2 := LogFin.gradEquiv_symm_of_mem N₂ hy
  simp only [fromBlocks, LinearMap.compl₂_apply, LinearMap.comp_apply]
  erw [e1, e2]
  erw [DFinsupp.lsum_single]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [DFinsupp.lsum_single]
  rfl

/-- Bilinear maps are determined by their restrictions to the genuine homogeneous
input pieces. -/
theorem bilinear_ext_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    {f g : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] X}
    (h : ∀ (a b : ℂ) (x : M₁) (y : M₂), x ∈ N₁.weight a → y ∈ N₂.weight b → f x y = g x y) :
    f = g := by
  ext x y
  refine LogFin.induction_on N₁ (C := fun x => f x y = g x y) x ?_ (by simp) ?_
  · intro a x hx
    refine LogFin.induction_on N₂ (C := fun y => f x y = g x y) y
      (fun b y hy => h a b x y hx hy) (by simp) ?_
    intro y z hy hz
    simp only [map_add,hy,hz]
  · intro x z hx hz
    simp only [map_add,LinearMap.add_apply,hx,hz]

/-- Evaluation on a single input weight pair and output weight. -/
noncomputable def evaluationBlock (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (a b c : ℂ) : N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] N₃.weight c :=
  LinearMap.mk₂ ℂ (fun x y => ⟨Y.1 (a+b-c-1) 0 x y, by
    have h := Y.2.mem_weight x.2 y.2 (a+b-c-1) 0
    convert h using 1 <;> ring⟩)
    (fun x x' y => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)
    (fun x y y' => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)

/-- Evaluation at `z = 1`, `log 1 = 0`, into the completed generalized module. -/
noncomputable def evaluateOne (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] Completion N₃ :=
  fromBlocks N₁ N₂ fun a b => LinearMap.mk₂ ℂ
    (fun x y c => evaluationBlock N₁ N₂ N₃ Y a b c x y)
    (fun x x' y => by funext c; simp)
    (fun s x y => by funext c; simp)
    (fun x y y' => by funext c; simp)
    (fun s x y => by funext c; simp)

/-- The defining coefficient formula uses the actual intertwiner, rather than an
independently stipulated map. -/
theorem evaluateOne_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (c : ℂ) :
    (evaluateOne N₁ N₂ N₃ Y x y c : M₃) = Y.1 (a+b-c-1) 0 x y := by
  rw [evaluateOne, fromBlocks_homogeneous N₁ N₂ _ hx hy]
  rfl

/-- The log-free mode on a homogeneous input pair is recovered from its evaluated
output component. -/
theorem recover_logZero_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (n : ℂ) :
    Y.1 n 0 x y = (evaluateOne N₁ N₂ N₃ Y x y (a+b-n-1) : M₃) := by
  rw [evaluateOne_homogeneous N₁ N₂ N₃ Y hx hy]
  congr 1
  ring

/-- Evaluation remains injective for generalized modules with arbitrary Jordan blocks.
The higher logarithmic coefficients are forced by the `L(0)` bracket. -/
theorem evaluateOne_injective (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) :
    Function.Injective (evaluateOne N₁ N₂ N₃) := by
  intro Y Z h
  apply logZero_injective
  ext n x y
  change Y.1 n 0 x y = Z.1 n 0 x y
  apply LogFin.induction_on N₁ x
  · intro a x hx
    apply LogFin.induction_on N₂ y
    · intro b y hy
      rw [recover_logZero_homogeneous N₁ N₂ N₃ Y hx hy,
        recover_logZero_homogeneous N₁ N₂ N₃ Z hx hy, h]
    · simp
    · intro y y' hy hy'
      simp only [map_add, hy, hy']
  · simp
  · intro x x' hx hx'
    simp only [map_add, LinearMap.add_apply, hx, hx']

end VOA.LogTensor.Pz
