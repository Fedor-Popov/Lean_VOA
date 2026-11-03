/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPostcompose

/-! # Actual source functoriality of logarithmic intertwining operators

Genuine weak-module maps can be inserted in both inputs, preserving finite
log degree, uniform truncation, the coupled derivative, and full Jacobi.
-/
namespace VOA.LogTensor
universe u v₁ v₂ v₃ w₁ w₂
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  {X₁ : Type w₁} {X₂ : Type w₂}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂]

/-- Insert actual linear maps in both source arguments of every logarithmic mode. -/
noncomputable def preModes (f : X₁ →ₗ[ℂ] M₁) (g : X₂ →ₗ[ℂ] M₂)
    (Y : LogModes M₁ M₂ M₃) : LogModes X₁ X₂ M₃ :=
  fun n k => (Y n k).comp f |>.compl₂ g

@[simp] theorem preModes_apply (f : X₁ →ₗ[ℂ] M₁) (g : X₂ →ₗ[ℂ] M₂)
    (Y : LogModes M₁ M₂ M₃) (n : ℂ) (k : ℕ) (x : X₁) (y : X₂) :
    preModes f g Y n k x y = Y n k (f x) (g y) := rfl

variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {B₁ : WeakModule W X₁} {B₂ : WeakModule W X₂}

/-- Actual weak source homomorphisms preserve the genuine logarithmic axioms. -/
theorem IsLogIntertwining.precompose {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (f : B₁.Hom A₁) (g : B₂.Hom A₂) :
    IsLogIntertwining B₁ B₂ A₃ (preModes f.toLinearMap g.toLinearMap Y) := by
  have hf : ∀ (u : V) (p : ℤ) (x : X₁),
      f.toLinearMap (mode (B₁.YM u) p x) = mode (A₁.YM u) p (f.toLinearMap x) := f.map_act
  have hg : ∀ (u : V) (p : ℤ) (y : X₂),
      g.toLinearMap (mode (B₂.YM u) p y) = mode (A₂.YM u) p (g.toLinearMap y) := g.map_act
  refine ⟨?_,?_,?_,?_⟩
  · intro x y n
    exact hY.logFinite (f.toLinearMap x) (g.toLinearMap y) n
  · intro x y n
    exact hY.truncation (f.toLinearMap x) (g.toLinearMap y) n
  · intro x n k
    apply LinearMap.ext
    intro y
    have h := congrArg (fun F : M₂ →ₗ[ℂ] M₃ => F (g.toLinearMap y))
      (hY.L_neg_one (f.toLinearMap x) n k)
    simpa only [preModes_apply,LinearMap.add_apply,LinearMap.smul_apply,Lm1,hf] using h
  · intro u x y ell m n k
    simpa only [preModes_apply,hf,hg] using
      hY.jacobi u (f.toLinearMap x) (g.toLinearMap y) ell m n k

/-- Genuine logarithmic source precomposition as an actual operator. -/
noncomputable def precompose (f : B₁.Hom A₁) (g : B₂.Hom A₂)
    (Y : LogIntertwiningOperator A₁ A₂ A₃) : LogIntertwiningOperator B₁ B₂ A₃ :=
  ⟨preModes f.toLinearMap g.toLinearMap Y.1,Y.2.precompose f g⟩

@[simp] theorem precompose_apply (f : B₁.Hom A₁) (g : B₂.Hom A₂)
    (Y : LogIntertwiningOperator A₁ A₂ A₃) (n : ℂ) (k : ℕ) (x : X₁) (y : X₂) :
    (precompose f g Y).1 n k x y = Y.1 n k (f.toLinearMap x) (g.toLinearMap y) := rfl

/-- Source precomposition is linear in the genuine logarithmic operator. -/
noncomputable def precomposeLinear (f : B₁.Hom A₁) (g : B₂.Hom A₂) :
    LogIntertwiningOperator A₁ A₂ A₃ →ₗ[ℂ] LogIntertwiningOperator B₁ B₂ A₃ where
  toFun := precompose f g
  map_add' Y Z := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl
  map_smul' s Y := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl

end VOA.LogTensor
