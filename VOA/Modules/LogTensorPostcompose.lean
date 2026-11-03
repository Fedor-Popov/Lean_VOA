/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorIntertwining

/-! # Actual postcomposition of logarithmic intertwiners

A genuine weak-module homomorphism preserves all four logarithmic intertwiner
axioms, including the uniform cutoff and every Jacobi logarithmic coefficient.
-/
namespace VOA.LogTensor
open scoped BigOperators
universe u v₁ v₂ v₃ v₄
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]

/-- Postcompose every actual mode coefficient with a linear map. -/
noncomputable def postModes (f : M₃ →ₗ[ℂ] M₄) (Y : LogModes M₁ M₂ M₃) : LogModes M₁ M₂ M₄ :=
  fun n k => LinearMap.mk₂ ℂ (fun x y => f (Y n k x y))
    (fun x z y => by simp) (fun s x y => by simp)
    (fun x y z => by simp) (fun s x y => by simp)

@[simp] theorem postModes_apply (f : M₃ →ₗ[ℂ] M₄) (Y : LogModes M₁ M₂ M₃)
    (n : ℂ) (k : ℕ) (x : M₁) (y : M₂) : postModes f Y n k x y = f (Y n k x y) := rfl

variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
  {A₃ : WeakModule W M₃} {A₄ : WeakModule W M₄}

/-- Actual module postcomposition preserves genuine logarithmic intertwining. -/
theorem IsLogIntertwining.postcompose {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (f : A₃.Hom A₄) :
    IsLogIntertwining A₁ A₂ A₄ (postModes f.toLinearMap Y) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y n
    obtain ⟨K,hK⟩ := hY.logFinite x y n
    exact ⟨K,fun k hk => by rw [postModes_apply,hK k hk,map_zero]⟩
  · intro x y n
    obtain ⟨K,hK⟩ := hY.truncation x y n
    exact ⟨K,fun m hm k => by rw [postModes_apply,hK m hm k,map_zero]⟩
  · intro x n k
    apply LinearMap.ext
    intro y
    have h := congrArg (fun F : M₂ →ₗ[ℂ] M₃ => f.toLinearMap (F y)) (hY.L_neg_one x n k)
    simpa only [postModes_apply,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul] using h
  · intro u x y ell m n k
    have h := congrArg f.toLinearMap (hY.jacobi u x y ell m n k)
    change f.toLinearMap (∑ᶠ i,IsLogIntertwining.jacL A₂ A₃ Y u x y ell m n k i) =
      f.toLinearMap (∑ᶠ i,IsLogIntertwining.jacR A₁ Y u x y ell m n k i) at h
    rw [map_finsum f.toLinearMap (IsLogIntertwining.jacL_support_finite hY.truncation ..),
      map_finsum f.toLinearMap (IsLogIntertwining.jacR_support_finite Y u x y ell m n k)] at h
    have hf : ∀ (v : V) (p : ℤ) (z : M₃),
        f.toLinearMap (mode (A₃.YM v) p z) = mode (A₄.YM v) p (f.toLinearMap z) := f.map_act
    simpa only [IsLogIntertwining.jacL,IsLogIntertwining.jacR,postModes_apply,
      map_smul,map_sub,hf] using h

/-- A genuine logarithmic operator postcomposed with an actual module homomorphism. -/
noncomputable def postcompose (f : A₃.Hom A₄) (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    LogIntertwiningOperator A₁ A₂ A₄ :=
  ⟨postModes f.toLinearMap Y.1,Y.2.postcompose f⟩

@[simp] theorem postcompose_apply (f : A₃.Hom A₄) (Y : LogIntertwiningOperator A₁ A₂ A₃)
    (n : ℂ) (k : ℕ) (x : M₁) (y : M₂) :
    (postcompose f Y).1 n k x y = f.toLinearMap (Y.1 n k x y) := rfl

end VOA.LogTensor
