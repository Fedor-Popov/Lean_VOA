/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzEvaluation

/-!
# Recovering the logarithmic coefficients from a single insertion-point evaluation

The `L(0)` defect on a bilinear mode `F` is
`L₀F - F(L₀·,·) - F(·,L₀·) + (n+1)F`. On the `k`th logarithmic coefficient of an
actual logarithmic intertwiner it equals `(k+1)` times the next coefficient. Thus the
`k`th coefficient is precisely `1/k!` times the `k`th power of that defect applied to
the zeroth coefficient. No semisimplicity assumption or formal existence input is used.
-/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

/-- The `L(0)` defect at exponent `-n-1`, as an actual linear endomorphism of
bilinear mode maps. -/
noncomputable def modeDefect (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (n : ℂ) : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := LinearMap.mk₂ ℂ
    (fun x y => L0 A₃ (F x y) - F (L0 A₁ x) y - F x (L0 A₂ y) + (n+1) • F x y)
    (fun x x' y => by dsimp only; simp only [map_add, LinearMap.add_apply, smul_add]; module)
    (fun s x y => by dsimp only; simp only [map_smul, LinearMap.smul_apply]; module)
    (fun x y y' => by dsimp only; simp only [map_add, smul_add]; module)
    (fun s x y => by dsimp only; simp only [map_smul]; module)
  map_add' F G := by ext x y; dsimp only; simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add, smul_add]; module
  map_smul' s F := by
    ext x y
    dsimp only
    simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]
    module

@[simp] theorem modeDefect_apply (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (n : ℂ) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    modeDefect A₁ A₂ A₃ n F x y =
      L0 A₃ (F x y) - F (L0 A₁ x) y - F x (L0 A₂ y) + (n+1) • F x y := rfl

/-- The defect recursion is forced by the genuine logarithmic intertwiner Jacobi
identity and derivative axiom. -/
theorem modeDefect_logCoeff {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n : ℂ) (k : ℕ) :
    modeDefect A₁ A₂ A₃ n (Y n k) = ((k:ℂ)+1) • Y n (k+1) := by
  ext x y
  rw [modeDefect_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  rw [hY.L0_bracket]
  module

/-- All higher logarithmic coefficients are obtained by finite powers of the same
`L(0)` defect. -/
theorem modeDefect_pow_logZero {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n : ℂ) (k : ℕ) :
    (modeDefect A₁ A₂ A₃ n ^ k) (Y n 0) = (k.factorial:ℂ) • Y n k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, modeDefect_logCoeff hY,
      smul_smul, Nat.factorial_succ]
    push_cast
    congr 1
    ring

/-- Explicit reconstruction, valid on weak modules without any grading hypothesis. -/
theorem logCoeff_eq_defect_pow {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (n : ℂ) (k : ℕ) :
    Y n k = (k.factorial:ℂ)⁻¹ • (modeDefect A₁ A₂ A₃ n ^ k) (Y n 0) := by
  rw [modeDefect_pow_logZero hY, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

end VOA.LogTensor.Pz
