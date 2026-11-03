import Mathlib.Algebra.Lie.AdjointAction.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-! Algebraic conjugation by exponentials of nilpotent endomorphisms. -/

namespace VOA.DeligneAudit.D4LevelReduction

open IsNilpotent

noncomputable local instance rationalModuleForExponential
    (X : Type*) [AddCommGroup X] [Module ℂ X] :
    Module ℚ X := Module.restrictScalars ℚ ℂ X

local instance rationalTowerForExponential (X : Type*) [AddCommGroup X] [Module ℂ X] :
    IsScalarTower ℚ ℂ X := IsScalarTower.restrictScalars ℚ ℂ X

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Exponentiating left multiplication agrees with left multiplication by the exponential. -/
theorem nilpotent_exp_mulLeft (x y : A) (hx : IsNilpotent x) :
    exp (LinearMap.mulLeft ℂ x) y = exp x * y := by
  obtain ⟨n, hn⟩ := hx
  have hl : (LinearMap.mulLeft ℂ x) ^ n = 0 := by
    rw [LinearMap.pow_mulLeft, hn]
    ext z
    simp
  simp [exp_eq_sum hl, exp_eq_sum hn, LinearMap.pow_mulLeft, Finset.sum_mul,
    smul_mul_assoc]

/-- Exponentiating right multiplication agrees with right multiplication by the exponential. -/
theorem nilpotent_exp_mulRight (x y : A) (hx : IsNilpotent x) :
    exp (LinearMap.mulRight ℂ x) y = y * exp x := by
  obtain ⟨n, hn⟩ := hx
  have hr : (LinearMap.mulRight ℂ x) ^ n = 0 := by
    rw [LinearMap.pow_mulRight, hn]
    ext z
    simp
  simp [exp_eq_sum hr, exp_eq_sum hn, LinearMap.pow_mulRight, Finset.mul_sum,
    mul_smul_comm]

/-- The nilpotent adjoint exponential is actual conjugation on the associative algebra. -/
theorem nilpotent_exp_ad_apply (x y : A) (hx : IsNilpotent x) :
    exp (LieAlgebra.ad ℂ A x) y = exp x * y * exp (-x) := by
  have hl : IsNilpotent (LinearMap.mulLeft ℂ x) := by
    rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight ℂ (-x)) := by
    rw [LinearMap.isNilpotent_mulRight_iff]
    exact hx.neg
  have he : LieAlgebra.ad ℂ A x = LinearMap.mulLeft ℂ x +
      LinearMap.mulRight ℂ (-x) := by
    ext z
    simp [LieAlgebra.ad_apply, Ring.lie_def, sub_eq_add_neg]
  rw [he, exp_add_of_commute (LinearMap.commute_mulLeft_right x (-x)) hl hr,
    Module.End.mul_apply, nilpotent_exp_mulRight _ _ hx.neg,
    nilpotent_exp_mulLeft _ _ hx, mul_assoc]

/-- An adjoint string of length two has a linear exponential formula. -/
theorem nilpotent_exp_ad_apply_of_square_zero (x y : A) (hx : IsNilpotent x)
    (hy : ⁅x, ⁅x, y⁆⁆ = 0) :
    exp (LieAlgebra.ad ℂ A x) y = y + ⁅x, y⁆ := by
  have hn := LieAlgebra.ad_nilpotent_of_nilpotent (R := ℂ) hx
  have hh : ((LieAlgebra.ad ℂ A x) ^ 2) • y = 0 := by
    simpa only [pow_two, Module.End.smul_def, Module.End.mul_apply,
      LieAlgebra.ad_apply] using hy
  have he := exp_smul_eq_sum hh hn
  simpa [Finset.sum_range_succ, Module.End.smul_def, LieAlgebra.ad_apply] using he

/-- An adjoint string of length three has a quadratic exponential formula. -/
theorem nilpotent_exp_ad_apply_of_cube_zero (x y : A) (hx : IsNilpotent x)
    (hy : ⁅x, ⁅x, ⁅x, y⁆⁆⁆ = 0) :
    exp (LieAlgebra.ad ℂ A x) y = y + ⁅x, y⁆ + (1 / 2 : ℚ) • ⁅x, ⁅x, y⁆⁆ := by
  have hn := LieAlgebra.ad_nilpotent_of_nilpotent (R := ℂ) hx
  have hh : ((LieAlgebra.ad ℂ A x) ^ 3) • y = 0 := by
    simpa only [_root_.pow_succ, pow_zero, Module.End.smul_def, Module.End.mul_apply,
      Module.End.one_apply, LieAlgebra.ad_apply] using hy
  have he := exp_smul_eq_sum hh hn
  simpa [Finset.sum_range_succ, _root_.pow_succ, Module.End.smul_def, Module.End.mul_apply,
    LieAlgebra.ad_apply] using he

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.nilpotent_exp_ad_apply
#print axioms VOA.DeligneAudit.D4LevelReduction.nilpotent_exp_ad_apply_of_square_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.nilpotent_exp_ad_apply_of_cube_zero
