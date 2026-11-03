/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Kernel vectors detected by a simple polynomial determinant root

A simple determinant root forces a nonzero pairing of the matrix derivative
between an ordinary left kernel vector and an ordinary right kernel vector.
The vectors are extracted from the adjugate, without a rank or multiplicity
assumption beyond the stated simple root. This is finite linear algebra,
not an assertion that a particular representation-theoretic determinant has
such a root.
-/
namespace VOA.PolynomialMatrix
open Polynomial Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- Differentiating a polynomial determinant replaces one column at a time
by its derivative and sums over all columns. -/
theorem derivative_det_columns (M : Matrix ι ι R[X]) :
    M.det.derivative = ∑ j, (M.updateCol j (fun i => (M i j).derivative)).det := by
  simp only [Matrix.det_apply', map_sum, derivative_intCast_mul,
    derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  have he : (fun i => M.updateCol j (fun a => (M a j).derivative) (σ i) i) =
      Function.update (fun i => M (σ i) i) j ((M (σ j) j).derivative) := by
    funext i
    by_cases h : i = j
    · subst i; simp
    · simp [h]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ j)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

/-- Jacobi's determinant derivative formula, expressed as a finite sum of
adjugate entries times differentiated entries. It remains valid at singular
matrices and does not use an inverse. -/
theorem derivative_det_adjugate (M : Matrix ι ι R[X]) :
    M.det.derivative = ∑ j, ∑ i, M.adjugate j i * (M i j).derivative := by
  rw [derivative_det_columns]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- Entrywise evaluation of a polynomial matrix at an ordinary parameter. -/
noncomputable def evaluate (M : Matrix ι ι R[X]) (z : R) : Matrix ι ι R :=
  (Polynomial.evalRingHom z).mapMatrix M

/-- Entrywise first derivative at a fixed parameter. -/
noncomputable def tangent (M : Matrix ι ι R[X]) (z : R) : Matrix ι ι R :=
  fun i j => (M i j).derivative.eval z

/-- Matrix multiplication obeys the product rule entry by entry. -/
theorem tangent_mul (M N : Matrix ι ι R[X]) (z : R) :
    tangent (M * N) z = tangent M z * evaluate N z + evaluate M z * tangent N z := by
  ext i j
  simp [tangent, evaluate, Matrix.mul_apply, derivative_mul, Finset.sum_add_distrib, eval_finsetSum]

/-- A determinant with nonzero derivative has a nonzero evaluated adjugate.
The conclusion is valid whether or not the determinant itself vanishes. -/
theorem adjugate_ne_zero (M : Matrix ι ι R[X]) (z : R)
    (hd : M.det.derivative.eval z ≠ 0) : evaluate M.adjugate z ≠ 0 := by
  intro hz
  apply hd
  rw [derivative_det_adjugate]
  simp only [eval_finsetSum, eval_mul]
  have he (i j : ι) : (M.adjugate i j).eval z = 0 := congrFun (congrFun hz i) j
  simp only [he, zero_mul, Finset.sum_const_zero]

/-- At a determinant root both products with the evaluated adjugate vanish. -/
theorem evaluate_adjugate_products (M : Matrix ι ι R[X]) (z : R)
    (hz : M.det.eval z = 0) :
    evaluate M z * evaluate M.adjugate z = 0 ∧
    evaluate M.adjugate z * evaluate M z = 0 := by
  have evmul (A B : Matrix ι ι R[X]) :
      evaluate (A * B) z = evaluate A z * evaluate B z := by
    ext i j
    simp [evaluate, Matrix.mul_apply, eval_finsetSum]
  have evzero : evaluate (M.det • (1 : Matrix ι ι R[X])) z = 0 := by
    ext i j
    by_cases h : i = j
    · subst j; simp [evaluate, hz]
    · simp [evaluate, Matrix.one_apply_ne h]
  constructor
  · rw [← evmul, Matrix.mul_adjugate, evzero]
  · rw [← evmul, Matrix.adjugate_mul, evzero]

/-- Differentiating the matrix-adjugate identity at a root and multiplying
by the adjugate kills the derivative-of-adjugate term. -/
theorem adjugate_tangent_adjugate (M : Matrix ι ι R[X]) (z : R)
    (hz : M.det.eval z = 0) :
    evaluate M.adjugate z * tangent M z * evaluate M.adjugate z =
      M.det.derivative.eval z • evaluate M.adjugate z := by
  have hp := (evaluate_adjugate_products M z hz).2
  have he := congrArg (fun A => tangent A z) (Matrix.mul_adjugate M)
  dsimp only at he
  rw [tangent_mul] at he
  have hs : tangent (M.det • (1 : Matrix ι ι R[X])) z =
      M.det.derivative.eval z • (1 : Matrix ι ι R) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [tangent]
    · simp [tangent, Matrix.one_apply_ne h]
  rw [hs] at he
  have hh := congrArg (fun A => evaluate M.adjugate z * A) he
  simpa only [Matrix.mul_add, ← Matrix.mul_assoc, hp, Matrix.zero_mul,
    add_zero, Matrix.mul_smul, Matrix.mul_one] using hh

/-- A simple determinant root supplies ordinary left and right kernel
vectors whose pairing through the matrix derivative is nonzero. The
adjugate constructs both vectors, so no choice of nullspace basis or rank
hypothesis is required. -/
theorem kernel_pair_of_simple_root [NoZeroDivisors R]
    (M : Matrix ι ι R[X]) (z : R)
    (hz : M.det.eval z = 0) (hd : M.det.derivative.eval z ≠ 0) :
    ∃ r c : ι → R,
      (∀ j, ∑ i, r i * (M i j).eval z = 0) ∧
      (∀ i, ∑ j, (M i j).eval z * c j = 0) ∧
      (∑ i, ∑ j, (r i * c j) * (M i j).derivative.eval z) ≠ 0 := by
  have hn := adjugate_ne_zero M z hd
  obtain ⟨a,b,hab⟩ : ∃ a b, evaluate M.adjugate z a b ≠ 0 := by
    by_contra! h
    apply hn
    ext i j
    exact h i j
  obtain ⟨hleft,hright⟩ := evaluate_adjugate_products M z hz
  refine ⟨fun i => evaluate M.adjugate z a i,
    fun j => evaluate M.adjugate z j b, ?_, ?_, ?_⟩
  · intro j
    exact congrFun (congrFun hright a) j
  · intro i
    exact congrFun (congrFun hleft i) b
  · have he := congrFun (congrFun (adjugate_tangent_adjugate M z hz) a) b
    have hp : (evaluate M.adjugate z * tangent M z * evaluate M.adjugate z) a b ≠ 0 := by
      rw [he]
      exact mul_ne_zero hd hab
    convert hp using 1
    simp only [Matrix.mul_apply, Finset.sum_mul, tangent]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

end VOA.PolynomialMatrix
