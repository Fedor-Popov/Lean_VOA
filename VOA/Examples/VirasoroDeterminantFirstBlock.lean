/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# First determinant coefficient along a radical block

If a polynomial Gram matrix has a radical second block at parameter zero,
one parameter factor can be removed from each row of that block. The first
possible determinant coefficient is the product of the nonradical constant
block determinant and the radical first-order block determinant. This is an
exact finite identity; it does not assert that either factor is nonzero.
-/
namespace VOA.PolynomialBlock
open Polynomial Matrix
variable {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]

/-- Divide the second group of rows by the formal parameter, leaving the
first group unchanged. Polynomial divX is used without division in a field. -/
noncomputable def divideSecondRows (M : Matrix (I ⊕ J) (I ⊕ J) R[X]) :
    Matrix (I ⊕ J) (I ⊕ J) R[X] := fun i j =>
  match i with
  | Sum.inl _ => M i j
  | Sum.inr _ => (M i j).divX

/-- If the second group of rows vanishes at zero, its row factors give
an exact parameter power dividing the determinant, before taking coefficients. -/
theorem det_factor_secondRows [DecidableEq I] [DecidableEq J]
    (M : Matrix (I ⊕ J) (I ⊕ J) R[X])
    (hz : ∀ i j, (M (Sum.inr i) j).coeff 0 = 0) :
    M.det = X ^ Fintype.card J * (divideSecondRows M).det := by
  have he : M = Matrix.of (fun i j =>
      (Sum.elim (fun _ : I => (1 : R[X])) (fun _ : J => X) i) *
        divideSecondRows M i j) := by
    funext i j
    cases i with
    | inl i => simp [divideSecondRows]
    | inr i =>
      have hh := X_mul_divX_add (M (Sum.inr i) j)
      simpa [divideSecondRows, hz] using hh.symm
  conv_lhs => rw [he]
  rw [Matrix.det_mul_column]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const_one, Finset.prod_const, Finset.card_univ, one_mul]

/-- The coefficient at the number of radical rows is the determinant of
the undivided constant block times the determinant of the first-order radical
block. Cross-block first derivatives do not affect this coefficient. -/
theorem det_first_radical_coefficient [DecidableEq I] [DecidableEq J]
    (M : Matrix (I ⊕ J) (I ⊕ J) R[X])
    (hrow : ∀ i j, (M (Sum.inr i) j).coeff 0 = 0)
    (hcol : ∀ i j, (M (Sum.inl i) (Sum.inr j)).coeff 0 = 0) :
    M.det.coeff (Fintype.card J) =
      Matrix.det (fun i j : I => (M (Sum.inl i) (Sum.inl j)).coeff 0) *
      Matrix.det (fun i j : J => (M (Sum.inr i) (Sum.inr j)).coeff 1) := by
  rw [det_factor_secondRows M hrow]
  have hc := coeff_X_pow_mul (divideSecondRows M).det (Fintype.card J) 0
  simp only [zero_add] at hc
  rw [hc]
  have he : ((divideSecondRows M).map (evalRingHom (0 : R))) =
      Matrix.fromBlocks
        (fun i j : I => (M (Sum.inl i) (Sum.inl j)).coeff 0)
        (0 : Matrix I J R)
        (fun i j => (M (Sum.inr i) (Sum.inl j)).coeff 1)
        (fun i j : J => (M (Sum.inr i) (Sum.inr j)).coeff 1) := by
    funext i j
    cases i <;> cases j <;>
      simp [divideSecondRows, ← coeff_zero_eq_eval_zero, coeff_divX, hcol]
  have hh := (evalRingHom (0 : R)).map_det (divideSecondRows M)
  change (divideSecondRows M).det.eval 0 = ((divideSecondRows M).map (evalRingHom (0 : R))).det at hh
  rw [← coeff_zero_eq_eval_zero, he, Matrix.det_fromBlocks_zero₁₂] at hh
  exact hh

end VOA.PolynomialBlock
