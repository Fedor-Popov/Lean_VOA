/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positivity criteria for real symmetric two-by-two matrices

This file supplies the elementary Sylvester criteria needed to certify the small Schur blocks
arising in graded-unitarity computations.  Mathlib's general positive-definite matrix API provides
the converse implications through diagonal and determinant positivity; the forward implications
below are proved by completing the square.
-/

namespace VOA

open Matrix

/-- A real symmetric two-by-two matrix is positive definite when its first diagonal entry and
determinant are positive.  This is the forward half of the two-by-two Sylvester criterion. -/
private lemma realSymmetricTwo_posDef_of {a b d : ℝ} (ha : 0 < a)
    (hdet : 0 < a * d - b ^ 2) :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      contrapose! hx
      funext i
      fin_cases i <;> simp_all
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two]
    simp only [of_apply, cons_val_zero, cons_val_one]
    rw [show x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + d * x 1) =
          a * x 0 ^ 2 + 2 * b * x 0 * x 1 + d * x 1 ^ 2 by ring]
    rcases eq_or_ne (x 1) 0 with hx1 | hx1
    · have hx0 : x 0 ≠ 0 := by
        rcases hx' with hx0 | hx1'
        · exact hx0
        · exact (hx1' hx1).elim
      simpa [hx1] using mul_pos ha (sq_pos_of_ne_zero hx0)
    · have hpositive :
          0 < (a * x 0 + b * x 1) ^ 2 + (a * d - b ^ 2) * x 1 ^ 2 :=
        add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hx1))
      have hidentity :
          a * (a * x 0 ^ 2 + 2 * b * x 0 * x 1 + d * x 1 ^ 2) =
            (a * x 0 + b * x 1) ^ 2 + (a * d - b ^ 2) * x 1 ^ 2 := by
        ring
      rw [← hidentity] at hpositive
      nlinarith

/-- A real symmetric two-by-two matrix is positive semidefinite when both diagonal entries and
its determinant are nonnegative.  This is the forward half of the semidefinite criterion. -/
private lemma realSymmetricTwo_posSemidef_of {a b d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hdet : 0 ≤ a * d - b ^ 2) :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two]
    simp only [of_apply, cons_val_zero, cons_val_one]
    rw [show x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + d * x 1) =
          a * x 0 ^ 2 + 2 * b * x 0 * x 1 + d * x 1 ^ 2 by ring]
    rcases ha.eq_or_lt with ha0 | ha
    · have hb : b = 0 := by
        nlinarith [sq_nonneg b]
      rw [← ha0, hb]
      simpa using mul_nonneg hd (sq_nonneg (x 1))
    · have hnonnegative :
          0 ≤ (a * x 0 + b * x 1) ^ 2 + (a * d - b ^ 2) * x 1 ^ 2 :=
        add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg _))
      have hidentity :
          a * (a * x 0 ^ 2 + 2 * b * x 0 * x 1 + d * x 1 ^ 2) =
            (a * x 0 + b * x 1) ^ 2 + (a * d - b ^ 2) * x 1 ^ 2 := by
        ring
      rw [← hidentity] at hnonnegative
      nlinarith

/-- Sylvester's criterion for a real symmetric two-by-two matrix: positive definiteness is
equivalent to positivity of the first leading principal minor and the determinant. -/
theorem realSymmetricTwo_posDef_iff {a b d : ℝ} :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosDef ↔
      0 < a ∧ 0 < a * d - b ^ 2 := by
  constructor
  · intro h
    constructor
    · simpa using h.diag_pos (i := 0)
    · simpa [Matrix.det_fin_two, pow_two] using h.det_pos
  · rintro ⟨ha, hdet⟩
    exact realSymmetricTwo_posDef_of ha hdet

/-- A real symmetric two-by-two matrix is positive semidefinite exactly when its two diagonal
entries and determinant are nonnegative. -/
theorem realSymmetricTwo_posSemidef_iff {a b d : ℝ} :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ↔
      0 ≤ a ∧ 0 ≤ d ∧ 0 ≤ a * d - b ^ 2 := by
  constructor
  · intro h
    exact ⟨by simpa using h.diag_nonneg (i := 0), by simpa using h.diag_nonneg (i := 1),
      by simpa [Matrix.det_fin_two, pow_two] using h.det_nonneg⟩
  · rintro ⟨ha, hd, hdet⟩
    exact realSymmetricTwo_posSemidef_of ha hd hdet

end VOA
