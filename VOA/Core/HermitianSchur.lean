/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Strict positivity and Hermitian Schur complements

Mathlib characterizes positive semidefiniteness of a Hermitian block matrix by its Schur
complement.  This file records the corresponding positive-definite equivalence.  Strictness is
recovered by combining semidefiniteness with the existing block-invertibility criterion.
-/

namespace VOA

open Matrix
open scoped ComplexOrder

/-- If the top-left Hermitian block is positive definite, then the full Hermitian block matrix is
positive definite exactly when its Schur complement is positive definite. -/
theorem fromBlocks_posDef_iff_schur₁₁ {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [Finite n] [DecidableEq m] {A : Matrix m m 𝕜}
    (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (hA : A.PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef ↔
      (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  letI := Fintype.ofFinite n
  letI := hA.isUnit.invertible
  constructor
  · intro h
    have hs := (hA.fromBlocks₁₁ B D).mp h.posSemidef
    have hu : IsUnit (D - Bᴴ * A⁻¹ * B) := by
      simpa only [Matrix.invOf_eq_nonsing_inv] using
        (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
          (A := A) (B := B) (C := Bᴴ) (D := D)).mp h.isUnit
    exact Matrix.PosSemidef.posDef_iff_isUnit hs |>.mpr hu
  · intro h
    have hs := (hA.fromBlocks₁₁ B D).mpr h.posSemidef
    have hu : IsUnit (Matrix.fromBlocks A B Bᴴ D) :=
      (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
        (A := A) (B := B) (C := Bᴴ) (D := D)).mpr
          (by simpa only [Matrix.invOf_eq_nonsing_inv] using h.isUnit)
    exact Matrix.PosSemidef.posDef_iff_isUnit hs |>.mpr hu

end VOA
