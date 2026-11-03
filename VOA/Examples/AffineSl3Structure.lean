/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3Lie

/-!
# Dual generators and adjoint normalization for affine sl3

The trace-dual family explicitly inverts the Cartan block; it is not just
root exchange on all eight generators. It detects every coordinate and
proves nondegeneracy. The two Cartan actions give the actual A2 weights.
The adjoint Casimir calculation supplies the scalar six, hence the
normalization 2 h-dual = 6 required by the proposed Sugawara construction.
None of these finite-dimensional facts assumes a vacuum PBW theorem.
-/
namespace VOA.AffineSl3
noncomputable section
set_option maxHeartbeats 4000000

/-- The trace-dual generators exchange opposite roots and invert the A2
Cartan matrix by one third of [[2,1],[1,2]]. -/
def dualGenerator : Fin 8 → Sl3 :=
  ![f1, f2, f12, e1, e2, e12, (1/3 : ℂ) • ((2 : ℂ) • h1 + h2),
    (1/3 : ℂ) • (h1 + (2 : ℂ) • h2)]

/-- The trace-zero relation expressed using the three actual diagonal entries. -/
theorem diagonal_sum_zero (x : Sl3) : x.val 0 0 + x.val 1 1 + x.val 2 2 = 0 := by
  have hx := x.property
  change Matrix.trace x.val = 0 at hx
  simpa [Matrix.trace, Fin.sum_univ_three, add_assoc] using hx

/-- Pairing with a dual generator extracts exactly its Chevalley coordinate. -/
theorem form_dual_coordinates (x : Sl3) (i : Fin 8) :
    form x (dualGenerator i) = coordinates x i := by
  have ht := diagonal_sum_zero x
  fin_cases i <;>
    simp [dualGenerator, coordinates, form_apply, e1, e2, e12, f1, f2, f12, h1, h2,
      LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.ext_iff,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;>
    first | linear_combination (-1/3 : ℂ) * ht | linear_combination (1/3 : ℂ) * ht

/-- Original and dual generators have Kronecker-delta pairings. -/
theorem generator_dual (i j : Fin 8) :
    form (generator i) (dualGenerator j) = if i=j then 1 else 0 := by
  rw [form_dual_coordinates, coordinates_generator]
  simp [Pi.single_apply, eq_comm]

/-- The normalized invariant trace form separates points in its left argument. -/
theorem form_left_nondegenerate (x : Sl3) (hx : ∀ y, form x y = 0) : x = 0 := by
  have hc : coordinates x = 0 := by
    ext i
    simpa [form_dual_coordinates] using hx (dualGenerator i)
  have h := reconstruct x
  rw [hc] at h
  simpa using h.symm

/-- By symmetry the form also separates points in its right argument. -/
theorem form_right_nondegenerate (x : Sl3) (hx : ∀ y, form y x = 0) : x = 0 :=
  form_left_nondegenerate x (fun y => by rw [form_invariant.symm]; exact hx y)

/-- The first coroot eigenvalues on the ordered Chevalley generators. -/
def weight1 : Fin 8 → ℤ := ![2,-1,1,-2,1,-1,0,0]

/-- The second coroot eigenvalues on the same generators. -/
def weight2 : Fin 8 → ℤ := ![-1,2,1,1,-2,-1,0,0]

/-- Bracketing with the first Cartan generator realizes the first A2 weight. -/
theorem h1_generator (a : Fin 8) : ⁅h1, generator a⁆ = (weight1 a : ℂ) • generator a := by
  apply Subtype.ext
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [generator, weight1, Ring.lie_def, e1, e2, e12, f1, f2, f12, h1, h2,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.ext_iff,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- Bracketing with the second Cartan generator realizes the second A2 weight. -/
theorem h2_generator (a : Fin 8) : ⁅h2, generator a⁆ = (weight2 a : ℂ) • generator a := by
  apply Subtype.ext
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [generator, weight2, Ring.lie_def, e1, e2, e12, f1, f2, f12, h1, h2,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.single, Fin.ext_iff,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-- Every structure constant is extracted from the actual matrix bracket;
this defines the complete table, including brackets involving composite roots. -/
def structureConstant (a b c : Fin 8) : ℂ :=
  coordinates ⁅generator a, generator b⁆ c

/-- The structure constants reconstruct every generator bracket exactly. -/
theorem generator_bracket (a b : Fin 8) :
    ⁅generator a, generator b⁆ = ∑ c, structureConstant a b c • generator c :=
  (reconstruct ⁅generator a, generator b⁆).symm

/-- The full structure-constant table is antisymmetric in the input indices. -/
theorem structureConstant_antisymm (a b c : Fin 8) :
    structureConstant a b c = -structureConstant b a c := by
  change coordinatesLinear ⁅generator a, generator b⁆ c =
    -coordinatesLinear ⁅generator b, generator a⁆ c
  rw [← lie_skew (generator a) (generator b), map_neg]
  rfl

/-- The trace-dual adjoint Casimir is six times the identity on every
trace-zero matrix. This proves the scalar normalization used for sl3,
without asserting any Sugawara field identity or VOA structure. -/
theorem adjoint_casimir (x : Sl3) :
    ∑ i, ⁅generator i, ⁅dualGenerator i, x⁆⁆ = (6 : ℂ) • x := by
  have ht := diagonal_sum_zero x
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, generator, dualGenerator, Ring.lie_def,
      e1, e2, e12, f1, f2, f12, h1, h2, Matrix.mul_apply, Matrix.single] <;>
    ring_nf <;> linear_combination (-2 : ℂ) * ht

end
end VOA.AffineSl3
