/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroRigidityStructural
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Taylor

/-!
# First-order determinant obstructions for Virasoro minimal models

A finite zero set does not imply infinitesimal rigidity: a double root admits a
nonzero tangent over the dual numbers. This file gives the correct scalar test.
A simple root prevents any nonzero first-order motion that preserves the polynomial
relation. It applies to Lee–Yang at level four, and Ising and M(2,7) at level six.

These determinant tests alone do not connect to arbitrary VOA deformations.
The later VirasoroDeformationGram4 and VirasoroWeight6Rigidity files prove
the actual central obstructions in these three cases; VirasoroFixedReconstruction
supplies coordinate changes. This file remains the scalar polynomial layer.
The uniform minimal-model central obstruction is still open.
-/

namespace VOA.VirRigidTangent

open Polynomial TrivSqZeroExt
open VirModule VirSimple VirGram56 LeeYang

/-- Evaluate a polynomial on a scalar plus an infinitesimal displacement.
The infinitesimal coefficient is precisely its derivative times the displacement. -/
theorem aeval_dual (p : Polynomial ℂ) (c δ : ℂ) :
    p.aeval (inl c + inr δ : DualNumber ℂ) =
      inl (p.eval c) + inr (p.derivative.eval c * δ) := by
  rw [aeval_add_of_sq_eq_zero p _ _ (by simp [pow_two])]
  have he (q : Polynomial ℂ) : q.aeval (inl c : DualNumber ℂ) = inl (q.eval c) :=
    aeval_algebraMap_apply_eq_algebraMap_eval c q
  rw [he, he]
  ext <;> simp [mul_comm]

/-- At a simple root, preserving the polynomial equation to first order forces
zero scalar motion. This is an algebraic statement over the dual numbers. -/
theorem tangent_eq_zero_of_simple_root (p : Polynomial ℂ) (c δ : ℂ)
    (hderiv : p.derivative.eval c ≠ 0)
    (hlift : p.aeval (inl c + inr δ : DualNumber ℂ) = 0) : δ = 0 := by
  rw [aeval_dual] at hlift
  have hs := congrArg TrivSqZeroExt.snd hlift
  simp only [snd_add, snd_inl, snd_inr, snd_zero, zero_add] at hs
  exact (mul_eq_zero.mp hs).resolve_left hderiv

/-- The canonical level-four determinant, as a polynomial in central charge. -/
noncomputable def determinant4 : Polynomial ℂ :=
  Polynomial.C (1 / 2) * X ^ 2 * (Polynomial.C 5 * X + Polynomial.C 22)

/-- The canonical level-six determinant, as a polynomial in central charge. -/
noncomputable def determinant6 : Polynomial ℂ :=
  Polynomial.C (3 / 4) * X ^ 4 * (Polynomial.C 2 * X - Polynomial.C 1) *
    (Polynomial.C 5 * X + Polynomial.C 22) ^ 2 * (Polynomial.C 7 * X + Polynomial.C 68)

/-- This polynomial is the actual canonical Gram determinant, not an auxiliary form. -/
theorem determinant4_eval (c : ℂ) : determinant4.eval c = (VirGram4.canGram4 c).det := by
  rw [VirGram4.det_canGram4]
  simp [determinant4]
  ring

/-- The level-six polynomial agrees with the canonical Gram determinant. -/
theorem determinant6_eval (c : ℂ) : determinant6.eval c = (canGram6 c).det := by
  rw [det_canGram6]
  simp [determinant6]

/-- The first Lee–Yang singular level has a simple determinant root. -/
theorem derivative4_leeYang_ne_zero : determinant4.derivative.eval leeYangC ≠ 0 := by
  norm_num [determinant4, derivative_mul, derivative_add, derivative_pow, leeYangC]

/-- The first Ising singular level has a simple determinant root. -/
theorem derivative6_ising_ne_zero : determinant6.derivative.eval isingC ≠ 0 := by
  norm_num [determinant6, derivative_mul, derivative_add, derivative_sub, derivative_pow, isingC]

/-- The first M(2,7) singular level has a simple determinant root. -/
theorem derivative6_m27_ne_zero : determinant6.derivative.eval m27C ≠ 0 := by
  norm_num [determinant6, derivative_mul, derivative_add, derivative_sub, derivative_pow, m27C]

/-- No infinitesimal central-charge motion preserves the level-four Lee–Yang determinant. -/
theorem leeYang_tangent_eq_zero (δ : ℂ)
    (h : determinant4.aeval (inl leeYangC + inr δ : DualNumber ℂ) = 0) : δ = 0 :=
  tangent_eq_zero_of_simple_root _ _ _ derivative4_leeYang_ne_zero h

/-- No infinitesimal central-charge motion preserves the level-six Ising determinant. -/
theorem ising_tangent_eq_zero (δ : ℂ)
    (h : determinant6.aeval (inl isingC + inr δ : DualNumber ℂ) = 0) : δ = 0 :=
  tangent_eq_zero_of_simple_root _ _ _ derivative6_ising_ne_zero h

/-- No infinitesimal central-charge motion preserves the level-six M(2,7) determinant. -/
theorem m27_tangent_eq_zero (δ : ℂ)
    (h : determinant6.aeval (inl m27C + inr δ : DualNumber ℂ) = 0) : δ = 0 :=
  tangent_eq_zero_of_simple_root _ _ _ derivative6_m27_ne_zero h

/-- A polynomial with just one scalar root can still have a nonzero infinitesimal root.
Thus a finite or isolated degeneracy locus alone cannot prove first-order rigidity. -/
theorem isolated_root_has_nonzero_tangent :
    (∀ c : ℂ, c ^ 2 = 0 ↔ c = 0) ∧
      (DualNumber.eps : DualNumber ℂ) ≠ 0 ∧
      (X ^ 2 : Polynomial ℂ).aeval (DualNumber.eps : DualNumber ℂ) = 0 := by
  refine ⟨fun c => sq_eq_zero_iff, ?_, ?_⟩
  · intro h
    have := congrArg TrivSqZeroExt.snd h
    simp at this
  · simp

/-- When a dimension deficit is known, the old realization assumption is exactly
rigidity itself. This certificate prevents using it as an independent proof input. -/
theorem realisedByNondegenerate_iff_isRigidGraded
    {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (n : ℤ) (d : ℕ) (hlt : Module.finrank ℂ (W.grading n) < d) :
    VirRigidStruct.RealisedByNondegenerate W n d ↔ Deform.IsRigidGraded W := by
  constructor
  · exact fun h => VirRigidStruct.isRigidGraded_of_finrank_lt W n d h hlt
  · intro h ⟨D, hD, hn⟩
    exact (hn (h D hD)).elim

end VOA.VirRigidTangent
