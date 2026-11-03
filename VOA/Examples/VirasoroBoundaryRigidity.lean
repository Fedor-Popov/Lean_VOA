/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSATaylor
import VOA.Examples.VirasoroBSAWordPolynomial
import VOA.Examples.VirasoroZeroChargeRigidity

/-!
# Graded rigidity of every M(2,q) minimal model

The reflected-pairing identity identifies the actual norm derivative with
its diagonal response. The latter is a proved nonzero multiple of the
recurrence residual at every even singular level. The established universal
word obstruction and reconstruction therefore give unconditional graded
rigidity for every coprime minimal-model pair with one label equal to two.
This does not prove the unrestricted minimal-model theorem.
-/
namespace VOA.VirModule

/-- The ACTUAL scalar norm response is nonzero at every positive even
singular level at least four. The reflection sign is one at these levels. -/
theorem bsaScalarNormResponse_even_ne_zero (k : ℕ) :
    bsaScalarNormResponse (bsaCharge (2*(k+2))) (2*(k+2)) (2*k+2) ≠ 0 := by
  rw [bsaScalarNormResponse_eq_diagonal _ _ (by omega)]
  have hp : (-1:ℂ)^(2*k+2)=1 := by rw [pow_add, pow_mul]; norm_num
  rw [hp, one_mul]
  exact bsaDiagonalResponse_even_ne_zero k

/-- The universal norm polynomial has a nonzero derivative at each of the
BSA minimal-model charges. This is the actual word polynomial used by the
deformation obstruction, not a hypothetical determinant or product formula. -/
theorem bsaNormPolynomial_even_derivative_ne_zero (k : ℕ) :
    (bsaNormPolynomial (2*(k+2))).derivative.eval (bsaCharge (2*(k+2))) ≠ 0 := by
  rw [bsaNormPolynomial_derivative _ (2*k+2) (by omega) (by omega)]
  exact bsaScalarNormResponse_even_ne_zero k

/-- Every graded first-order deformation of the simple Virasoro VOA at the
even BSA charge is trivial. There are no residual rigidity hypotheses. -/
theorem bsa_even_graded_rigidity (k : ℕ) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (bsaCharge (2*(k+2)))) :=
  graded_rigidity_of_bsa_scalar _ (2*k+2) (by omega) (by omega)
    (bsaScalarNormResponse_even_ne_zero k)

/-- Every M(2,q) with odd q at least three is graded rigid. The q=3 case
uses the already proved zero-charge theorem; all larger odd labels use the
uniform BSA norm obstruction, not separate finite-level calculations. -/
theorem minimal_two_odd_graded_rigidity (q : ℕ) (hq : 3≤q) (hodd : Odd q) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (minimalCentralCharge 2 q)) := by
  by_cases he : q=3
  · subst q
    have hc : (minimalCentralCharge 2 3 : ℂ) = 0 := by norm_num [minimalCentralCharge]
    exact hc ▸ VirDeformModes.zeroCharge_graded_rigidity
  · obtain ⟨j,hj⟩ := hodd.exists_bit1
    have hq' : q=2*((j-2)+2)+1 := by omega
    have hh := bsa_even_graded_rigidity (j-2)
    rw [bsaCharge_eq_minimal, ← hq'] at hh
    exact hh

/-- The family theorem with the usual minimal-model assumptions: labels
2 and q are at least two and coprime. Coprimality supplies the oddness. -/
theorem minimal_two_graded_rigidity (q : ℕ) (hq : 2≤q) (hcop : Nat.Coprime 2 q) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (minimalCentralCharge 2 q)) := by
  have hodd : Odd q := Nat.coprime_two_left.mp hcop
  obtain ⟨j,hj⟩ := hodd.exists_bit1
  exact minimal_two_odd_graded_rigidity q (by omega) hodd

/-- Exchanging the two labels leaves the minimal central charge unchanged.
This is an arithmetic equality and needs no representation-theory input. -/
theorem minimalCharge_swap (p q : ℕ) :
    minimalCentralCharge p q=minimalCentralCharge q p := by
  unfold minimalCentralCharge
  rw [show (p:ℚ)-(q:ℚ) = -((q:ℚ)-(p:ℚ)) by ring, neg_sq]
  congr 2 <;> ring

/-- The same unconditional family theorem covers labels (p,2), by symmetry
of the central charge. Models with both labels greater than two remain a
separate uniform problem. -/
theorem minimal_right_two_graded_rigidity (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 2) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (minimalCentralCharge p 2)) := by
  rw [minimalCharge_swap]
  exact minimal_two_graded_rigidity p hp hcop.symm

end VOA.VirModule
