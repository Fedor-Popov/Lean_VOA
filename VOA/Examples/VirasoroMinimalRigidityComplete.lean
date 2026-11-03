/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningKacRoots

/-!
# Unrestricted graded rigidity of Virasoro minimal models

Finite integer screenings provide genuine Gram roots for every positive
Kac label at infinitely many parameters. Laurent interpolation and level
induction supply the general nonzero singular states. The already proved
Kac degree exhaustion, actual Verma-to-vacuum determinant identity, simple
root transfer and deformation reconstruction complete the uniform argument.
No Kac determinant theorem, singular existence, character formula, or
rigidity premise is assumed in the final theorem.
-/
namespace VOA.VirModule
open VirSimple Deform InverseDS.VirasoroVerma VirasoroScreening

/-- EVERY simple Virasoro minimal model with coprime labels at least two
is graded first-order rigid. Every grading-preserving deformation is a
coboundary. This is the unrestricted theorem, including labels both greater
than three, with no remaining representation-theoretic or rigidity inputs. -/
theorem minimal_graded_rigidity (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hcop : p.Coprime q) :
    IsRigidGraded (virasoroSimple (minimalCentralCharge p q)) := by
  apply minimal_rigidity_of_infinite_kac_roots p q hp hq hcop
  intro r s hr hs _
  exact infinite_integer_screening_roots r s hr hs

end VOA.VirModule
