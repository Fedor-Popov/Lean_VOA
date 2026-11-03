/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMFinal
import VOA.Examples.TripletWpTwoMixedClose

/-!
# Unconditional C2-cofiniteness of the lattice triplet at p = 2

This file is the final consumer of the two independently audited finite calculations:

* the three mixed screening coordinates, which close all seven mixed generator pairs;
* the weight-ten Adamovic--Milas identity.

Together with the general pair-closure theorem they prove C2-cofiniteness of the lattice
triplet `W(2)` and the explicit bound `dim A2(W(2)) <= 80`.
-/

namespace VOA.LatGen.WpC2

open VOA
open VOA.LatGen
open VOA.LatGen.Triplet
open VOA.LatGen.Wp
open VOA.LatGen.WpTwoAMFinal

/-- The lattice triplet at `p = 2` is unconditionally C2-cofinite, with the explicit
Poisson-quotient dimension bound furnished by the general closure theorem. -/
theorem tripletWVOA_two_c2Cofinite_and_finrank_le (hp : 1 ≤ 2) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_three_coordinates_AM hp
    (threeCoordinateIdentitiesWp_two hp)
    (amOmegaIdentity_two hp)

/-- The C2-cofiniteness component of the unconditional `p = 2` theorem. -/
theorem tripletWVOA_two_c2Cofinite (hp : 1 ≤ 2) : C2Cofinite (tripletWVOA 2 hp) :=
  (tripletWVOA_two_c2Cofinite_and_finrank_le hp).1

/-- The explicit dimension component of the unconditional `p = 2` theorem. -/
theorem tripletWVOA_two_A₂_finrank_le (hp : 1 ≤ 2) :
    Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  (tripletWVOA_two_c2Cofinite_and_finrank_le hp).2

end VOA.LatGen.WpC2

section AxiomAudit
#print axioms VOA.LatGen.WpC2.tripletWVOA_two_c2Cofinite_and_finrank_le
#print axioms VOA.LatGen.WpC2.tripletWVOA_two_c2Cofinite
#print axioms VOA.LatGen.WpC2.tripletWVOA_two_A₂_finrank_le
end AxiomAudit
