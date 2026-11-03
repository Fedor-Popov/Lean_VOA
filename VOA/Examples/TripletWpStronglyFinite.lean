/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoIrrational
import VOA.Modules.StronglyRational

/-!
# The conditional strongly-finite package for lattice `W(2)`

The lattice triplet `tripletWVOA 2 hp` is already unconditionally `C2`-cofinite, has no
weight-one states, and is neither admissibly rational nor Gannon-rational.  This file packages
those results with the one remaining independent input needed by the repository's definition of
`StronglyFinite`: simplicity of this same lattice carrier.

No screening-kernel identification, symplectic-fermion comparison, Felder exactness, or module
classification is used.  Every strongly-finite endpoint below keeps `hsimple` explicit.
Simplicity is proved downstream (`Wp.tripletWVOA_two_isSimple`, `Examples.TripletWpTwoZhuFinal`),
which also states the unconditional endpoints (`tripletWVOA_two_stronglyFinite`, …).
-/

namespace VOA.LatGen.Wp

open VOA
open VOA.LatGen
open VOA.LatGen.Triplet
open VOA.LatGen.WpC2

/-- The intrinsic weight-one space of the lattice triplet carrier is zero. -/
theorem eq_zero_of_mem_tripletWVOA_two_grading_one (hp : 1 ≤ 2)
    {v : (tripletW 2 hp).carrier} (hv : v ∈ (tripletWVOA 2 hp).grading 1) : v = 0 := by
  apply Subtype.ext
  exact eq_zero_of_mem_tripletW_two_and_grading_one hp v.property hv

/-- The weight-one grading submodule of the lattice triplet carrier is bottom. -/
theorem tripletWVOA_two_grading_one_eq_bot (hp : 1 ≤ 2) :
    (tripletWVOA 2 hp).grading 1 = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_tripletWVOA_two_grading_one hp hv
  · exact bot_le

/-- Conditional only on simplicity, lattice `W(2)` is strongly finite.  Weight-one vanishing
supplies strong CFT type and hence self-duality through the general recognition theorem; the
`C2`-cofiniteness input is unconditional. -/
theorem tripletWVOA_two_stronglyFinite_of_isSimple (hp : 1 ≤ 2)
    (hsimple : (tripletWVOA 2 hp).IsSimple) : StronglyFinite (tripletWVOA 2 hp) := by
  apply stronglyFinite_of_L_one_grading_one_eq_zero hsimple _
    (tripletWVOA_two_c2Cofinite hp)
  intro v hv
  have hv0 : v = 0 := eq_zero_of_mem_tripletWVOA_two_grading_one hp hv
  subst v
  exact map_zero ((tripletWVOA 2 hp).L 1)

/-- The full conditional benchmark on one carrier: simple lattice `W(2)` is strongly finite but
is neither admissibly rational nor Gannon-rational. -/
theorem tripletWVOA_two_stronglyFinite_and_irrational_of_isSimple (hp : 1 ≤ 2)
    (hsimple : (tripletWVOA 2 hp).IsSimple) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  ⟨tripletWVOA_two_stronglyFinite_of_isSimple hp hsimple,
    not_admissiblyRational_tripletWVOA_two hp,
    not_gannonRational_tripletWVOA_two hp⟩

/-- Independently of simplicity (proved separately, `tripletWVOA_two_isSimple`), lattice `W(2)`
cannot be strongly rational,
because strong rationality includes admissible rationality. -/
theorem not_stronglyRational_tripletWVOA_two (hp : 1 ≤ 2) :
    ¬ StronglyRational (tripletWVOA 2 hp) := by
  intro h
  exact not_admissiblyRational_tripletWVOA_two hp h.rational

end VOA.LatGen.Wp

section AxiomAudit
#print axioms VOA.LatGen.Wp.eq_zero_of_mem_tripletWVOA_two_grading_one
#print axioms VOA.LatGen.Wp.tripletWVOA_two_grading_one_eq_bot
#print axioms VOA.LatGen.Wp.tripletWVOA_two_stronglyFinite_of_isSimple
#print axioms VOA.LatGen.Wp.tripletWVOA_two_stronglyFinite_and_irrational_of_isSimple
#print axioms VOA.LatGen.Wp.not_stronglyRational_tripletWVOA_two
end AxiomAudit
