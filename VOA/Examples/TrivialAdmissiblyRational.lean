/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.ZhuInstantiation
import VOA.Modules.AdmissibleRationality

/-!
# The trivial VOA is admissibly rational — the positive witness

`Modules/AdmissibleRationality.lean` defines `AdmissiblyRational` (Zhu, JAMS **9** (1996);
Dong–Li–Mason, J. Algebra **206** (1998)) and `Examples/TripletIrrational.lean` derives
`¬ AdmissiblyRational tripletW2` from it.  A negative result is only as good as the evidence that
the predicate is satisfiable at all: an accidentally over-strong predicate would make every
`¬ AdmissiblyRational …` theorem true and worthless.

This file closes that gap by exhibiting a VOA that **does** satisfy it.  `trivialVOA = ℂ𝟙`
(the rank-zero lattice VOA, `Examples/ZhuInstantiation.lean`) is spanned by its vacuum, so every
`ℂ`-subspace of every weak module is a weak submodule and complements always exist
(`admissiblyRational_of_span_vacuum`).

Two separate vacuity worries are closed:

* **The predicate has a model**: `trivial_admissiblyRational`.
* **The quantified class has objects**: `adjointAdmissibleModule trivialVOA` is an admissible
  module with a *nontrivial* carrier (`trivialAdjointAdmissible_nontrivial`), so
  `AdmissiblyRational trivialVOA` is not true merely for want of admissible modules.

⚠ Consistency check worth stating: `trivialVOA` is also the VOA for which
`Examples/ZhuInstantiation.trivial_semisimpleA` proves `IsSemisimpleRing (A trivialVOA)`.  So the
named hypothesis `ZhuAdmissibleSemisimple trivialVOA` (Zhu Thm 2.2.3) is *consistent* here — the
irrationality machinery does not degenerate into "no VOA is admissibly rational".

## Status
`sorry`-free / axiom-free.
-/

namespace VOA

/-- **The trivial VOA `ℂ𝟙` is rational in the standard (Zhu / Dong–Li–Mason) admissible
sense.**  The positive witness that keeps `¬ AdmissiblyRational` from being vacuous. -/
theorem trivial_admissiblyRational : AdmissiblyRational trivialVOA :=
  admissiblyRational_of_span_vacuum trivialVOA trivial_span_vacuum

/-- The adjoint admissible module of the trivial VOA has a nontrivial carrier: the admissible
category over `trivialVOA` really does contain a nonzero object. -/
theorem trivialAdjointAdmissible_nontrivial :
    Nontrivial (LatGen.LatModuleGen (stdLattice 0)) := inferInstance

/-- Spelled out: the trivial VOA's own grading makes `𝒱 = ℂ𝟙` an admissible module over itself,
and that module is completely reducible. -/
theorem trivialAdjointAdmissible_isCompletelyReducible :
    (adjointAdmissibleModule trivialVOA).IsCompletelyReducible :=
  trivial_admissiblyRational (adjointAdmissibleModule trivialVOA)

end VOA
