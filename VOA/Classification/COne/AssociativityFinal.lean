/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Classification.COne.AdmissibleOrdinaryBridge
import VOA.Huang.PzTensorDecompPBW

/-!
# Associativity of intertwining operators for strongly rational VOAs

Assembles Huang's associativity theorem (Huang 2005 §3; Huang–Lepowsky–Zhang IV Thm 5.44 / §6)
from the proved pieces:

* `VOA.Huang.PzTensorHL6`, `PzTensorDecomp`: associativity from the coefficient-space
  decomposition (log removal, `HLZ544_holds`, `Y3`/`Y4`, complete reducibility, finite fusion);
* `ABDWeakAdmissible.abdWeakIsAdmissible`: Abe–Buhl–Dong Prop. 5.7 (every weak module of a
  `C₂`-cofinite VOA is admissible), proved;
* `AdmissibleOrdinary.abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible`: ABD Cor. 5.8, proved;
* finiteness of the irreducibles from the PBW bottom projection `voaPBWBottomProjection`, the only
  place the theorem `VOA.pbw` enters.
-/

namespace VOA.Classification.COne

open VOA.Classification.COne.ABDWeakAdmissible VOA.Classification.COne.AdmissibleOrdinary

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VOA.VertexOperatorAlgebra 𝒱}

/-- **Associativity of intertwining operators** for every strongly rational VOA.
`#print axioms`: Lean's three standard axioms only.  The proof uses the theorem `VOA.pbw`, through
the finiteness of the set of irreducible modules
only. -/
theorem associativityInput_of_stronglyRational_pbw (hV : StronglyRational W) :
    VOA.Huang.AssocTarget.AssociativityInput W :=
  VOA.Huang.PzTensorDecompPBW.associativityInput_of_ABD_voaPBW hV abdWeakIsAdmissible
    (abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible abdWeakIsAdmissible)

end VOA.Classification.COne
