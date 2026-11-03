/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.AssociativityFinal
import VOA.Huang.CommutativityDLM
import VOA.Huang.AssocConverseUniqueness

/-!
# Commutativity (one half of braiding) of intertwining operators for strongly rational VOAs

`CommutativityHalf W` (products in one order continue analytically, through the upper half plane,
to products in the other order) follows from associativity (`associativityInput_of_stronglyRational_pbw`)
and skew-symmetry (`VOA.Huang.BraidingSkew.skewEquiv`), via
`VOA.Huang.CommutativityTarget.commutativityHalf_of_assoc`.
-/

namespace VOA.Classification.COne

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VOA.VertexOperatorAlgebra 𝒱}

/-- **Commutativity of intertwining operators (one half)** for every strongly rational VOA.
`#print axioms`: Lean's three standard axioms only (the proof uses the theorem `VOA.pbw`). -/
theorem commutativityHalf_of_stronglyRational_pbw (hV : StronglyRational W) :
    VOA.Huang.CommutativityTarget.CommutativityHalf W :=
  VOA.Huang.CommutativityTarget.commutativityHalf_of_assoc hV
    (associativityInput_of_stronglyRational_pbw hV)

/-- **Commutativity (braiding) of intertwining operators, both halves**, for every strongly
rational VOA: from associativity in both directions (`associativityBoth_of_stronglyRational_pbw`) and
skew-symmetry. `#print axioms`: Lean's three standard axioms only (the proof uses the theorem
`VOA.pbw`). -/
theorem commutativityInput_of_stronglyRational_pbw (hV : StronglyRational W) :
    VOA.Huang.CommutativityTarget.CommutativityInput W :=
  VOA.Huang.CommutativityTarget.commutativityInput_of_assoc hV
    (associativityInput_of_stronglyRational_pbw hV)
    (VOA.Huang.AssocConverse.associativityConverse_of_stronglyRational_pbw hV)

end VOA.Classification.COne
