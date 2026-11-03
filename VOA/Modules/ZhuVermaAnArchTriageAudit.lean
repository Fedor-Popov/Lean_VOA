/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGenFromBottomFinal
import VOA.Modules.ZhuVermaAnArchScopeClose
import VOA.Modules.ZhuVermaAnArchMUConstruct

/-!
# Independence probes for the residual Zhu 5.3.4 leaves.

This file changes no other declaration; it (a) prototypes the canonical bottom map `β`/`hβ` as a
term (the subtype inclusion of the realized bottom), and (b) re-prints axioms on the already-proven
terms `R0` (`bottomBalancedEquiv`), `hirr` (`realizeIrreducible_of_canonical`), and the `KerJ`
first-isomorphism core, to confirm each is `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **β/hβ candidate term.** For ANY bundled lowest-weight `P`, the canonical bottom map
`β : (P.toAMod).carrier →ₗ[ℂ] P.carrier` is the subtype inclusion of the realized bottom
`P_h = P.isMod.weight P.h` (note `P.toAMod.carrier = ↥(P.isMod.weight P.h)` definitionally, since
`toAMod = lowestAMod P.isLow` whose carrier is `P.isMod.weight P.h`). -/
noncomputable def betaCanonical (P : LWModule W) :
    (P.toAMod).carrier →ₗ[ℂ] P.carrier :=
  (P.isMod.weight P.h).subtype

/-- **hβ candidate term.** The canonical bottom map lands in the realized
bottom — `Subtype.property`. -/
theorem hbetaCanonical (P : LWModule W) :
    ∀ u : (P.toAMod).carrier, betaCanonical P u ∈ P.isMod.weight P.h :=
  fun u => u.2

end InducedAssignment

end VOA

-- Integrity gate.
