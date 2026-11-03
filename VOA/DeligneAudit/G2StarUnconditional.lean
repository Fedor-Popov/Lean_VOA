/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2StarLorenz
import VOA.DeligneAudit.DeligneMLDECubicEis

/-!
# The `G₂` target side, unconditionally

`G2Level3Core` (Borwein's cubic identity and the two level-3 Eisenstein identities for
`a = θ_{A₂}`) and `G2KWEqMLDE` (the Kac–Wakimoto form solves the AK recurrence with `h = 4`) hold
with no hypotheses: Lorenz's formula (`lorenzA2`, via the quintuple product identity and the
Wronskian of the Jacobi triple product at a cube root of unity), the Lambert-form Eisenstein
relations (`g2Level3EisLambert`, heat equation at `u = ω eˣ`) and Ramanujan's identities
(`ramanujanFormal`).  `G2StarIdentity` then rests only on `G2DemazureEqKW`.
-/

namespace VOA.DeligneAudit.G2Star

open VOA.DeligneAudit.DeligneCharacter

/-- **The level-3 core, unconditionally.** -/
theorem g2Level3Core : G2Level3Core := g2Level3Core_of_eisLambert g2Level3EisLambert

/-- **`G2KWEqMLDE`, unconditionally.** -/
theorem g2KWEqMLDE : G2KWEqMLDE := g2KWEqMLDE_of_eisLambert g2Level3EisLambert

/-- **`G2StarIdentity` from the Demazure/Kac–Wakimoto comparison alone.** -/
theorem g2StarIdentity_of_demazure (hD : G2DemazureEqKW) : G2StarIdentity :=
  g2StarIdentity_of_reduction hD g2KWEqMLDE

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.g2Level3Core
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE
#print axioms VOA.DeligneAudit.G2Star.g2StarIdentity_of_demazure
end AxiomAudit
