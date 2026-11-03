/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureEnergy
import VOA.DeligneAudit.DeligneCharacterExceptional

/-!
# `E₆`: Demazure energies are nonnegative

`F` = the `W(E₆)`-orbit of `θ^∨` (all 72 roots, as functionals on root coordinates); the
`OrbitData` checks are `decide +kernel`, one per simple letter.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

/-- The `W(E₆)`-orbit of `⟨·, θ^∨⟩`. -/
def e6CorootOrbit : List (List ℤ) :=
  [[-2, 0, 1, 0, 0, 0], [-1, -1, 0, 0, 1, 0], [-1, -1, 0, 1, -1, 1], [-1, -1, 0, 1, 0, -1], [-1, -1, 1, 0, 0, 1], [-1, -1, 1, 0, 1, -1], [-1, -1, 1, 1, -1, 0], [-1, 0, -1, 1, 0, 0], [-1, 0, 0, 0, 1, 0], [-1, 0, 0, 1, -1, 1], [-1, 0, 0, 1, 0, -1], [-1, 0, 1, -1, 0, 1], [-1, 0, 1, -1, 1, -1], [-1, 0, 1, 0, -1, 0], [-1, 0, 2, -1, 0, 0], [-1, 1, 0, -1, 1, 0], [-1, 1, 0, 0, -1, 1], [-1, 1, 0, 0, 0, -1], [-1, 1, 1, -1, 0, 1], [-1, 1, 1, -1, 1, -1], [-1, 1, 1, 0, -1, 0], [0, -2, 0, 1, 0, 0], [0, -1, -1, 1, 0, 1], [0, -1, -1, 1, 1, -1], [0, -1, -1, 2, -1, 0], [0, -1, 0, 0, 0, 0], [0, -1, 0, 1, 0, 0], [0, -1, 1, -1, 1, 0], [0, -1, 1, 0, -1, 1], [0, -1, 1, 0, 0, -1], [0, 0, -1, 0, 0, 1], [0, 0, -1, 0, 1, -1], [0, 0, -1, 1, -1, 0], [0, 0, 0, -1, 1, 1], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2], [0, 0, 0, 0, 1, -2], [0, 0, 0, 1, -2, 1], [0, 0, 0, 1, -1, -1], [0, 0, 1, -1, 1, 0], [0, 0, 1, 0, -1, 1], [0, 0, 1, 0, 0, -1], [0, 1, -1, 0, 0, 1], [0, 1, -1, 0, 1, -1], [0, 1, -1, 1, -1, 0], [0, 1, 0, -1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, -2, 1, 0], [0, 1, 1, -1, -1, 1], [0, 1, 1, -1, 0, -1], [0, 2, 0, -1, 0, 0], [1, -1, -1, 0, 1, 0], [1, -1, -1, 1, -1, 1], [1, -1, -1, 1, 0, -1], [1, -1, 0, 0, 0, 1], [1, -1, 0, 0, 1, -1], [1, -1, 0, 1, -1, 0], [1, 0, -2, 1, 0, 0], [1, 0, -1, 0, 1, 0], [1, 0, -1, 1, -1, 1], [1, 0, -1, 1, 0, -1], [1, 0, 0, -1, 0, 1], [1, 0, 0, -1, 1, -1], [1, 0, 0, 0, -1, 0], [1, 0, 1, -1, 0, 0], [1, 1, -1, -1, 1, 0], [1, 1, -1, 0, -1, 1], [1, 1, -1, 0, 0, -1], [1, 1, 0, -1, 0, 1], [1, 1, 0, -1, 1, -1], [1, 1, 0, 0, -1, 0], [2, 0, -1, 0, 0, 0]]

theorem e6_letters (i : ℕ) (hi : i < 6) :
    ∀ φ ∈ e6CorootOrbit, reflFunFin 6 cartanE6 i φ ∈ e6CorootOrbit := by
  interval_cases i <;> decide +kernel

theorem e6_theta : ∀ φ ∈ e6CorootOrbit, reflFunTheta 6 cartanE6 thetaE6 φ ∈ e6CorootOrbit := by
  decide +kernel

theorem e6OrbitData : OrbitData 6 cartanE6 thetaE6 wordE6 e6CorootOrbit :=
  OrbitData.of_letters rfl (by decide) e6_letters e6_theta (by decide +kernel) (by decide +kernel)

/-- **`E₆` Demazure energies are nonnegative.** -/
theorem e6DemazureEnergy (m : ℕ) :
    ∀ t ∈ demazureChar cartanE6 thetaE6 wordE6 m, 0 ≤ t.1.2 + (m : ℤ) * m :=
  energy_of_orbit e6OrbitData m

end VOA.DeligneAudit.DeligneCharacter.DemCount

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.e6DemazureEnergy
end AxiomAudit
