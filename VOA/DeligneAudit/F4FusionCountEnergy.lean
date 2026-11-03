/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureEnergy
import VOA.DeligneAudit.DeligneCharacterExceptional

/-!
# `F₄`: Demazure energies are nonnegative

`F` = the `W(F₄)`-orbit of `⟨·, θ^∨⟩` (24 functionals on root coordinates, computed outside
Lean); the `energy_of_orbit`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

/-- The `W(F₄)`-orbit of `⟨·, θ^∨⟩`. -/
def f4CorootOrbit : List (List ℤ) :=
  [[-1, 0, 0, 0], [1, -1, 0, 0], [1, 0, 0, 0], [0, 1, -1, 0], [2, -1, 0, 0], [-1, 1, 0, 0],
   [0, -1, 1, -1], [1, 1, -1, 0], [-2, 1, 0, 0], [0, -1, 1, 0], [-1, 1, 0, -1], [0, -1, 0, 1],
   [1, -1, 1, -1], [-1, 2, -1, 0], [-1, -1, 1, 0], [0, 1, -1, 1], [1, 0, 0, -1], [-1, 1, -1,
   1], [0, 1, 0, -1], [1, -1, 0, 1], [-1, 0, 1, -1], [1, -2, 1, 0], [1, 0, -1, 1], [-1, 0, 0,
   1]]

theorem f4_letters (i : ℕ) (hi : i < 4) :
    ∀ φ ∈ f4CorootOrbit, reflFunFin 4 cartanF4 i φ ∈ f4CorootOrbit := by
  interval_cases i <;> decide +kernel

theorem f4_theta : ∀ φ ∈ f4CorootOrbit, reflFunTheta 4 cartanF4 thetaF4 φ ∈ f4CorootOrbit := by
  decide +kernel

theorem f4OrbitData : OrbitData 4 cartanF4 thetaF4 wordF4 f4CorootOrbit :=
  OrbitData.of_letters rfl (by decide) f4_letters f4_theta (by decide +kernel) (by decide +kernel)

/-- **`F₄` Demazure energies are nonnegative.** -/
theorem f4DemazureEnergy (m : ℕ) :
    ∀ t ∈ demazureChar cartanF4 thetaF4 wordF4 m, 0 ≤ t.1.2 + (m : ℤ) * m :=
  energy_of_orbit f4OrbitData m

end VOA.DeligneAudit.DeligneCharacter.DemCount

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.f4DemazureEnergy
end AxiomAudit
