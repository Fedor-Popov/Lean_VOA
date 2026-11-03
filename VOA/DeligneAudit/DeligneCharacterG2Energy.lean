import VOA.DeligneAudit.DeligneCharacterDemazureEnergy
import VOA.DeligneAudit.DeligneCharacterExceptionalParameters

/-! The G2 energy theorem and its finite special case use only character data. -/
namespace VOA.DeligneAudit.DeligneCarrier
open VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.DeligneCharacter.DemCount

/-- **Named input**: the `G₂` Demazure energies are nonnegative (extremal vector in degree `0`).
Checked by kernel computation for `m ≤ 2` (`g2DemazureEnergy_small`). -/
def G2DemazureEnergy : Prop :=
  ∀ m : ℕ, ∀ t ∈ demazureChar cartanG2 thetaG2 wordG2 m, 0 ≤ t.1.2 + (m : ℤ) * m

/-- The `W(G₂)`-orbit of the functional `⟨·, θ^∨⟩` (root coordinates). -/
def g2CorootOrbit : List (List ℤ) := [[-1, 1], [-1, 2], [0, -1], [0, 1], [1, -2], [1, -1]]

theorem g2OrbitData : DemCount.OrbitData 2 cartanG2 thetaG2 wordG2 g2CorootOrbit :=
  ⟨rfl, by decide, by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩

/-- **`G2DemazureEnergy` holds.** -/
theorem g2DemazureEnergy_holds : G2DemazureEnergy :=
  DemCount.energy_of_orbit g2OrbitData

theorem g2DemazureEnergy_small :
    ∀ m ∈ List.range 3, ∀ t ∈ demazureChar cartanG2 thetaG2 wordG2 m, 0 ≤ t.1.2 + (m : ℤ) * m := by
  intro m _ t ht
  exact g2DemazureEnergy_holds m t ht

end VOA.DeligneAudit.DeligneCarrier

#print axioms VOA.DeligneAudit.DeligneCarrier.g2DemazureEnergy_holds
