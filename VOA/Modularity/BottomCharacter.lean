/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LeadingCoeff
import VOA.Modularity.CharIndependence

/-!
# The leading `q`-coefficient of a trace function IS the character of the bottom

The third brick of residual **(d)**.  `Modularity.LeadingCoeff` shows the leading coefficient of a
one-point function is detected by its values on `ℍ`; `Modularity.CharIndependence` separates the
characters of pairwise non-isomorphic simple `A(𝒱)`-modules.  This file identifies the two: for a
lowest-weight module the leading coefficient of `𝒵_M(v; q)` is exactly `tr_{M_h} ρ([v])`, the
character of the bottom as an `A(𝒱)`-module.

## Main results

* `torusOnePoint_at_bottom` — `𝒵_M(v)(h − c/24) = tr_{M_h} (actA [v])`;
* `torusOnePoint_at_bottom_lowestAMod` — the same through the bundled `lowestAMod`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Transport of the graded trace along an equality of weights. -/
private theorem trace_weightBlock_congr (N : OrdVModule W M) (v : 𝒱) {α β : ℂ} (h : α = β) :
    (haveI := N.finrank α; LinearMap.trace ℂ (N.weight α) (weightBlock N (oMod N v) α))
      = (haveI := N.finrank β; LinearMap.trace ℂ (N.weight β) (weightBlock N (oMod N v) β)) := by
  subst h; rfl

/-- **The leading coefficient of a one-point function is the bottom character.** -/
theorem torusOnePoint_at_bottom (N : OrdVModule W M) {hw : ℂ} (hlow : IsLowestWeight N hw) (v : 𝒱) :
    torusOnePoint N v (hw - W.centralCharge / 24)
      = haveI := N.finrank hw; LinearMap.trace ℂ (N.weight hw) (actA N hlow (mk W v)) := by
  have hc : hw - W.centralCharge / 24 + W.centralCharge / 24 = hw := by ring
  haveI := N.finrank hw
  rw [actA_mk]
  have h1 : onePoint N v (hw - W.centralCharge / 24)
      = (haveI := N.finrank hw
         LinearMap.trace ℂ (N.weight hw) (weightBlock N (oMod N v) hw)) :=
    trace_weightBlock_congr N v hc
  show onePoint N v (hw - W.centralCharge / 24) = _
  rw [h1]
  rfl

/-- The same, through the bundled `lowestAMod` action. -/
theorem torusOnePoint_at_bottom_lowestAMod (N : OrdVModule W M) {hw : ℂ}
    (hlow : IsLowestWeight N hw) (v : 𝒱) :
    torusOnePoint N v (hw - W.centralCharge / 24)
      = haveI := N.finrank hw
        LinearMap.trace ℂ ((lowestAMod hlow).carrier) ((lowestAMod hlow).ρ (mk W v)) :=
  torusOnePoint_at_bottom N hlow v

end VOA
