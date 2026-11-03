/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchTriageAudit
import VOA.Modules.ZhuVermaAnArchLayerAction
import VOA.Modules.Character

/-!
# Leaf 2 — `bottom_ne_zero` for the canonical bottom map (a term, axiom-clean)

This file retires one of the *independent, tractable* leaves of the residual Zhu 5.3.4 assembly
(`GenFromBottomFinalData.bottom_ne_zero`, `ZhuVermaAnArchGenFromBottomFinal.lean:123`) **as a term**,
for the **canonical** bottom map `β = betaCanonical P` (the subtype inclusion of the realized bottom,
built term-level in `ZhuVermaAnArchTriageAudit`).

The statement is the **`BottomOrbit` survival of the bottom**:

  `(GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction 0
    ≠ 0`.

It is **genuinely independent** of the two hard cores of Zhu 5.3.4 — the cross-tower membership
`crossCirc0_mem_Onm` / `CrossCirc0TowerEq` (which gates `q_act` / `MUGradedAction`) and the universal
property `GeneratedFromBottom` (the injective half).  Nothing here touches `MU`, the cross-tower, or
`L(U)`: the level-`0` layer map evaluated at the vacuum pure tensor `[𝟙] ⊗ u` is, by the chain

  `layerAction 0 ([𝟙] ⊗ u) = gMode P.isMod 0 𝟙 (β u)`  (`toLayerActionData_layerAction_tmul`)
                          `= oMod  P.isMod   𝟙 (β u)`  (`gMode_zero`)
                          `= β u`                       (`oMod_vacuum`, `LinearMap.id`)
                          `= u.1`                       (`betaCanonical = subtype`),

simply the underlying weight vector `u.1`.  Since `P` is *realized* (`P.isMod.weight P.h ≠ ⊥`,
`LWModule.realized`) there is a nonzero `u₀ : P.isMod.weight P.h`, so the map sends a pure tensor to a
nonzero vector and is therefore not the zero map.

All ingredients (`oMod_vacuum`, `gMode_zero`, `toLayerActionData_layerAction_tmul`, `LWModule.realized`)
are pre-existing, axiom-clean terms; this file only assembles them.  `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`.

## References
Gannon §5.3.2, Thm 5.3.4; Dong–Jiang `math/0601626`; `ZhuVermaAnArchFreenessDescent`
(`gMode_zero`, `GradedModeVanish.ofBottom`/`.toLayerActionData`), `Character` (`oMod_vacuum`),
`ZhuBijection` (`LWModule`, `lowestAMod`, `betaCanonical`).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The level-`0` canonical layer map, on the vacuum pure tensor `[𝟙] ⊗ u`, returns `β u`.**

`layerAction 0 ([𝟙] ⊗ u) = gMode P.isMod 0 𝟙 (β u) = oMod P.isMod 𝟙 (β u) = β u`
(`toLayerActionData_layerAction_tmul`, `gMode_zero`, `oMod_vacuum`).  Here `β = betaCanonical P` is
the subtype inclusion of the realized bottom, so `β u = u.1`. -/
theorem canonicalLayer0_vacuum_tmul (P : LWModule W) (u : (P.toAMod).carrier) :
    (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction 0
        (mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] u)
      = betaCanonical P u := by
  rw [GradedModeVanish.toLayerActionData_layerAction_tmul, gMode_zero, oMod_vacuum,
    LinearMap.id_apply]

/-- **Leaf 2 — `bottom_ne_zero` for the canonical bottom map (`BottomOrbit` survival).**

The level-`0` layer map of the term-level freeness `GradedModeVanish.ofBottom (betaCanonical P)
(hbetaCanonical P)` is **not** the zero map.  Witnessed at the vacuum pure tensor `[𝟙] ⊗ u₀` for a
nonzero `u₀` in the realized bottom (`LWModule.realized`); the value is `u₀.1 ≠ 0`.

Genuinely independent of the cross-tower keystone and the universal property. -/
theorem canonical_bottom_ne_zero (P : LWModule W) :
    (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction 0
      ≠ 0 := by
  -- A nonzero element of the realized bottom `P_h = P.isMod.weight P.h`.
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).1 P.realized
  -- Repackage it as a `(P.toAMod).carrier = ↥(P.isMod.weight P.h)` element.
  set u₀ : (P.toAMod).carrier := ⟨v, hv_mem⟩ with hu₀
  intro hzero
  -- Evaluating the (assumed zero) map at the vacuum pure tensor must give `0`...
  have hval :
      (GradedModeVanish.ofBottom (betaCanonical P)
          (hbetaCanonical P)).toLayerActionData.layerAction 0
          (mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] u₀) = 0 := by
    rw [hzero, LinearMap.zero_apply]
  -- ... but it is `β u₀ = u₀.1 = v ≠ 0`.
  rw [canonicalLayer0_vacuum_tmul] at hval
  -- `betaCanonical P u₀ = (P.isMod.weight P.h).subtype ⟨v, _⟩ = v` definitionally.
  exact hv_ne hval

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
