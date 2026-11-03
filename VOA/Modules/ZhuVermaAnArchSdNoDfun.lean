/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdAssemble

/-!
# Eliminating `Dfun` from the `StructuralData` assembly — `bijection_of_sdAssemble_noDfun`

`Modules.ZhuVermaAnArchSdAssemble` proved `bijection_of_sdAssemble`, which produces the faithful
Zhu-5.3.4 bijection `Function.Bijective (forwardMapIrr W)` from six explicit inputs
`[hslice, G, bregen, realizes, Dfun, G']`, with `A`/`hirr` discharged as terms `sdA`/`sdHirr`.

The `Dfun : MUFunctorialData (G.toLUFamily (sdLudata G bregen))` input is consumed **only** to
build the lifting datum `A = sdA … Dfun` (its `isoInvariant` field feeds
`CanonicalAssignmentData.toInducedAssignment`).  It is **not** consumed by the bijection's own
`hiso` (functoriality) clause: `bijection_of_structural → phase4_of_dj28_uniform_regen →
phase4_of_dj28_uniform_lumax` sources `hiso` entirely from the *proven* DJ Prop 3.4/3.5 discharge
for the level-shift construction, `A` being used only for `hirr` and as the abstract lifting datum.

This file eliminates `Dfun` as a **carried** input by producing it as a **TERM**.  For the genuine
uniform Construction-A family both DJ naturality residuals are theorems:

* DJ Prop 3.4 (`MUActionNatural`) — the proven term `G.actionNatural (sdLudata G bregen)` (the
  level-shift action touches only the first tensor factor, `MUActionNatural_of_levelShift`);
* DJ Prop 3.5 (`MUJNatural`) — proven from the canonical-`J` identity via
  `G.mujNatural_of_canonicalJ`, whose `hJcanon` input is discharged by `LUMaxData.J_eq_Jcanon`
  applied to the maximal-`J` datum `lumaxOfRegen G bregen U` that *defines* `sdLudata`.

Assembling these two via `MUFunctorialData.ofNaturality` yields `Dfun` as a genuine term
`sdDfun G bregen`.  Feeding it to `bijection_of_sdAssemble` drops the leaf set `6 → 5`:
`bijection_of_sdAssemble_noDfun` takes exactly `[hslice, G, bregen, realizes, G']`.

## What is proved as a TERM here (the eliminated leaf)

* **`sdDfun G bregen : MUFunctorialData (G.toLUFamily (sdLudata G bregen))`** — the
  `M(·)`-functoriality datum, not carried; every ingredient (`MUActionNatural`, `MUJNatural`
  via `J = Jcanon`) is a proven theorem for the uniform level-shift construction.

## What remains CARRIED (unchanged)

`hslice` (the Track-A keystone `NeededSliceMems`), `G : BimodGenuineConstructionAUniform W`
(carrying `MUGradedAction W = G.graded` and the level-shift analytic leaves), `bregen`
(generation-from-bottom), `realizes` (bottom survival), and `G'` (the generation-from-bottom lift
family).  Five leaves.  No `sorry`, **never** an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008), Prop 3.4–3.5, Thm 4.13; Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchConstructionAUniform` (`BimodGenuineConstructionAUniform.actionNatural`,
`BimodGenuineConstructionAUniform.mujNatural_of_canonicalJ`), `ZhuVermaAnArchMUJNaturalCanonical`
(`LUMaxData.J_eq_Jcanon`), `ZhuVermaAnArchHoleMuEquiv` (`MUFunctorialData.ofNaturality`),
`ZhuVermaAnArchSdAssemble` (`bijection_of_sdAssemble`, `sdLudata`, `sdA`, `sdHirr`).
-/

set_option linter.style.longLine false

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## `MUJNatural` for the `sdLudata` family as a TERM (via `J = Jcanon`) -/

/-- **DJ Prop 3.5 (`MUJNatural`) for the `sdLudata G bregen` family as a TERM.**

The maximal-`J` datum feeding `sdLudata` is `lumaxOfRegen G bregen U`, a genuine `LUMaxData`.  By
`LUMaxData.J_eq_Jcanon`, its `J` is the *canonical* maximal bottom-trivial graded submodule
`Jcanon`.  Combined with the proven DJ Prop 3.4 naturality of the uniform level-shift action
(`G.actionNatural`), `G.mujNatural_of_canonicalJ` upgrades this to the full DJ Prop 3.5 naturality
`MUJNatural (G.toLUFamily (sdLudata G bregen))`.  A term (no carried hypothesis, no axiom). -/
theorem sdMujNatural (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) :
    MUJNatural (G.toLUFamily (sdLudata G bregen)) :=
  G.mujNatural_of_canonicalJ (sdLudata G bregen)
    (fun U => LUMaxData.J_eq_Jcanon (G.toLUFamily (sdLudata G bregen)) U (lumaxOfRegen G bregen U))

/-! ## `Dfun` as a TERM -/

/-- **The `M(·)`-functoriality datum `Dfun` as a TERM.**

Both Dong–Jiang naturality residuals of the uniform level-shift construction are theorems: DJ Prop
3.4 (`MUActionNatural`, the term `G.actionNatural (sdLudata G bregen)`) and DJ Prop 3.5
(`MUJNatural`, the term `sdMujNatural G bregen`).  Assembling them through the genuine functor map
`MU.functorEquiv` (`MUFunctorialData.ofNaturality`) produces the full
`MUFunctorialData (G.toLUFamily (sdLudata G bregen))` — not a carried leaf. -/
noncomputable def sdDfun (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) :
    MUFunctorialData ((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)) :=
  MUFunctorialData.ofNaturality (G.actionNatural (sdLudata G bregen)) (sdMujNatural G bregen)

end InducedAssignment

/-! ## The bijection without a carried `Dfun` (six leaves reduced to five) -/

/-- **`bijection_of_sdAssemble_noDfun` — the faithful Zhu-5.3.4 bijection with `Dfun` eliminated.**

`Function.Bijective (forwardMapIrr W)` from exactly FIVE inputs — the keystone `hslice` and the
genuine construction data `[G, bregen, realizes, G']` — with `A`/`hirr` discharged as terms
(`sdA`/`sdHirr`) *and* the `M(·)`-functoriality datum `Dfun` discharged as the term
`sdDfun G bregen`.  Compared with `bijection_of_sdAssemble`, the carried leaf `Dfun` is gone: it is
sourced from the proven DJ Prop 3.4 (`G.actionNatural`) + DJ Prop 3.5 (`J = Jcanon`, `sdMujNatural`)
discharge for the uniform level-shift construction.  This shrinks the structural surface `6 → 5`.
No `sorry`, **never** an axiom. -/
theorem bijection_of_sdAssemble_noDfun {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (realizes : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily
        (InducedAssignment.sdLudata G bregen)).K U).toAMod U)
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_sdAssemble hslice G bregen realizes (InducedAssignment.sdDfun G bregen) G'

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
