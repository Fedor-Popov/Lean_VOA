/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchStructuralClose

/-!
# The `StructuralData` assembly scaffold — the exact clean surface of Zhu Theorem 5.3.4

`Modules.ZhuVermaAnArchStructuralClose` proved `bijection_of_structural`, which produces the faithful
Zhu-5.3.4 bijection `Function.Bijective (forwardMapIrr W)` from exactly two inputs:

* `hslice : NeededSliceMems W`   — the Track-A keystone (carried, the sibling run's frontier);
* `sd : InducedAssignment.StructuralData W` — the 5-field structural bundle
  `⟨A, hirr, G, bregen, G'⟩`.

This file is the **Track-B constructor scaffold**: it assembles `sd : StructuralData W` from the
genuine construction data, discharging the two `A`/`hirr` fields as **terms** (via the HoleA canonical
route) and carrying the remaining genuinely-open analytic leaves as **precise hypotheses** — never a
`sorry`, never an axiom, never `pbw`.  It records the exact clean surface on which the whole bijection
rests.

## What is a TERM here (the discharged fields)

* **`A : InducedAssignment W`** — the canonical assignment `U ↦ L(U) = M(U)/J` on the genuine
  bimodule-composition loop representation, built as
  `bimodHoleA_inducedAssignment (G.toBimodGenuineConstructionA) ludataA realizes Dfun`
  (`ZhuVermaAnArchAGenuineRho`).  Here `ludataA U := (lumaxOfRegen G bregen U).toLUData` — the *same*
  maximal-`J` `LUData` that feeds `G'`'s family, so `A`'s `LUFamily` is on the nose the bijection's
  family.  The carrier, the level-shift loop action, module-Jacobi (from `hmi`), and the grading are
  all genuine terms inside `realize`.
* **`hirr : A.RealizeIrreducible`** — the TERM `realizeIrreducible_of_canonical …`
  (`ZhuVermaAnArchScopeClose`): each `A.realize U = L(U)` is irreducible by the proven
  `LUFamily.K_isIrreducibleLW`.  Not a carried hypothesis.

## What is CARRIED (the precise open analytic leaves)

* **`G : BimodGenuineConstructionAUniform W`** — carries, as its own fields, `MUGradedAction W`
  (`G.graded`, the Track-A keystone; do NOT re-prove) with all the genuinely-open level-shift
  leaves: `σ`, the DJ Prop 3.4 descents `hL`/`hR`, the Borcherds relations `hderiv`/`hbracket` (the
  deepest carried leaf, per `ZhuVermaAnArchRhoRelations`), the module-iterate `hmi`, and
  `hvac`/`htr`/`hL0`/`hfin`/`hbot`.
* **`bregen : BottomRegenData G`** — the SINGLE remaining maximal-`J` field (generation-from-bottom,
  Gannon Thm 5.3.4 / DJ 4.13); all sibling maximal-`J` fields are terms via `lumaxOfRegen`.
* **`realizes` / `Dfun`** — the bottom-survival iso and `M(·)`-functoriality datum feeding `A` (only
  `A`'s own `realizes`/`isoInvariant`; the bijection's `hiso` comes from `G` + `lumax`, not `Dfun`).
* **`G' : GenFromBottomGFamily …`** — the generation-from-bottom lift family (its `q_act` gate is
  bridged from `MUGradedAction`).

After this file the whole Zhu-5.3.4 bijection rests on exactly `[hslice, G, bregen, realizes, Dfun,
G']`, with `A`/`hirr` terms — the honest minimal structural surface.

## References
Dong–Jiang, Math. Z. 259 (2008), Prop 3.4–3.5, Thm 4.13; DLM3 §4; Frenkel–Zhu; Gannon §5.3.2,
Thm 5.3.4; `ZhuVermaAnArchStructuralClose` (`bijection_of_structural`, `StructuralData`,
`lumaxOfRegen`, `BottomRegenData`), `ZhuVermaAnArchConstructionAUniform`
(`BimodGenuineConstructionAUniform`), `ZhuVermaAnArchAGenuineRho` (`bimodHoleA_inducedAssignment`),
`ZhuVermaAnArchScopeClose` (`realizeIrreducible_of_canonical`).
-/

set_option linter.style.longLine false

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The maximal-`J` `LUData` shared by `A` and `G'` -/

/-- **The maximal-`J` `LUData` family from a per-`U` generation-from-bottom residue.**  On the nose the
`ludata` that `bijection_of_structural`/`lumaxOfRegen` feed to `G'`; reused here to source the lifting
datum `A` so both share the identical family.  A term (via `lumaxOfRegen … .toLUData`). -/
noncomputable def sdLudata (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) :
    ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U) :=
  fun U => (lumaxOfRegen G bregen U).toLUData

/-! ## `A` and `hirr` as TERMS -/

/-- **The lifting datum `A` as a TERM** — the canonical assignment `U ↦ L(U)` on the genuine
bimodule-composition loop representation, sharing the maximal-`J` family `sdLudata G bregen` with the
bijection's `G'` family.  The two abstract fields `realizes` (bottom survival) and `Dfun`
(`M(·)`-functoriality, sourcing only `A`'s own `isoInvariant`) are carried. -/
noncomputable def sdA (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G)
    (realizes : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod U)
    (Dfun : MUFunctorialData ((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen))) :
    InducedAssignment W :=
  bimodHoleA_inducedAssignment (G.toBimodGenuineConstructionA) (sdLudata G bregen) realizes Dfun

/-- **`hirr` as a TERM** — the realizations of `sdA` are irreducible.  Each `A.realize U = L(U)` is
the irreducible quotient `M(U)/J`, so `RealizeIrreducible` is the proven `LUFamily.K_isIrreducibleLW`
via `realizeIrreducible_of_canonical` (no carried hypothesis). -/
theorem sdHirr (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G)
    (realizes : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod U)
    (Dfun : MUFunctorialData ((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen))) :
    (sdA G bregen realizes Dfun).RealizeIrreducible :=
  realizeIrreducible_of_canonical (sdA G bregen realizes Dfun)
    ((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen))
    (fun U =>
      bimodHoleA_inducedAssignment_realize (G.toBimodGenuineConstructionA)
        (sdLudata G bregen) realizes Dfun U)

/-! ## The `StructuralData` assembly -/

/-- **`sdAssemble` — the `StructuralData W` assembled from the genuine construction data.**

Wires the two discharged fields (`A := sdA …`, `hirr := sdHirr …`) as terms and carries the remaining
genuinely-open leaves as precise hypotheses:

* `G : BimodGenuineConstructionAUniform W` — carries `MUGradedAction W` (`G.graded`) and the
  level-shift analytic leaves (`σ`/`hL`/`hR`/`hderiv`/`hbracket`/`hmi`/…);
* `bregen : BottomRegenData G` — the single remaining maximal-`J` field;
* `realizes`/`Dfun` — the bottom-survival iso and `M(·)`-functoriality feeding `A`;
* `G' : GenFromBottomGFamily (G.toLUFamily (lumaxOfRegen …).toLUData)` — the generation-from-bottom
  lift family.

The `G'` argument's family is on the nose `G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)`,
matching the `StructuralData.G'` field.  No `sorry`, **never** an axiom. -/
noncomputable def sdAssemble (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G)
    (realizes : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod U)
    (Dfun : MUFunctorialData ((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)))
    (G' : GenFromBottomGFamily (G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData))) :
    StructuralData W where
  A := sdA G bregen realizes Dfun
  hirr := sdHirr G bregen realizes Dfun
  G := G
  bregen := bregen
  G' := G'

end InducedAssignment

/-! ## The bijection from the assembled scaffold -/

/-- **`bijection_of_sdAssemble` — the faithful Zhu-5.3.4 bijection from the assembled scaffold.**

`Function.Bijective (forwardMapIrr W)` from the keystone `hslice` and the genuine construction data,
with `A`/`hirr` discharged as terms and the open leaves (`G` — carrying `MUGradedAction`, `bregen`,
`realizes`, `Dfun`, `G'`) carried as precise hypotheses.  This records the exact clean surface of the
whole bijection.  No `sorry`, **never** an axiom. -/
theorem bijection_of_sdAssemble {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (realizes : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily
        (InducedAssignment.sdLudata G bregen)).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((G.toBimodGenuineConstructionA).toLUFamily (InducedAssignment.sdLudata G bregen)))
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_structural hslice (InducedAssignment.sdAssemble G bregen realizes Dfun G')

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
