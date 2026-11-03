/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchL0Semisimple

/-!
# Structural-half close — `lumax` from `bottom_regen` alone; the minimal structural surface

`Modules.ZhuVermaAnArchL0Semisimple` reduced the per-`U` maximal-`J` datum `LUMaxData` to the SINGLE
deep field `bottom_regen` (generation-from-bottom, Gannon Thm 5.3.4 / DJ 4.13) via
`MaxJData.ofRegen` (`J`, `J_graded`, `bottom_disjoint`, `quot_submodule_graded` =
`L₀`-semisimplicity, and `quot_graded_simple` all terms).

This file threads that through the proven main theorem `phase4_of_dj28_uniform_lumax`: it builds the
whole `lumax : ∀ U, LUMaxData …` from a per-`U` `bottom_regen` residue (`lumaxOfRegen`), and
re-exports the faithful bijection consuming `bottom_regen` in place of `lumax`
(`phase4_of_dj28_uniform_regen`).  This makes the maximal-`J` residue of the whole Zhu-5.3.4
bijection **exactly** `bottom_regen`.

## The honest minimal structural surface

After this file, `Function.Bijective (forwardMapIrr W)` is a term modulo the following inputs, of
which the ONLY non-structural (A-run) one is the keystone `hslice`:

* `hslice : NeededSliceMems W`   — **the keystone** (`MUGradedAction` / the A-direction cross-circle
  memberships); carried, the sibling run's frontier.  Threads through `hslice`, `G.graded`,
  `G.hL`/`G.hR`, and `G'`'s gate.
* `G : BimodGenuineConstructionAUniform W` — the genuine admissible `M(U)`: `σ`/`hderiv`/`hbracket`
  (the level-shift loop action's Borcherds relations), `hmi` (`ModuleIterate`), `htr`/`hvac`/`hL0`/
  `hfin`/`hbot` — the genuine Frenkel–Zhu construction data (`hL`/`hR`/`graded` keystone-shaped).
* `bottom_regen` (per-`U`) — generation-from-bottom, the SINGLE remaining maximal-`J` field.
* `G' : GenFromBottomGFamily …` — the generation-from-bottom lift (its gate is the keystone).
* `A`/`hirr` — the lifting datum and its irreducible realizations (ρ-side terms; `hirr` from the
  proven `quot_graded_simple`).

`hiso` (functoriality) contributes **no** residual (fully proven), and the
maximal-`J` machinery is a term except for `bottom_regen`.

## References
Dong–Li–Mason J. Algebra 206 (1998); Dong–Jiang Math. Z. 259 (2008) §3–4; Frenkel–Zhu (generalized
Verma); Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchL0Semisimple` (`MaxJData.ofRegen`),
`ZhuVermaAnArchLumax` (`MaxJData.toLUMaxData`), `ZhuVermaAnArchMUJNaturalCanonical`
(`phase4_of_dj28_uniform_lumax`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The per-`U` `lumax` from a per-`U` `bottom_regen`.**  Uses `MaxJData.ofRegen` (with
`sup_bottom_disjoint`/`quot_submodule_graded` supplied as terms) and `MaxJData.toLUMaxData`; the
maximal `J := supBotTrivialGraded` is genuine, and only `bottom_regen` is carried. -/
noncomputable def lumaxOfRegen (G : BimodGenuineConstructionAUniform W)
    (bregen : ∀ (U : AMod W)
      (Q : WeakModule.Submodule'
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.toWeakModule),
      OrdVModule.IsGradedSubmodule
          ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule Q →
        Q.carrier ⊓ ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.weight
            ((G.toBimodGenuineConstructionA).toMURepFamily.hU U) ≠ ⊥ →
          Q.carrier = ⊤) :
    ∀ U : AMod W, MUModuleData.LUMaxData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U) :=
  fun U => (MUModuleData.MaxJData.ofRegen _ (bregen U)).toLUMaxData

end InducedAssignment

/-- **`phase4_of_dj28_uniform_regen` — the faithful Zhu-5.3.4 bijection with the maximal-`J` residue
reduced to `bottom_regen` alone.**

Identical to `phase4_of_dj28_uniform_lumax`, but consuming the per-`U` generation-from-bottom
residue `bregen` in place of the whole `lumax` (built here via `lumaxOfRegen`).  So the maximal-`J`
machinery of the structural half is a term except for the single deep field `bottom_regen`; the only
non-structural input is the keystone `hslice`. -/
theorem phase4_of_dj28_uniform_regen {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : ∀ (U : AMod W)
      (Q : WeakModule.Submodule'
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.toWeakModule),
      OrdVModule.IsGradedSubmodule
          ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule Q →
        Q.carrier ⊓ ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.weight
            ((G.toBimodGenuineConstructionA).toMURepFamily.hU U) ≠ ⊥ →
          Q.carrier = ⊤)
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_uniform_lumax hslice A hirr G (InducedAssignment.lumaxOfRegen G bregen) G'

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The generation-from-bottom residue** for the uniform construction `G` — the SINGLE remaining
maximal-`J` field: any graded submodule of `M(U)` meeting the bottom `M(U)_h` nontrivially is all of
`M(U)` (`M(U)` is generated from its bottom, Gannon Thm 5.3.4 / DJ 4.13). -/
@[reducible] def BottomRegenData (G : BimodGenuineConstructionAUniform W) : Prop :=
  ∀ (U : AMod W) (Q : WeakModule.Submodule'
      ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.toWeakModule),
    OrdVModule.IsGradedSubmodule
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule Q →
      Q.carrier ⊓ ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toOrdVModule.weight
          ((G.toBimodGenuineConstructionA).toMURepFamily.hU U) ≠ ⊥ →
        Q.carrier = ⊤

/-- **The complete structural-half data of Zhu Theorem 5.3.4** — everything the bijection needs
*beyond the keystone*.  All `hiso` (functoriality) and maximal-`J` machinery is already proven; this
bundles the genuine remaining Frenkel–Zhu/DLM construction data:

* `A`/`hirr` — the `U ↦ M̄(U)` lifting datum and its irreducible realizations;
* `G` — the genuine admissible `M(U)` (the level-shift loop representation: `σ`, the Borcherds
  relations `hderiv`/`hbracket`, the iterate `hmi`, and the grading/finiteness fields);
* `bregen` — generation-from-bottom (the single remaining maximal-`J` field);
* `G'` — the generation-from-bottom lift family.

A hypothesis structure carrying the genuine construction; **never** an axiom. -/
structure StructuralData (W : VertexOperatorAlgebra 𝒱) where
  /-- The lifting datum. -/
  A : InducedAssignment W
  /-- Its realizations are irreducible. -/
  hirr : A.RealizeIrreducible
  /-- The genuine admissible `M(U)` (uniform Construction-A). -/
  G : BimodGenuineConstructionAUniform W
  /-- Generation-from-bottom (the single maximal-`J` residue). -/
  bregen : BottomRegenData G
  /-- The generation-from-bottom lift family. -/
  G' : GenFromBottomGFamily (G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData))

end InducedAssignment

/-- **`bijection_of_structural` — the faithful Zhu-5.3.4 bijection from the keystone + the
structural bundle.**

The entire structural (`B`) half is packaged into one datum `sd : StructuralData W`; the only other
input is the keystone `hslice : NeededSliceMems W` (the A-run's `MUGradedAction`).  So from the
A-team's viewpoint, the bijection `Function.Bijective (forwardMapIrr W)` rests on the keystone
alone, with the structural side a single bundled term.  `hiso` and the maximal-`J` machinery (bar
`bregen`) are proven; the bundle carries the genuine remaining Frenkel–Zhu/DLM construction data. -/
theorem bijection_of_structural {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W) (sd : InducedAssignment.StructuralData W) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_uniform_regen hslice sd.A sd.hirr sd.G sd.bregen sd.G'

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
