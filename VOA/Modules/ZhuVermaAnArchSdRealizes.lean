/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdAssemble

/-!
# Track-B constructor — the bottom-survival `realizes` iso as the composite of its two honest pieces

`Modules.ZhuVermaAnArchSdAssemble` proved `bijection_of_sdAssemble`, the faithful Zhu-5.3.4 bijection
`Function.Bijective (forwardMapIrr W)`, taking six explicit hypotheses of which one is

  `realizes : ∀ U : AMod W,
    AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod U`

— the **bottom survival** `L(U)_h ≅ U` (DLM/Li Prop 3.2.9, Gannon Thm 5.3.4).  This file records the
honest structure of that leaf: it is *not* a single monolithic residue but the `AModEquiv.trans` of
exactly two `A(𝒱)`-module pieces, both of which live in every existing universal bundle
(`ZhuVermaAnArchLightPrimitives`, `…LighterFinest`, `…UniversalClose2`) as carried fields:

* the **survival piece** `surv U : L(U).toAMod ≅ M(U).toAMod` — the quotient bottom equals the module
  bottom because the maximal `J = supBotTrivialGraded` is bottom-disjoint
  (`J ⊓ M(U)_h = ⊥`, the `bregen`-sourced `bottom_disjoint`); this is the field `bottomQuot` of
  `MURepFamily.LightData`;
* the **R0 piece** `r0 U : M(U).toAMod ≅ U` — the balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`
  (`MUConstruct.bottomBalancedEquiv`) lifted to the `A(𝒱)`-action by the bottom zero-mode
  equivariance; this is the field `mudataBottomIso` of `MURepFamily.LightData`.

`realizes U = (surv U).trans (r0 U)` — precisely how `MURepFamily.UniversalClose2.toUniversalClose`
builds its `bottomIso` (its `bottomIso` "is itself the `AModEquiv.trans` of the two finer pieces",
`ZhuVermaAnArchLightPrimitives`).  So the single carried leaf `realizes` reduces, **as a term**, to
the two honest sub-pieces `surv`/`r0`.

## What is a TERM here

* **`sdRealizes G bregen surv r0`** — the `realizes` field of `bijection_of_sdAssemble`, produced from
  `surv`/`r0` by `AModEquiv.trans`.  No `sorry`, **never** an axiom.
* **`bijection_of_sdRealizes`** — the faithful Zhu-5.3.4 bijection with `realizes` discharged to the
  two honest pieces (feeds `sdRealizes` into `bijection_of_sdAssemble`).

## What is CARRIED (the two honest sub-pieces of `realizes`)

* **`surv`** — the per-`U` survival iso `L(U).toAMod ≅ M(U).toAMod` (`bottomQuot`; the deep content
  is the bottom-disjointness of the maximal `J`, from `bregen`).
* **`r0`** — the per-`U` R0 iso `M(U).toAMod ≅ U` (`mudataBottomIso`; R0 balanced bottom + bottom
  zero-mode equivariance).

Both are genuinely-open leaves in the existing architecture (never raw terms); we carry them
precisely and reduce `realizes` to their composite.  The remaining bijection inputs
(`hslice`, `G` — carrying `MUGradedAction`, `bregen`, `Dfun`, `G'`) are threaded unchanged.

## References
Dong–Li–Mason J. Algebra 206 (1998), Prop 3.2.9; Dong–Jiang Math. Z. 259 (2008); Frenkel–Zhu;
Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchLightPrimitives` (`bottomQuot`, `mudataBottomIso`,
`toUniversalClose` `bottomIso = AModEquiv.trans`), `ZhuVermaAnArchMUConstruct`
(`bottomBalancedEquiv`, R0); `ZhuVermaAnArchSdAssemble` (`sdLudata`, `bijection_of_sdAssemble`);
`ZhuBijection` (`AModEquiv.trans`).
-/

set_option linter.style.longLine false

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## `realizes` as the `AModEquiv.trans` of its two honest pieces -/

/-- **`sdRealizes` — the bottom-survival iso `L(U).toAMod ≅ U` as a TERM off its two honest pieces.**

The `realizes` clause that `bijection_of_sdAssemble` consumes is the composite

  `L(U).toAMod  ≅[surv U]  M(U).toAMod  ≅[r0 U]  U`,

exactly the `bottomIso = AModEquiv.trans (bottomQuot) (mudataBottomIso)` of
`MURepFamily.UniversalClose2.toUniversalClose`.  Here

* `surv U : AModEquiv W ((…toLUFamily (sdLudata G bregen)).K U).toAMod
    ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod`
  is the survival piece (the quotient by the bottom-disjoint maximal `J` retains the bottom), and
* `r0 U : AModEquiv W ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod U`
  is the R0 balanced-bottom piece.

`sdRealizes` is their `AModEquiv.trans` — a genuine term, no `sorry`, **never** an axiom. -/
noncomputable def sdRealizes (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G)
    (surv : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod)
    (r0 : ∀ U : AMod W,
      AModEquiv W ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod U) :
    ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod U :=
  fun U => AModEquiv.trans W (surv U) (r0 U)

end InducedAssignment

/-! ## The bijection with `realizes` discharged to the two honest pieces -/

/-- **`bijection_of_sdRealizes` — the faithful Zhu-5.3.4 bijection with `realizes` reduced to its two
honest pieces.**

`Function.Bijective (forwardMapIrr W)` from the keystone `hslice`, the genuine construction datum
`G` (carrying `MUGradedAction`), the maximal-`J` residue `bregen`, the functoriality datum `Dfun`,
the generation-from-bottom family `G'`, and — in place of the single opaque bottom-survival leaf
`realizes` — its two honest sub-pieces `surv` (survival `L(U)_h ≅ M(U)_h`) and `r0` (R0 balanced
bottom `M(U)_h ≅ U`).  Feeds `InducedAssignment.sdRealizes G bregen surv r0` as the `realizes` of
`bijection_of_sdAssemble`.  No `sorry`, **never** an axiom. -/
theorem bijection_of_sdRealizes {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (surv : ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily
        (InducedAssignment.sdLudata G bregen)).K U).toAMod
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod)
    (r0 : ∀ U : AMod W,
      AModEquiv W ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((G.toBimodGenuineConstructionA).toLUFamily (InducedAssignment.sdLudata G bregen)))
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_sdAssemble hslice G bregen
    (InducedAssignment.sdRealizes G bregen surv r0) Dfun G'

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
