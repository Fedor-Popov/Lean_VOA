/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCrossCircConditional
import VOA.Modules.ZhuVermaAnArchSdAssemble
import VOA.Modules.ZhuVermaAnArchSdNoDfun
import VOA.Modules.ZhuVermaAnArchSdSurv
import VOA.Modules.ZhuVermaAnArchCrossCircReduce

/-!
# Zhu-5.3.4 from `CrossCircCore` with `A`/`hirr` (and `graded`, `hslice`) all discharged.

This combines the two conditional-bijection scaffolds:

* `zhu534_of_crossCircCore_peelGraded` (`ZhuVermaAnArchCrossCircConditional`): the single Half-A residue
  `(∀n, CrossCircCore W n)` discharges BOTH the keystone `hslice : NeededSliceMems W`
  (`neededSliceMems_of_crossCirc`) AND the construction field `graded : MUGradedAction W`
  (`mUGradedAction_of_crossCircCore`, via `GAUniformNoGraded.toFull`);
* `bijection_of_sdAssemble` (`ZhuVermaAnArchSdAssemble`): the lifting datum `A : InducedAssignment W`
  and its irreducibility `hirr : A.RealizeIrreducible` are discharged as terms (`sdA`/`sdHirr`,
  `sdHirr` being the unconditional `realizeIrreducible_of_canonical`), leaving the `M(·)`-functoriality
  `Dfun` and the bottom-survival isos `realizes` as the carried lifting inputs.

The result, `zhu534_of_crossCircCore_sdAssemble`, discharges **six** things — `hslice`, `graded`, `A`,
`hirr`, the `M(·)`-functoriality `Dfun` (via `sdDfun`), and the bottom-survival piece `surv` of
`realizes` (via `survOfRegen`, `bijection_of_sdSurv`) — from the single Half-A residue
`(∀n, CrossCircCore W n)` plus the construction data, so the whole Zhu-5.3.4 bijection
`Function.Bijective (forwardMapIrr W)` rests on `CrossCircCore` plus exactly the genuine
Frenkel–Zhu/DLM generalized-Verma leaves

  `G0` (the twelve non-`graded` Construction-A fields), `bregen`, `r0` (the R0 balanced-bottom
  `M(U)_h ≅ U`), `G'`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free; no `sorry`/`admit`/`axiom`; no
existing file mutated.  The bijection row is **not** flipped (these leaves are genuine carried
construction data).

## References
`ZhuVermaAnArchCrossCircConditional` (`GAUniformNoGraded.toFull`, `hcross_of_crossCircCore`),
`ZhuVermaAnArchSdAssemble` (`sdA`/`sdHirr`/`bijection_of_sdAssemble`), `ZhuVermaAnArchCrossCircReduce`
(`neededSliceMems_of_crossCirc`); Dong–Jiang math/0601626 §3–4; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`zhu534_of_crossCircCore_sdAssemble` — the Zhu-5.3.4 bijection with `hslice`, `graded`, `A`,
`hirr`, `Dfun`, AND the bottom-survival piece `surv` all discharged from the single Half-A residue
`(∀n, CrossCircCore W n)`.**

`hslice`/`graded` come from `CrossCircCore` (via `neededSliceMems_of_crossCirc`,
`GAUniformNoGraded.toFull`); `A`/`hirr` are the discharged `sdA`/`sdHirr` terms; the functoriality
`Dfun` is the discharged `sdDfun` term (DJ Prop 3.4 + 3.5); and the bottom-survival piece `surv` of
`realizes` is the discharged `survOfRegen` term (via `bijection_of_sdSurv`).  The carried Half-B leaves
are the twelve non-`graded` fields `G0`, the maximal-`J` regeneration `bregen`, the R0 balanced-bottom
`AModEquiv` `r0 : M(U)_h ≅ U`, and the generation-from-bottom lift `G'`.

⚠ **This RE-EXPRESSES, it does not reduce, the deep content** (adversarially-verified Half-B field map):
* `r0 : M(U)_h ≅ U` is on the ℂ-tensor bottom `mudata U = A₀₀(𝒱) ⊗_ℂ U`, which is STRICTLY LARGER than
  `U` for `dim A(𝒱) > 1` — so `r0` is the **balanced-bottom keystone**, provably FALSE on the current carrier
  (`qInjOnBottom_false_of_balancing_ne_bot`, `ZhuVermaAnArchSdBalancedBottom`).  It becomes a term only
  after the balanced-bottom re-grafting `A₀₀ ⊗_{A(𝒱)} U ≅ U` (`bottomBalancedEquiv`/`muBalBottomEquivA`).
* `G0 : GAUniformNoGraded W` is itself deep and NOT instantiable non-degenerately on the
  `levelShiftActGen` carrier (`hderiv` forces the zero action on shifted layers, contradicting
  `hvac`+`hbot`; `ZhuVermaAnArchRhoRelations`/`RhoDerivBracket`/`SdGvac`).  The structural fix is
  re-basing the action onto `fzRhoMU` (`zhuBijection_fzRoute`, `ZhuVermaAnArchRhoFZMURoute`), where
  `hderiv`/`hbracket`/`htr`/`hmi` become terms.
So this term makes `A`/`hirr`/`Dfun`/`surv` canonical and surfaces `r0` explicitly, but the honest
minimal residual is NOT just `bregen`: it is `CrossCircCore` + the balanced-bottom surgery + `LevelReach`
+ `q_act_of_graded` + the `hL/hR` (n≥1) descents + the `G0` carrier re-base + the `hpieces/hnt` finiteness. -/
theorem zhu534_of_crossCircCore_sdAssemble (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n)
    (G0 : GAUniformNoGraded W)
    (bregen : InducedAssignment.BottomRegenData (G0.toFull hcore))
    (r0 : ∀ U : AMod W,
      AModEquiv W (((G0.toFull hcore).toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod U)
    (G' : InducedAssignment.GenFromBottomGFamily
      ((G0.toFull hcore).toLUFamily
        (fun U => (InducedAssignment.lumaxOfRegen (G0.toFull hcore) bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_sdSurv
    (neededSliceMems_of_crossCirc W (hcross_of_crossCircCore W hcore))
    (G0.toFull hcore) bregen r0
    (InducedAssignment.sdDfun (G0.toFull hcore) bregen) G'

end VOA

-- Integrity gate (axiom-clean: [propext, Classical.choice, Quot.sound]; NO sorryAx/pbw).
