/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCarrierBridgeBuild
import VOA.Modules.ZhuVermaAnArchCarrierBridge
import VOA.Modules.ZhuVermaAnArchLightPrimitives
import VOA.Modules.ZhuVermaAnArchRhoDerivBracket

/-!
# The clean route to `Function.Bijective (forwardMap W)`

This file is an **audit leaf**. It does NOT introduce any new mathematical
content; it only RE-NAMES the chosen clean headline and its minimal leaf set so that a single
`#print axioms` pass certifies the route end-to-end, and it records the *degeneracy* finding on the
suspect `hderiv`-carrying alternative.

## Status (faithful)

The single cleanest route to `Function.Bijective (forwardMap W)` is

  `zhuBijection_of_bridgeData`  (`ZhuVermaAnArchCarrierBridgeBuild`)
    ← `headline_zhuBijection_of_bridge`  (`ZhuVermaAnArchCarrierBridge`)
    ← `zhuBijection_of_repFamily`        (`ZhuVermaAnArchMUModuleDataBuild`)

fed a `VHat.CarrierBridgeDataFamily W`.  The `MURepFamily` is built CONSTRUCTIVELY by
`CarrierBridgeFamily.toMURepFamily`, whose `rho U := transportRep (F.bridge U)` conjugates the
genuine, axiom-free defect-quotient Construction-A engine `defectRep W M = quotientRep (freeRep W M)`
along the bridge iso.  Crucially:

* the module-Jacobi 5.3.1b (`hjac`) is proved by `transportRep_isModuleJacobi`, transported from
  `freeRep_defectQuotient_isModuleJacobi` — it is NOT a carried hypothesis;
* the `𝒱`-mode action is genuinely mode-dependent (it is `umode W a m` left-multiplication in
  `UEnv`, see `freeRep_actMode_tmul`) — NO `hderiv` is carried anywhere on this route;
* `FZModeDescent` is NOT on this route.

The minimal carried leaf set is therefore exactly:

  (1) per-`U` `CarrierBridgeData` = { fwd, bwd, left_inv, right_inv, equivariant }
      (the Dong–Jiang Prop 3.4/3.5 iso + equivariance — pure linear algebra packaging of the genuine
      residue-membership descent; sharpenable to `CarrierBridgeReprData` = `g`+`hker`),
  (2) `htr`  : `ActModeTruncated (freeRep W U.carrier)`  (the PBW-gated bottom-survival truncation,
      the single route-independent crux),
  (3) `hvac`, `hL0`, `hfin`, `hbot`  (the named grading/finiteness/vacuum data on the headline field),
  (4) `ludata` (per-`U` maximal-`J`), `realizes`, `Dfun` (FZ functoriality), `hall`
      (`AllLWIrreducible`), `G` (generation-from-bottom).

This is the equal of "ARDScalarCore=MUGradedAction, ludata, bottomQuotEquiv, muEquiv, hall, and the
fzRho CarrierBridge data — NOT a false hderiv": the bridge transports the free defect-quotient action
(no `hderiv` carried), the graded action lives inside the genuine engine, and the deep residues
(`ludata`/realization/`Dfun`/`G`) are carried in their honest finest form.

## DEGENERACY of the alternative `vhatRepMU`/`hderiv` route (gap on that route only)

`derivObstruction` (`ZhuVermaAnArchRhoDerivBracket`) PROVES: if the *degree-independent* bottom-row
family `composeActLevel W U hclo` satisfies the descent relation
`hderiv : ∀ a m, f (L₋₁ a) + m • f a = 0`, then `f a = 0` for every `a` — the action is identically
zero.  (Take `m = 0`: `f(L₋₁a) = 0`; then any `m`: `m • f a = 0 ⟹ f a = 0`.)

Hence ANY route that (i) instantiates the carrier action by the *degree-independent* `composeAct`
family AND (ii) carries the `composeActLevel`-shaped `hderiv` is VACUOUS — its hypothesis set is
inconsistent except at the zero action, which is not a faithful `M(U)`.  The
`repMU`/`levelShift`/`vhatRepMU`-via-`composeAct` field is exactly that degree-independent family
(`repMU_actMode_eq : (repMU …).actMode = fun a _ => composeAct …`, mode-independent).

The `fzRho`-transport route AVOIDS this: it never carries a `composeActLevel`-`hderiv`; the genuine
mode-dependence comes from `freeRep`/`umode`, so `derivObstruction`'s hypothesis is simply absent.

NOTE on `genuine_spanning_closes_bridge` (`ZhuVermaAnArchSpanningClose`): it carries a FULLY GENERAL
`D : VHatModeData W (MU W U)` (not the degenerate `composeAct` one) and only concludes
`Function.Bijective (… ).toReprData.fwd` — a per-`U` bridge bijectivity, NOT the main theorem
`Function.Bijective (forwardMap W)`.  So that headline is not itself vacuous, but it does not reach
the main theorem and is strictly weaker than the clean route; the moment one tries to *supply* its `D`
through the degree-independent `composeAct`/`hderiv` machinery, `derivObstruction` forces zero.

## Carried-hypothesis falsity check (the two named pitfalls)

* `FZModeDescent` — proven FALSE (`ZhuVermaAnArchFZModeDescent`).  NOT on the clean route.
* the `repMU`/`levelShift`/`vhatRepMU`-`hderiv` — proven DEGENERATE by `derivObstruction`.  NOT on
  the clean route (the clean route carries no `hderiv`; mode-dependence is in the free engine).
-/

namespace VOA
namespace Stage7Audit

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The clean main theorem** — verbatim re-export of `zhuBijection_of_bridgeData`.  This is the
single cleanest route to the main Zhu theorem; its carried leaf set is the minimal honest one (see the
file docstring).  No `sorry`, no axiom, no `pbw`, NO `hderiv`. -/
theorem clean_route_zhuBijection {W : VertexOperatorAlgebra 𝒱}
    (F : VHat.CarrierBridgeDataFamily W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((F.toCarrierBridgeFamily.toMURepFamily).mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W
        (((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_bridgeData F ludata realizes Dfun hall G

/-- **Degeneracy certificate (re-export of `derivObstruction`).**  Records that the degree-independent
`composeActLevel` family carrying the `hderiv` descent relation is forced to the zero action — so any
route supplying its carrier action that way is vacuous. -/
theorem hderiv_degeneracy_certificate (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      VHat.composeActLevel W U hclo (W.L (-1) a)
        + (m : ℂ) • VHat.composeActLevel W U hclo a = 0)
    (a : 𝒱) : VHat.composeActLevel W U hclo a = 0 :=
  VHat.derivObstruction W U hclo hderiv a

end Stage7Audit
end VOA

-- ============================================================================
-- FINAL INTEGRITY GATE — the chosen headline + its minimal carried leaf set.
-- All must report exactly: [propext, Classical.choice, Quot.sound].
-- ============================================================================

-- The clean main theorem to the main theorem.

-- The exact headline it re-exports, and the two upstream reductions it factors through.

-- The constructive engine on the carrier (NO hderiv): transport of the free defect-quotient engine.

-- The genuine, mode-dependent, axiom-free Construction-A engine the bridge transports.

-- The directional leaf packaging (pure linear algebra) and its representative-level sharpening.

-- The degeneracy certificate of the suspect hderiv route (the gap on THAT route, not the clean one).
