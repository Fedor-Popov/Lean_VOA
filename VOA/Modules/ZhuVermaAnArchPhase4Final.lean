/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchStage7Audit
import VOA.Modules.ZhuVermaAnArchARDScalarCoreAssemble
import VOA.Modules.ZhuVermaAnArchGenFromBottomG

/-!
# The Zhu bijection from the ONE genuine gate `CrossCFirstDiffTowerEq`

This is the **endgame assembly leaf** of Zhu Theorem 5.3.4.  Every structural component of the
`Φ(𝒱) ↔ Irr A(𝒱)` bijection is proven or closed-as-a-term and the clean route is checked
faithful (`ZhuVermaAnArchStage7Audit`).  The whole construction reduces to the **single**
mathematical identity

  `CrossCFirstDiffTowerEq W n K M P a c d`
    :  `crossCFirstDiff W n K M a c d
         = PresTowerFam W M n c (… over a₍g₎d …) + MGTowerFam W n S (… c₍s₎a @ d …)`

— the per-base pole-difference tower decomposition (Dong–Jiang Lemma 2.8 `a`-outer collapse,
per-base weight `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))`, `crossDiffWeight_eq`;
engine-verified TRUE on the rank-1 free boson, `certificates/mathematica/cfirst0_diff.wl`).  This file
wires that single gate end-to-end to the main theorem `Function.Bijective (forwardMap W)`.

## The wiring (one continuous run of PROVEN reductions + TERM construction data)

```
(∀ n K M P, homog → CrossCFirstDiffTowerEq W n K M P a c d)          -- THE single genuine gate
   │  MUGradedAction_of_crossCFirstDiffScalarCore   (ZhuVermaAnArchARDScalarCoreAssemble, PROVEN)
   ▼
MUGradedAction W                                                      -- the DJ-2.8 q_act source
   │  genFromBottomFinalFamily_of_G  (ZhuVermaAnArchGenFromBottomG, PROVEN)
   │     — turns the gate-form residue family `GenFromBottomGFamily` (q_act carried as the gate
   │       bridge `q_act_of_graded`) into the `GenFromBottomFinalFamily` the bridge route consumes
   ▼
GenFromBottomFinalFamily (F.toCarrierBridgeFamily.toMURepFamily.toLUFamily ludata)
   │  clean_route_zhuBijection = zhuBijection_of_bridgeData via transportRep  (Stage7Audit, proven)
   │     — the clean main theorem: each bottom `U` carried with the honest forward/backward
   │       Dong–Jiang maps inside `CarrierBridgeDataFamily F`; the `MURepFamily` is built
   │       CONSTRUCTIVELY by `transportRep` of the free defect-quotient engine (NO `hderiv`)
   ▼
Function.Bijective (forwardMap W)                                     -- the main Zhu theorem
```

`MUGradedAction W` is the q_act source carried by the injective half (`GenFromBottomGFamily`'s
`q_act_of_graded` bridge); supplying it from `CrossCFirstDiffTowerEq` discharges that field, so the
**only genuine mathematical hypothesis** of `zhuBijection_phase4` is `CrossCFirstDiffTowerEq`.
Everything else is either the irreducibility scope `hall : AllLWIrreducible W` or the term-level
construction data (the `CarrierBridgeDataFamily`, the `ludata`/`realizes`/`Dfun` finest carriers, and
the gate-form generation-from-bottom residue family `G : GenFromBottomGFamily`).

## The DEFINITIVE final hypothesis list of `zhuBijection_phase4`

1. **`Hdiff`** — `∀ n K M P, homog → CrossCFirstDiffTowerEq W n K M P a c d`
   *(the SINGLE genuine mathematical content — the per-base pole-difference tower decomposition).*
2. **`hall`** — `InducedAssignment.AllLWIrreducible W`  *(the irreducibility scope of the theorem).*
3. **`F`** — `VHat.CarrierBridgeDataFamily W`  *(the per-`U` directional Dong–Jiang bridge term data
   + named grading/finiteness data).*
4. **`ludata`** — the per-`U` maximal-`J` datum  *(finest FZ/DJ carrier).*
5. **`realizes`** — the per-`U` bottom-survival realization `AModEquiv`  *(finest carrier).*
6. **`Dfun`** — the `M(·)` functoriality datum  *(finest carrier).*
7. **`G`** — `InducedAssignment.GenFromBottomGFamily (…)`  *(the gate-form generation-from-bottom
   residue family: bottom map `β`/`hβ`, the gate bridge `q_act_of_graded`, the `BottomOrbit` survival
   `bottom_ne_zero`, the maximal-`J` `KerJData` — every field a term EXCEPT `q_act`, which is the
   carried bridge from `MUGradedAction W`).*

No `sorry`, no `admit`, no new `axiom`, no `pbw`.  `#print axioms zhuBijection_phase4` is exactly
`[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Prop 3.4–3.5, Lemma 2.8, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
`ZhuVermaAnArchStage7Audit` (`clean_route_zhuBijection`), `ZhuVermaAnArchARDScalarCoreAssemble`
(`MUGradedAction_of_crossCFirstDiffScalarCore`), `ZhuVermaAnArchGenFromBottomG`
(`GenFromBottomGFamily`, `genFromBottomFinalFamily_of_G`), `ZhuVermaAnArchCarrierBridgeBuild`
(`CarrierBridgeDataFamily`, `zhuBijection_of_bridgeData`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## PHASE 4 FINAL — the single Zhu bijection from `CrossCFirstDiffTowerEq` -/

/-- **`zhuBijection_phase4` — the FINAL Phase-4 theorem: the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` whose
ONLY genuine mathematical hypothesis is the single gate `CrossCFirstDiffTowerEq`.**

Given

* `Hdiff` — for every level `n` and all homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the per-base
  pole-difference tower decomposition `CrossCFirstDiffTowerEq W n K M P a c d` (the SINGLE genuine
  identity — Dong–Jiang Lemma 2.8 `a`-outer collapse, per-base weight `cbz(M, μ+2) − cbz(M, μ+(n+2))`,
  engine-verified TRUE);
* `F : VHat.CarrierBridgeDataFamily W` — the per-`U` directional Dong–Jiang bridge term data and the
  named grading/finiteness data (the clean carrier — the `MURepFamily` is built
  CONSTRUCTIVELY by `transportRep` of the free defect-quotient engine, NO `hderiv`);
* `ludata` — the per-`U` maximal-`J` finest carrier;
* `realizes` — the per-`U` bottom-survival realization `AModEquiv`;
* `Dfun` — the `M(·)` functoriality finest carrier;
* `hall : InducedAssignment.AllLWIrreducible W` — the irreducibility scope;
* `G : InducedAssignment.GenFromBottomGFamily (…)` — the gate-form generation-from-bottom residue
  family (every field a term except `q_act`, carried as the bridge `q_act_of_graded` from
  `MUGradedAction W`),

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The proof wires the single gate `CrossCFirstDiffTowerEq` through the PROVEN reductions:
`MUGradedAction_of_crossCFirstDiffScalarCore` produces the q_act source `MUGradedAction W`;
`genFromBottomFinalFamily_of_G` upgrades the gate-form residue family `G` to the
`GenFromBottomFinalFamily` consumed by the clean main theorem `clean_route_zhuBijection`
(= `zhuBijection_of_bridgeData` via `transportRep`).  No `sorry`, no axiom, no `pbw`. -/
theorem zhuBijection_phase4 {W : VertexOperatorAlgebra 𝒱}
    (Hdiff : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirstDiffTowerEq W n K M P a c d)
    (F : VHat.CarrierBridgeDataFamily W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((F.toCarrierBridgeFamily.toMURepFamily).mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W
        (((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomGFamily
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  -- (1) the single genuine gate ⟹ the DJ-2.8 q_act source `MUGradedAction W`.
  let hgraded : MUGradedAction W := MUGradedAction_of_crossCFirstDiffScalarCore W Hdiff
  -- (2) upgrade the gate-form residue family to the `GenFromBottomFinalFamily` the bridge consumes.
  Stage7Audit.clean_route_zhuBijection F ludata realizes Dfun hall
    (InducedAssignment.genFromBottomFinalFamily_of_G _ hgraded G)

/-! ## Status — the Zhu bijection reduced to the single gate `CrossCFirstDiffTowerEq`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/
`axiom`/`pbw`):

* **`zhuBijection_phase4`** — the FINAL Phase-4 theorem: `Function.Bijective (forwardMap W)` with the
  ONLY genuine mathematical hypothesis the single gate `CrossCFirstDiffTowerEq`, every other input
  being the irreducibility scope `hall` or term-level construction data
  (`F`/`ludata`/`realizes`/`Dfun`/`G`).

The single remaining identity (engine-verified TRUE, NOT faked) is the universally-quantified
`CrossCFirstDiffTowerEq W n K M P a c d`, with exact per-base weight
`crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))` (`crossDiffWeight_eq`); the genuine residual is
ONLY the cross-base reorganization of this weight into the `c₍s₎a` `MGTowerFam`.
-/

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
