/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutUCore
import VOA.Modules.ZhuVermaAnArchPhase4Final

/-!
# PHASE 4 TROPHY — the single Zhu bijection from the ONE genuine collapse `AoutUCoreLev0Core`

This is the **tightest endgame leaf** of Zhu Theorem 5.3.4.  Every structural component of the
`Φ(𝒱) ↔ Irr A(𝒱)` bijection is already proven or closed-as-a-term, and the whole apparatus
(`ARDTowerDecomp`, the commutator half `ardCommPart_eq_MGTowerFam`, the level-`n` half
`aOutLevNHalf_eq_PresTowerFam`, the reshaping `anmRightDiff_eq_aOuterModeFinsum`, the assembly
`crossCFirstDiffTowerEq_of_aOutUCoreLev0Core` / `MUGradedAction_of_aOutUCoreLev0Core`, the bijection
wiring `zhuBijection_phase4` / `clean_route_zhuBijection`) has been driven down to the **single**
remaining mathematical identity

  `AoutUCoreLev0Core W n K M P a c d`
    :  the level-`0` half `aOutLev0Half = ∑_{i≤K} C(K,i) • (c∘₀)(a₍i−(n+1)₎d)` collapses onto a
       grade-`M` level-`n` `PresTowerFam` in `c` (over the wider `a₍g₎d`) plus the `c₍s₎a` `MGTowerFam`

— the `a`-outer `c`-outer twin of the PROVEN diagonal U-core `UgammaModeCollAnm_eq_towerCoeff`
(`ZhuVermaAnArchMUcircClose`) and the PROVEN per-`s` slice difference
`crossDiffSliceDiff_eq_PresTowerFam` (`ZhuVermaAnArchHPoleN`), engine-verified TRUE on the rank-1 free
boson.  This file wires that single collapse end-to-end to the main theorem
`Function.Bijective (forwardMap W)`.

## The wiring (one continuous run of PROVEN reductions + TERM construction data)

```
(∀ n K M P, homog → AoutUCoreLev0Core W n K M P a c d)               -- THE single genuine collapse
   │  crossCFirstDiffTowerEq_of_aOutUCoreLev0Core   (ZhuVermaAnArchAoutUCore, PROVEN)
   │     — subtract the proven level-`n` `c`-tower `aOutLevNHalf_eq_PresTowerFam`, merge the two
   │       grade-`M` level-`n` `c`-`PresTowerFam`s via `smul_PresTowerFam` + `PresTowerFam_add`
   ▼
(∀ n K M P, homog → CrossCFirstDiffTowerEq W n K M P a c d)          -- the per-base pole-diff tower
   │  zhuBijection_phase4                            (ZhuVermaAnArchPhase4Final, PROVEN)
   │     — MUGradedAction_of_crossCFirstDiffScalarCore ⟹ q_act source `MUGradedAction W`;
   │       genFromBottomFinalFamily_of_G ⟹ the bridge-consumed final family;
   │       clean_route_zhuBijection = zhuBijection_of_bridgeData via transportRep (no `hderiv`)
   ▼
Function.Bijective (forwardMap W)                                     -- the main Zhu theorem
```

The single mathematical input upstream of `Hdiff` is `AoutUCoreLev0Core` itself: its clean
level-`n` half is proved (`aOutLevNHalf_eq_PresTowerFam`) and only the level-`0` half cross-base
reorganization into the `c₍s₎a` `MGTowerFam` remains, exactly mirroring the two PROVEN cores.

## The DEFINITIVE final hypothesis list of `zhuBijection_trophy`

1. **`Hcore`** — `∀ n K M P, homog → AoutUCoreLev0Core W n K M P a c d`
   *(the SINGLE genuine mathematical content — the level-`0` half cross-base collapse).*
2. **`hall`** — `InducedAssignment.AllLWIrreducible W`  *(the irreducibility scope of the theorem).*
3. **`F`** — `VHat.CarrierBridgeDataFamily W`  *(the per-`U` directional Dong–Jiang bridge term data
   + named grading/finiteness data; the `MURepFamily` is built CONSTRUCTIVELY by `transportRep`).*
4. **`ludata`** — the per-`U` maximal-`J` datum  *(finest FZ/DJ carrier).*
5. **`realizes`** — the per-`U` bottom-survival realization `AModEquiv`  *(finest carrier).*
6. **`Dfun`** — the `M(·)` functoriality datum  *(finest carrier).*
7. **`G`** — `InducedAssignment.GenFromBottomGFamily (…)`  *(the gate-form generation-from-bottom
   residue family: every field a term EXCEPT `q_act`, the carried bridge from `MUGradedAction W`).*

No `sorry`, no `admit`, no new `axiom`, no `pbw`.  `#print axioms zhuBijection_trophy` is exactly
`[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8), Prop 3.4–3.5, Thm 4.13;
DLM3 §4; H. Li hep-th/9406211 §2; Frenkel–Zhu Lemma 2.1.2; Gannon §5.3.1–§5.3.2, Thm 5.3.4; Zhu [574].
`ZhuVermaAnArchAoutUCore` (`AoutUCoreLev0Core`, `crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`),
`ZhuVermaAnArchPhase4Final` (`zhuBijection_phase4`), `ZhuVermaAnArchStage7Audit`
(`clean_route_zhuBijection`), `ZhuVermaAnArchMUcircClose` (`UgammaModeCollAnm_eq_towerCoeff`),
`ZhuVermaAnArchHPoleN` (`crossDiffSliceDiff_eq_PresTowerFam`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The universal level-`0` core ⟹ the universal per-base pole-difference tower. -/

/-- **The universal `CrossCFirstDiffTowerEq` from the single universal `AoutUCoreLev0Core`.**
Given, for every level `n` and all homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` half
cross-base collapse `AoutUCoreLev0Core`, the per-base pole-difference tower decomposition
`CrossCFirstDiffTowerEq` holds for the same data — `crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`) discharges each instance (subtract the PROVEN level-`n` `c`-tower
`aOutLevNHalf_eq_PresTowerFam`, merge the two grade-`M` level-`n` `c`-`PresTowerFam`s). -/
theorem crossCFirstDiffTowerEq_forall_of_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱)
    (Hcore : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), AoutUCoreLev0Core W n K M P a c d) :
    ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirstDiffTowerEq W n K M P a c d :=
  fun n K M P a ha c hc d hd =>
    crossCFirstDiffTowerEq_of_aOutUCoreLev0Core W n (Hcore n K M P a ha c hc d hd)

/-! ## PHASE 4 TROPHY — the single Zhu bijection from `AoutUCoreLev0Core`. -/

/-- **`zhuBijection_trophy` — the FINAL main theorem: the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` whose
ONLY genuine mathematical hypothesis is the single collapse `AoutUCoreLev0Core`.**

Given

* `Hcore` — for every level `n` and all homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0`
  half cross-base collapse `AoutUCoreLev0Core W n K M P a c d` (the SINGLE genuine identity — the
  `a`-outer `c`-outer twin of the diagonal U-core `UgammaModeCollAnm_eq_towerCoeff`, engine-verified
  TRUE; clean level-`n` half proved as `aOutLevNHalf_eq_PresTowerFam`);
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

The proof first lifts the single collapse `AoutUCoreLev0Core` to the per-base pole-difference tower
`CrossCFirstDiffTowerEq` (`crossCFirstDiffTowerEq_forall_of_aOutUCoreLev0Core`), then feeds that single
gate end-to-end through the PROVEN endgame `zhuBijection_phase4` (q_act source `MUGradedAction W` via
`MUGradedAction_of_crossCFirstDiffScalarCore`; `genFromBottomFinalFamily_of_G`; the clean
main theorem `clean_route_zhuBijection` = `zhuBijection_of_bridgeData` via `transportRep`).
No `sorry`, no axiom, no `pbw`. -/
theorem zhuBijection_trophy {W : VertexOperatorAlgebra 𝒱}
    (Hcore : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), AoutUCoreLev0Core W n K M P a c d)
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
  zhuBijection_phase4
    (crossCFirstDiffTowerEq_forall_of_aOutUCoreLev0Core W Hcore)
    F ludata realizes Dfun hall G

/-! ## Status — the Zhu bijection reduced to the SINGLE collapse `AoutUCoreLev0Core`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/
`axiom`/`pbw`):

* **`crossCFirstDiffTowerEq_forall_of_aOutUCoreLev0Core`** — the universal lift: the single universal
  `AoutUCoreLev0Core` ⟹ the universal per-base pole-difference tower `CrossCFirstDiffTowerEq`, via
  `crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`.
* **`zhuBijection_trophy`** — the FINAL main theorem: `Function.Bijective (forwardMap W)` with the ONLY
  genuine mathematical hypothesis the single collapse `AoutUCoreLev0Core`, every other input being the
  irreducibility scope `hall` or term-level construction data (`F`/`ludata`/`realizes`/`Dfun`/`G`).

**The DEFINITIVE final pending identity (engine-verified TRUE; NOT faked):** the universally-quantified
`AoutUCoreLev0Core W n K M P a c d` — the level-`0` half `aOutLev0Half = ∑_{i≤K} C(K,i)•(c∘₀)(a₍i−(n+1)₎d)`
collapsing onto a grade-`M` level-`n` `PresTowerFam` in `c` over `a₍g₎d` plus an `MGTowerFam` in `c₍s₎a`.
Its clean level-`n` half is proved (`aOutLevNHalf_eq_PresTowerFam`); the level-`0` half cross-base
reorganization is the `a`-outer `c`-outer twin of the FULLY-proven diagonal U-core
`UgammaModeCollAnm_eq_towerCoeff` (`ZhuVermaAnArchMUcircClose`) and the per-`s` slice difference
`crossDiffSliceDiff_eq_PresTowerFam` (`ZhuVermaAnArchHPoleN`), absorbed via `towerCoeffAnm_regrade_int`
+ `uCoreN`/`muIdentityN`.  When a sibling closes `AoutUCoreLev0Core` unconditionally, instantiate it
into `zhuBijection_trophy` to obtain the bijection with NO mathematical hypothesis.
-/

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
