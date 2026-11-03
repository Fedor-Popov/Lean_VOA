/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuCount
import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modularity.SimpleAModFinite

/-!
# The count with `FiniteDimensional ℂ (A 𝒱)` discharged

`Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite` proves `dim A(𝒱) < ∞` from
`C₂`-cofiniteness.  Every declaration in the count carries that as a named hypothesis; this file
removes it, leaving `C2Cofinite 𝒱` — which the modularity chain assumes everywhere anyway — in its
place.

## Main results

* `exists_injective_finrank_quot_commSpan_to_Φ_of_C2`;
* `finrank_quot_blockRelSpanAtCusp_le_card_Φ_of_C2` — Zhu Thm 5.3.3 at the cusp, with the
  hypothesis list reduced to `VacuumGradeZero`, `C2Cofinite`, `IsSemisimpleRing (A 𝒱)`,
  `SimpleAModsRealized 𝒱`, and the explicit `BottomProjection` assumption `Pr`.
* `finiteDimensional_of_isSimpleAMod_of_C2` — the free repair of the `SimpleAModsRealized`
  scoping, stated from `C₂`-cofiniteness directly.

## Status
Proof-term `#print axioms`-clean, no `sorry`, but conditional on the displayed inputs:
`IsSemisimpleRing (A 𝒱)` (Zhu's rationality), `SimpleAModsRealized 𝒱`, and the explicit
`BottomProjection` assumption `Pr`. The project-level `regularAMod` witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- Every simple bundled `A(𝒱)`-module of a `C₂`-cofinite VOA is finite-dimensional.  This is
the repair of the `SimpleAModsRealized` mis-scoping (`Modularity.SimpleAModFinite`), with the
hypothesis supplied by `C₂`-cofiniteness rather than carried. -/
theorem finiteDimensional_of_isSimpleAMod_of_C2 (hC2 : C2Cofinite W)
    (U : AMod W) (hU : IsSimpleAMod U) : FiniteDimensional ℂ U.carrier :=
  finiteDimensional_of_isSimpleAMod (finiteDimensional_A_of_C2Cofinite W hC2) U hU

/-- The Wedderburn factors inject into `Φ(𝒱)`, with `dim A(𝒱) < ∞` discharged. -/
theorem exists_injective_finrank_quot_commSpan_to_Φ_of_C2 (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    ∃ f : Fin (letI := instRingA W; letI := instAlgebraA W;
        Module.finrank ℂ (A W ⧸ commSpan ℂ (A W))) → Φ W,
      Function.Injective f :=
  exists_injective_finrank_quot_commSpan_to_Φ W (finiteDimensional_A_of_C2Cofinite W hC2) hss
    hreal Pr

/-- **Zhu's Theorem 5.3.3 at the cusp, from `C₂`-cofiniteness.**  No `VacuumGradeZero`
hypothesis: it holds for every VOA. -/
theorem finrank_quot_blockRelSpanAtCusp_le_card_Φ_of_C2 [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    Module.finrank ℂ (𝒱 ⧸ blockRelSpanAtCusp W) ≤ Nat.card (Φ W) :=
  finrank_quot_blockRelSpanAtCusp_le_card_Φ W (finiteDimensional_A_of_C2Cofinite W hC2)
    hss hreal Pr

end VOA
