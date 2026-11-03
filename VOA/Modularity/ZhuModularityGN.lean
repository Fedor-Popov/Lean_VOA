/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.StrictSpanning
import VOA.Modularity.ZhuModularitySurface

/-!
# Residual **(b)** reduced to Gaberdiel–Neitzke **Proposition 8** alone

`Modularity.StrictSpanning.hcof_of_strictSpanning` is GN Theorem 11: strict-decrease spanning
gives `C_m`-cofiniteness for every `m`.  Feeding it into
`Modularity.RealizationCofinite.simpleAModsRealized_of_cofinite` discharges residual **(b)** from
the single datum `StrictSpanning W` — which is GN Prop. 8 verbatim.

## Main results

* `simpleAModsRealized_of_strictSpanning`;
* `exists_zhuModularity_of_strictSpanning` — an **unpinned existential**, carrying
  `StrictSpanning` (analytic residual **(b)**), `hslash` (analytic residual **(e1)**), and the
  standing assumptions including the explicit `regularAMod` `BottomProjection` parameter `Pr`.

Conclusion-strength warning: the existential theorem does not state that its witness's `Mfam` and
`h` fields equal the supplied family. Its proof uses that family, but the public conclusion is
strictly weaker than a pinned family-specific modularity theorem.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`, but conditional on the displayed
parameters. `StrictSpanning` is a **named datum** (GN Prop. 8). The project-level `regularAMod`
`BottomProjection` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open scoped BigOperators
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Residual (b) from GN Prop. 8.** -/
theorem simpleAModsRealized_of_strictSpanning (hC2 : C2Cofinite W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (d : StrictSpanning W) : SimpleAModsRealized W :=
  simpleAModsRealized_of_cofinite hC2 Pr (hcof_of_strictSpanning d)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Unpinned modular-data existence, carrying GN Prop. 8 and the `S`-slash as its two
analytic residuals, plus the standing hypotheses including `Pr`.** The conclusion does not pin its
witness to the supplied `Mfam`/`h`.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem exists_zhuModularity_of_strictSpanning [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (d : StrictSpanning W)
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2)))
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  exists_zhuModularity_of_cofinite Mfam h hC2 hss Pr (hcof_of_strictSpanning d)
    hcard hcw hsep hslash

end

end VOA
