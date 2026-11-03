/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockGrowth
import VOA.Modularity.ZhuModularityODE

/-!
# Zhu's modularity theorem with `hgr` **discharged**

`Modularity.BlockGrowth.onePointSubexp_of_c2` proves the growth datum outright from
`C₂`-cofiniteness and a conformal weight.  Plugging it into
`Modularity.ZhuModularityFibre.zhu_modularity_of_bottomSeparation` removes residual **(c)** from the
main theorem entirely.

## What the main theorem still carries, after this file

* the standing carries `VacuumGradeZero W`, `C2Cofinite W`, `IsSemisimpleRing (A W)` (rationality),
  `Finite (Φ W)`, `hcard`, and the explicit `regularAMod` `BottomProjection` hypothesis `Pr`; its
  project-level witness is supplied by `voaPBWBottomProjection`, from the generic
  relative-induction field of the theorem `VOA.pbw : PBWPrinciple`;
* the `Mfam`-level facts `hcw`, `hsimp`, `hsep`;
* residual **(b)** as `hreal : SimpleAModsRealized W`;
* residual **(e1)** as `hslash`.

**Residual (c) does not appear.**

## Main result

* `exists_zhuModularity_of_c2` — an **unpinned existential**.

Conclusion-strength warning: its type is only `∃ D, ZhuModularityAnalytic D`; it does not state
that `D.Mfam = Mfam` and `D.h = h`. The proof chooses the expected family-specific modular data,
but consumers cannot recover that linkage from this conclusion. The pinned theorem is
`zhu_modularity_of_bottomSeparation`.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`, but conditional on the displayed
parameters, including the explicit `BottomProjection` assumption `Pr`. The project-level witness
is supplied separately as above.
-/

namespace VOA

open scoped BigOperators
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Unpinned modular-data existence, with residual (c) discharged.** The growth datum `hgr`
is supplied by `onePointSubexp_of_c2`, which needs only `C₂`-cofiniteness and the conformal
weights — both already carried. The conclusion does not pin the witness to the supplied
`Mfam`/`h`.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem exists_zhuModularity_of_c2 [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2)))
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  ⟨_, zhu_modularity_of_bottomSeparation Mfam h hC2 hss hreal Pr hcard hcw
    (fun i => onePointSubexp_of_c2 W (Mfam i).isMod (hcw i) (vacuumGradeZero_holds W) hC2)
    hsep hslash⟩

end

end VOA
