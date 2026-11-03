/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuModularityGN
import VOA.Modularity.SqSlashBridge

/-!
# Zhu's modularity theorem with `hgr`, `hslash` and `hreal` all composed in — and the
conclusion **pinned** to the given family

Three residuals are theorems and are composed here:

* `hgr` — `Modularity.BlockGrowth.onePointSubexp_of_c2`;
* `hslash` — `Modularity.SqSlashBridge.traceBlock_S_sqRestrict_mem_analyticBlocks`;
* `hreal` — `Modularity.ZhuModularityGN.simpleAModsRealized_of_strictSpanning`, from the single
  datum `StrictSpanning W` (Gaberdiel–Neitzke Prop. 8).

⚠ **The conclusion is pinned.**  `∃ D : ModularData W ι, ZhuModularityAnalytic D` does *not* say
that `D` is the modular datum of the given `Mfam`/`h` — and `ZhuModularityAnalytic` reads its whole
content off `D.Mfam` and `D.h`.  Fewer hypotheses is only progress if the conclusion holds fixed, so
every statement here carries `D.Mfam = Mfam ∧ D.h = h`.

## What the main theorem still carries

`VacuumGradeZero`, `C2Cofinite`, `IsSemisimpleRing (A 𝒱)` (rationality), `Finite (Φ 𝒱)`, `hcard`,
`hcw`, `hsimp`, `hsep` — the legitimate hypotheses of Zhu's theorem — plus the PBW datum `Pr` and
`StrictSpanning W` (residual **(b)**, i.e. GN Prop. 8).

## Main results

* `zhuModularity_pinned_of_strictSpanning`;
* `zhuModularity_pinned_of_real` — the same with `hreal` carried directly.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Pinned Zhu modularity, carrying `hreal` directly.**  `hgr` and `hslash` are composed in;
the modular datum returned is the one of the given `Mfam`/`h`.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem zhuModularity_pinned_of_real [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ZhuModularityAnalytic D :=
  ⟨_, rfl, rfl,
    zhu_modularity_of_bottomSeparation Mfam h hC2 hss hreal Pr hcard hcw
      (fun i => onePointSubexp_of_c2 W (Mfam i).isMod (hcw i) (vacuumGradeZero_holds W) hC2) hsep
      (traceBlock_S_sqRestrict_mem_analyticBlocks Mfam h hcw (vacuumGradeZero_holds W) hC2)⟩

/-- **Pinned Zhu modularity from Gaberdiel–Neitzke Prop. 8.**  Residuals (c) and (e1) are absent,
and (b) appears only as the datum `StrictSpanning W`.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem zhuModularity_pinned_of_strictSpanning [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (d : StrictSpanning W)
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ZhuModularityAnalytic D :=
  zhuModularity_pinned_of_real Mfam h hC2 hss
    (simpleAModsRealized_of_strictSpanning hC2 Pr d) Pr hcard hcw hsep

end

end VOA
