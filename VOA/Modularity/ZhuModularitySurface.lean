/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuModularityC2
import VOA.Modularity.RealizationCofinite

/-!
# The exact remaining surface of Zhu's modularity theorem

`Modularity.ZhuModularityC2.exists_zhuModularity_of_c2` removed residual **(c)**.
`Modularity.RealizationCofinite.simpleAModsRealized_of_cofinite` reduces residual **(b)** to the
cofiniteness family `𝒱/C_{n+2}(𝒱)` finite-dimensional.  Substituting the latter into the former
displays the main theorem's surface in full.

## What is left, and only this

* `hcof` — `C₂`-cofinite ⟹ `C_m`-cofinite (Gaberdiel–Neitzke Prop. 8): **residual (b)**;
* `hslash` — the analytic representability of the `S`-slash: **residual (e1)**;

together with the carries `VacuumGradeZero`, `C2Cofinite`, `IsSemisimpleRing (A 𝒱)` (rationality),
`Finite (Φ 𝒱)`, `hcard`, the explicit `regularAMod` `BottomProjection` hypothesis `Pr`, and the
`Mfam`-level `hcw`/`hsimp`/`hsep`. The project-level witness for `Pr` is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.

## Main result

* `exists_zhuModularity_of_cofinite` — an **unpinned existential**.

Conclusion-strength warning: the theorem concludes only `∃ D, ZhuModularityAnalytic D`; it does
not expose `D.Mfam = Mfam` or `D.h = h`. Its proof passes the supplied family through the chain,
but the public proposition is strictly weaker than a family-pinned modularity result.

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

/-- **Unpinned modular-data existence, with (c) discharged and (b) reduced.** The two new analytic
residuals are `hcof` (Gaberdiel–Neitzke Prop. 8) and `hslash` (the `S`-slash). The theorem also
carries the standing assumptions, notably the explicit `BottomProjection` parameter `Pr`.
Its conclusion does not pin the witness to the supplied `Mfam`/`h`.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem exists_zhuModularity_of_cofinite [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcof : ∀ n : ℕ, ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱)
        = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-((n : ℤ) + 2)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2)))
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  exists_zhuModularity_of_c2 Mfam h hC2 hss
    (simpleAModsRealized_of_cofinite hC2 Pr hcof) Pr hcard hcw hsep hslash

end

end VOA
