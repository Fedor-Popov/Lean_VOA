/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OnePointODE
import VOA.Modularity.ZhuModularityFibre

/-!
# `hgr` reduced to the formal ODE

`Modularity.OnePointODE` proves `OnePointSubexp` from a monic formal ODE. This file plugs it into
`Modularity.ZhuModularityFibre.zhu_modularity_of_bottomSeparation`, so residual **(c)** appears as
the single replacement hypothesis `hode`; the standing carries, including `Pr`, remain.

After this the modularity theorem rests on: the standing carries (`VacuumGradeZero`, `C2Cofinite`,
`IsSemisimpleRing (A 𝒱)`, `SimpleAModsRealized 𝒱`, `Finite (Φ 𝒱)`, `hcard`, `Pr`), the `Mfam`-level
facts `hcw`/`hsimp`/`hsep`, residual **(c)** as `hode`, and residual **(e1)** as `hslash`.

## Main result

* `exists_zhuModularity_of_ode` — an **unpinned existential**.

Conclusion-strength warning: its type is only `∃ D, ZhuModularityAnalytic D`; it does not state
that `D.Mfam = Mfam` and `D.h = h`. The proof chooses the expected `modularDataOf Mfam h …`, but
that linkage is not recoverable from this theorem's conclusion. Use the pinned
`zhu_modularity_of_bottomSeparation` when the supplied family must remain visible.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`, but conditional on the standing
parameters, including the explicit `BottomProjection` assumption `Pr`. The project-level
`regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open scoped BigOperators
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Unpinned modular-data existence with `hgr` reduced to the formal ODE.** The conclusion
does not identify the witness's `Mfam` and `h` fields with the supplied arguments.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem exists_zhuModularity_of_ode [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hode : ∀ (i : ι) (v : 𝒱), ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧
      (∀ j, Subexponential (fun k => ‖g j k‖)) ∧
      ∀ n : ℕ,
        indicialP (h i - W.centralCharge / 24) s g n
            * torusOnePoint (Mfam i).isMod v (h i - W.centralCharge / 24 + (n : ℂ))
          = - ∑ m ∈ Finset.range n, ∑ j ∈ Finset.range s,
              g j (n - m) * (h i - W.centralCharge / 24 + (m : ℂ)) ^ j
                * torusOnePoint (Mfam i).isMod v (h i - W.centralCharge / 24 + (m : ℂ)))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2)))
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  ⟨_, zhu_modularity_of_bottomSeparation Mfam h hC2 hss hreal Pr hcard hcw
    (fun i => onePointSubexp_of_indicialODE (Mfam i).isMod _ (hode i)) hsep hslash⟩

end

end VOA
