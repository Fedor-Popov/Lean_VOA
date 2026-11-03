/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.FibreIndependence
import VOA.Modularity.SqAmbientRank
import VOA.Modules.ZhuBottomSimple

/-!
# Discharging `hfib` — Zhu's modularity theorem from bottom separation

`Modularity.FibreIndependence.fibreIndependent_of_bottomSeparation` proves residual **(d)**.  This
file feeds it to `Modularity.SqAmbientRank.zhu_modularity_of_slashRepresentable`, whose `hfib`
hypothesis is thereby **discharged**.

After this, Zhu's law 5.3.18a for every `A ∈ SL₂(ℤ)` rests on:

* the standing carries `VacuumGradeZero`, `C2Cofinite`, `IsSemisimpleRing (A 𝒱)`,
  `SimpleAModsRealized 𝒱`, `Finite (Φ 𝒱)`, `hcard`, and the explicit `BottomProjection`
  assumption `Pr`;
* `hcw` (dischargeable by `Modularity.ConformalWeightChoice.conformalWeightOf`);
* `hgr` — residual **(c)**;
* `hsimp` / `hsep` — the bottom-separation data, which are *`Mfam`-level* facts, not gates:
  simplicity of the bottoms and their pairwise non-isomorphy at equal conformal weight;
* `hslash` — residual **(e1)**.

## Main result

* `zhu_modularity_of_bottomSeparation`.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`, but conditional on the displayed
parameters, including `Pr`. The project-level `regularAMod` witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Bottom simplicity is automatic under semisimplicity.**  If `A(𝒱)` is semisimple, then for
any family of irreducible modules with conformal weights, every bottom `Ω(M_j)` is a simple
`A(𝒱)`-module (`isSimpleAMod_of_irreducible_of_semisimple`, given `Pr`).  This discharges a
bottom-simplicity hypothesis `hsimp` in the Zhu modularity theorems. -/
theorem isSimpleAMod_lowestAMod_of_semisimple {ι : Type*} (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    ∀ j, IsSimpleAMod (lowestAMod (hcw j).2) := by
  intro j
  let P : LWModule W :=
    { carrier := (Mfam j).carrier
      isMod := (Mfam j).isMod
      h := h j
      isLow := (hcw j).2
      realized := (hcw j).1 }
  exact isSimpleAMod_of_irreducible_of_semisimple Pr hss P (Mfam j).irreducible

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Zhu's modularity theorem 5.3.8 (5.3.18a), with `hfib` discharged.**  Compared with
`Modularity.SqAmbientRank.zhu_modularity_of_slashRepresentable`, the independence hypothesis is
replaced by the bottom-separation data `hsep` (with bottom simplicity derived from `hss`, `Pr`),
from which `Modularity.FibreIndependence` derives it.

No `VacuumGradeZero` or bottom-simplicity hypothesis: `𝒱₀ = ℂ𝟙` holds for every VOA
(`vacuumGradeZero_holds`), and simplicity of the bottoms follows from `hss` and `Pr`
(`isSimpleAMod_lowestAMod_of_semisimple`), so neither is a hypothesis here. -/
theorem zhu_modularity_of_bottomSeparation [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2)))
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h
            (Submodule.map (sqRestrict W) (analyticBlocks W))
            (traceIndependent_of_fibreIndependent Mfam h hcw
              (fibreIndependent_of_bottomSeparation Mfam h hcw hgr
                (isSimpleAMod_lowestAMod_of_semisimple Mfam h Pr hss hcw) hsep))
            (fun i => ⟨traceBlock Mfam h i, traceBlock_isAnalyticBlock Mfam h hcw hgr i, rfl⟩)
            hslash
            (rank_map_sqRestrict_analyticBlocks_le (ι := ι) (vacuumGradeZero_holds W) hC2 hss hreal
              Pr hcard)))
        (traceIndependent_of_fibreIndependent Mfam h hcw
          (fibreIndependent_of_bottomSeparation Mfam h hcw hgr
            (isSimpleAMod_lowestAMod_of_semisimple Mfam h Pr hss hcw) hsep)) hcw) :=
  zhu_modularity_of_slashRepresentable Mfam h (vacuumGradeZero_holds W) hC2 hss hreal Pr hcard
    hcw hgr (fibreIndependent_of_bottomSeparation Mfam h hcw hgr
      (isSimpleAMod_lowestAMod_of_semisimple Mfam h Pr hss hcw) hsep) hslash

end

end VOA
