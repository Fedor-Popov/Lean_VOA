/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuBlockCount
import VOA.Modularity.ConformalWeightChoice
import VOA.Modularity.FamilyIndexing

/-!
# Discharging `hrank` — Zhu's modularity theorem modulo `(e1)` alone

`Modularity.ZhuBlockCount` proves Zhu Thm 5.3.3, `dim 𝔅 ≤ #Φ(𝒱)`, for
`𝔅 = map restrictImGT (analyticBlocks 𝒱)`.  This file carries that bound across `sqRestrict` and
feeds it to `SlashAmbientObstruction.slashSpannedAtS_of_sqRank_le`.

**The key observation.**  `slashSpannedAtS_of_sqRank_le` takes an *arbitrary* ambient `𝔄`.  It
is normally instantiated at `sqAnalyticSlashAmbient = map sqRestrict (analyticBlocks) ⊔ span (range
of the S-slashes)`, whose rank is not bounded by `#ι`.  Instantiating it instead at the **first
summand alone**, `map sqRestrict (analyticBlocks 𝒱)`, makes the rank hypothesis a *theorem*
(`rank_map_sqRestrict_analyticBlocks_le`, off Zhu Thm 5.3.3) and leaves exactly one open
membership — residual **(e1)** — as the sole new input.

## The residual, stated exactly

  `hslash : ∀ i, sqRestrict 𝒱 (blockSlash 𝒱 S (traceBlock Mfam h i))
                   ∈ Submodule.map (sqRestrict 𝒱) (analyticBlocks 𝒱)`

⚠ **Why it is not free**: the graded
blocks *are* `SL₂(ℤ)`-stable (`isGradedBlock_blockSlash`), but `IsGradedBlock.negTwo` requires `a`
**bi**-homogeneous — `a ∈ W.grading ka` *and* `a ∈ sqWeightSpace K` — while `blockRelSpan`'s
generators and `vSqZ`'s very definition are indexed by the **round** weight `ka` alone.  `L[0]` does
not preserve `𝒱_{ka}` (it is `L(0)` plus strictly degree-lowering terms), so a round-homogeneous `a`
has no square-bracket-homogeneous refinement inside `𝒱_{ka}`, in **either** direction.  Both named
routes — an `IsGradedBlock → IsAnalyticBlock` bridge, and a graded-side descent for
`sqGradedAmbient` — hit this same wall.  `SqModeWeighted` (`GradedBlock.lean:126`) already
*presupposes* bi-homogeneous `a`, so it does not resolve it either.

## Main results

* `rank_map_sqRestrict_analyticBlocks_le` — `hrank` for the first summand;
* `zhu_modularity_of_slashRepresentable` — Zhu's law 5.3.18a for every `A ∈ SL₂(ℤ)` from
  `hgr`, `hfib` and the single membership `hslash`.

## Status
Proof-term `#print axioms`-clean, no `sorry`, but conditional on all displayed parameters. Besides
the explicit undischarged `hslash`, these include the `BottomProjection` assumption `Pr`. The
project-level `regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **`hrank`, for the analytic-block summand.**  `sqRestrict` factors through
`restrictImGT`, so Zhu Thm 5.3.3 transfers. -/
theorem rank_map_sqRestrict_analyticBlocks_le [Finite (Φ W)]
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W)) :
    Module.rank ℂ (Submodule.map (sqRestrict W) (analyticBlocks W))
      ≤ (Fintype.card ι : Cardinal) := by
  obtain ⟨hfd𝔅, hle𝔅⟩ :=
    finiteDimensional_and_finrank_analyticBlocks_le_card_Φ W hzero hC2 hss hreal Pr
  haveI := hfd𝔅
  have hmapeq : Submodule.map (sqRestrict W) (analyticBlocks W)
      = Submodule.map (sqPtEval W) (Submodule.map restrictImGT (analyticBlocks W)) := by
    rw [sqRestrict_eq_comp, Submodule.map_comp]
  haveI : FiniteDimensional ℂ (Submodule.map (sqRestrict W) (analyticBlocks W)) := by
    rw [hmapeq]; infer_instance
  have hstep : Module.finrank ℂ (Submodule.map (sqRestrict W) (analyticBlocks W))
      ≤ Nat.card (Φ W) := by
    rw [hmapeq]
    exact le_trans (Submodule.finrank_map_le (sqPtEval W) _) hle𝔅
  rw [← Module.finrank_eq_rank]
  exact_mod_cast le_trans hstep (le_of_eq hcard.symm)

/-- **Zhu's modularity theorem 5.3.8 (5.3.18a), for every `A ∈ SL₂(ℤ)`, from the single
membership `hslash`.**  Compared with
`Modularity.ConformalWeightChoice.zhu_modularity_of_sqAnalyticRank_le_irr`, the rank hypothesis
`hrank` is **discharged** (Zhu Thm 5.3.3) and replaced by residual **(e1)**. -/
theorem zhu_modularity_of_slashRepresentable [Finite (Φ W)]
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hfib : FibreIndependent Mfam h)
    (hslash : ∀ i, sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i))
      ∈ Submodule.map (sqRestrict W) (analyticBlocks W)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h
            (Submodule.map (sqRestrict W) (analyticBlocks W))
            (traceIndependent_of_fibreIndependent Mfam h hcw hfib)
            (fun i => ⟨traceBlock Mfam h i, traceBlock_isAnalyticBlock Mfam h hcw hgr i, rfl⟩)
            hslash
            (rank_map_sqRestrict_analyticBlocks_le (ι := ι) hzero hC2 hss hreal Pr hcard)))
        (traceIndependent_of_fibreIndependent Mfam h hcw hfib) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

end

end VOA
