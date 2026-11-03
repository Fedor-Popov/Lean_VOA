/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqGradedBlockSlash
import VOA.Modularity.ZhuModularityC2

/-!
# The source-correct slash discharges residual (e1)

The globally linear square-weight slash is an analytic block. On square-homogeneous points it is
the same fixed-weight slash as the pointwise `blockSlash`, so their `sqRestrict`s agree.
Consequently
the slash membership itself is unconditional. The downstream modularity theorem still carries the
explicit `BottomProjection` assumption `Pr`. Its project-level `regularAMod` witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open VHat VHat.DLM3 Module
open scoped MatrixGroups

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The corrected linear slash and the pointwise slash agree after restriction to
square-homogeneous inputs and the upper half-plane. -/
theorem sqRestrict_sqBlockSlash_eq_blockSlash {F : V → ℂ → ℂ}
    (hF : IsSqGradedBlock W F) (gamma : SL(2, ℤ)) :
    sqRestrict W (sqBlockSlash W hF gamma) = sqRestrict W (blockSlash W gamma F) := by
  funext p z
  by_cases hz : z ∈ imGT 0
  · rw [sqRestrict_apply W _ p hz, sqRestrict_apply W _ p hz]
    exact ((isSlashOf_sqBlockSlash W hF gamma) p.1 (p.2 : V) p.2.property z hz).trans
      ((isSlashOf_blockSlash W gamma (fun z _ ↦ hF.zerov z))
        p.1 (p.2 : V) p.2.property z hz).symm
  · change Set.indicator (imGT 0) _ z = Set.indicator (imGT 0) _ z
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-- The pointwise slash restricted to square-homogeneous inputs is represented by an
honest analytic block: the source-correct globally linear slash. -/
theorem sqRestrict_blockSlash_mem_analyticBlocks {F : V → ℂ → ℂ}
    (hF : IsAnalyticBlock W F) (gamma : SL(2, ℤ)) :
    sqRestrict W (blockSlash W gamma F) ∈
      Submodule.map (sqRestrict W) (analyticBlocks W) := by
  let hSq : IsSqGradedBlock W F := hF.toSqGradedBlock
  refine ⟨sqBlockSlash W hSq gamma, ?_, ?_⟩
  · exact (hSq.sqBlockSlash gamma).toAnalyticBlock
  · exact sqRestrict_sqBlockSlash_eq_blockSlash hSq gamma

section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
    (Mfam : iota → IrrModule W) (h : iota → ℂ)

/-- Residual `hslash` for every trace block, with no slash hypothesis. -/
theorem traceBlock_S_sqRestrict_mem_analyticBlocks
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (i : iota) :
    sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈
      Submodule.map (sqRestrict W) (analyticBlocks W) := by
  apply sqRestrict_blockSlash_mem_analyticBlocks
  exact traceBlock_isAnalyticBlock Mfam h hcw
    (fun j ↦ onePointSubexp_of_c2 W (Mfam j).isMod (hcw j) hzero hC2) i

/-- **Unpinned modular-data existence** with residuals (c) and (e1) both discharged.
The remaining analytic realization hypothesis is residual (b), alongside the standing `Pr`.
The conclusion `∃ D, ZhuModularityAnalytic D` does not pin `D.Mfam`/`D.h` to the supplied family.

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem exists_zhuModularity_of_c2_sqSlash [Finite (Φ W)]
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card iota = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : iota, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W iota, ZhuModularityAnalytic D :=
  exists_zhuModularity_of_c2 Mfam h hC2 hss hreal Pr hcard hcw hsep
    (traceBlock_S_sqRestrict_mem_analyticBlocks Mfam h hcw (vacuumGradeZero_holds W) hC2)

end

end VOA
