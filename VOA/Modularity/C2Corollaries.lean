/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuModularityC2
import VOA.Modularity.ConformalWeightChoice
import VOA.Modularity.QEvalHolomorphic

/-!
# Free corollaries of the discharge of residual (c)

`Modularity.BlockGrowth.onePointSubexp_of_c2` proves the growth datum from `C₂`-cofiniteness alone.
Several data that the development had been carrying as hypotheses therefore become theorems.

## Main results

* `subexponentialCoeffs_of_c2` — the **character** growth datum
  (`Modularity.ConvergenceBridge.SubexponentialCoeffs`), the `v = 𝟙` case;
* `qSummable_gradedDim_of_c2` — hence the character `q`-series **converges** on `ℍ`, from `C₂`;
* `exists_zhuModularity_of_sqAnalyticRank_le_irr_c2` — the *minimal-closure* theorem with
  `hgr` removed, leaving exactly `hfib` and `hrank`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Character

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The character growth datum is free from `C₂`.**  `SubexponentialCoeffs` is the `v = 𝟙`
case of `OnePointSubexp`. -/
theorem subexponentialCoeffs_of_c2 (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    SubexponentialCoeffs N (hw - W.centralCharge / 24) := by
  have h := onePointSubexp_of_c2 W N hcw hzero hC2 W.vacuum
  rwa [show (fun n : ℕ => ‖torusOnePoint N W.vacuum (hw - W.centralCharge / 24 + (n : ℂ))‖)
    = (fun n : ℕ => ‖gradedDim N (hw - W.centralCharge / 24 + (n : ℂ))‖) from by
      funext n; rw [torusOnePoint_vacuum]; rfl] at h

/-- **The character `q`-series converges on `ℍ`, from `C₂`-cofiniteness alone.** -/
theorem qSummable_gradedDim_of_c2 (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (τ : UpperHalfPlane) :
    QSummableAt (gradedDim N) (hw - W.centralCharge / 24) τ :=
  qSummable_gradedDim N _ (subexponentialCoeffs_of_c2 N hcw hzero hC2) τ

end Character

section MinimalClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W)

/-- **The minimal-closure theorem with `hgr` discharged.**  What remains is exactly
`hfib` (residual **(d)**'s output, itself derivable from bottom separation) and `hrank`
(Zhu Thm 5.3.3 at an interior point, whose only gap is residual **(e1)**).

No `VacuumGradeZero` hypothesis: it holds for every VOA (`vacuumGradeZero_holds`). -/
theorem exists_zhuModularity_of_sqAnalyticRank_le_irr_c2
    (hC2 : C2Cofinite W)
    (hfib : FibreIndependent Mfam (fun i => conformalWeightOf (Mfam i)))
    (hrank : Module.rank ℂ
        (sqAnalyticSlashAmbient Mfam (fun i => conformalWeightOf (Mfam i)))
      ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  ⟨_, zhu_modularity_of_sqAnalyticRank_le_irr Mfam
    (fun i => onePointSubexp_of_c2 W (Mfam i).isMod (hasConformalWeight_family Mfam i)
      (vacuumGradeZero_holds W) hC2)
    hfib hrank⟩

end MinimalClosure

end VOA
