/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangConcreteDescent

/-!
# The explicit weight `-1/5` target null generators

The charged Feigin--Fuchs vacuum is a Lee--Yang highest-weight vector of weight `-1/5`.
This file records the two standard singular expressions at levels two and three and packages
the target candidate null submodule that they generate.  Descent to this candidate is then the
fully explicit coefficient-membership problem left by the Fock Ward construction.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangTargetNull

open Module (End)
open ScreeningLowering LeeYangWardClosure
open LeeYangIntertwinerDescent LeeYangConcreteDescent
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFullFockWard

noncomputable section

/-- The polynomial vacuum, regarded as the highest-weight vector of the charged target sector. -/
def k85TargetTop : LeeYangFock := HeisenbergN.vacuumN 1

theorem alphaMode_targetTop_nonneg (n : ℤ) (hn : 0 ≤ n) :
    alphaMode n k85TargetTop = 0 := by
  exact HeisenbergN.oscN_vacuum 1 2 0 n hn

theorem sectorCurrent_targetTop_pos (p : ℂ) (n : ℤ) (hn : 0 < n) :
    sectorCurrent p n k85TargetTop = 0 := by
  rw [sectorCurrent, if_neg (by omega : n ≠ 0), zero_smul, add_zero]
  exact alphaMode_targetTop_nonneg n (by omega)

theorem sectorSugawara_targetTop_pos (p : ℂ) (n : ℤ) (hn : 0 < n) :
    sectorSugawara p n k85TargetTop = 0 := by
  have hL : HeisenbergN.LvirN 1 2 n k85TargetTop = 0 := by
    exact HeisenbergN.LvirN_vacuum 1 2 (by omega : -1 ≤ n)
  have ha := alphaMode_targetTop_nonneg n (by omega : 0 ≤ n)
  simp only [sectorSugawara, LinearMap.add_apply, LinearMap.smul_apply,
    if_neg (by omega : n ≠ 0), zero_smul, hL, ha, smul_zero, add_zero]

/-- Every positive target Virasoro mode annihilates the charged top vector. -/
theorem k85TargetL_pos_annihilate (n : ℤ) (hn : 0 < n) :
    k85TargetL n k85TargetTop = 0 := by
  rw [k85TargetL, sectorVirasoro, LinearMap.sub_apply,
    sectorSugawara_targetTop_pos k85FockCharge n hn,
    sectorBackgroundCurrent]
  simp only [LinearMap.smul_apply]
  rw [sectorCurrent_targetTop_pos k85FockCharge n hn, smul_zero, smul_zero, sub_zero]

theorem sectorSugawara_targetTop_zero (p : ℂ) :
    sectorSugawara p 0 k85TargetTop = p ^ 2 • k85TargetTop := by
  have hL : HeisenbergN.LvirN 1 2 0 k85TargetTop = 0 := by
    exact HeisenbergN.LvirN_vacuum 1 2 (by norm_num : -1 ≤ (0 : ℤ))
  have ha := alphaMode_targetTop_nonneg 0 (by norm_num : (0 : ℤ) ≤ 0)
  simp only [sectorSugawara, LinearMap.add_apply, LinearMap.smul_apply,
    hL, ha, smul_zero, zero_add, if_true, Module.End.one_apply]

theorem sectorCurrent_targetTop_zero (p : ℂ) :
    sectorCurrent p 0 k85TargetTop = (2 * p) • k85TargetTop := by
  rw [sectorCurrent, LinearMap.add_apply, LinearMap.smul_apply,
    alphaMode_targetTop_nonneg 0 (by norm_num), zero_add, if_pos rfl,
    Module.End.one_apply]

/-- The target top has conformal weight `-1/5`. -/
theorem k85TargetL_zero :
    k85TargetL 0 k85TargetTop = k85ScreeningVirWeight • k85TargetTop := by
  rw [k85TargetL, sectorVirasoro, LinearMap.sub_apply,
    sectorSugawara_targetTop_zero, sectorBackgroundCurrent]
  simp only [LinearMap.smul_apply]
  rw [sectorCurrent_targetTop_zero]
  simp only [smul_smul]
  norm_num
  rw [show k85FockBackground * (2 * k85FockCharge) =
      2 * k85FockBackground * k85FockCharge by ring,
    ← sub_smul, k85FockWeight]

/-- The target Virasoro commutator, evaluated on a Fock vector. -/
theorem k85TargetL_comm_apply (m n : ℤ) (x : LeeYangFock) :
    k85TargetL m (k85TargetL n x) =
      k85TargetL n (k85TargetL m x) +
        ((m : ℂ) - n) • k85TargetL (m + n) x +
        (if m + n = 0 then
          ((((m : ℂ) ^ 3 - m) / 12 * leeYangCentralCharge) •
            (1 : End ℂ LeeYangFock)) x else 0) := by
  have h := LinearMap.congr_fun (k85TargetL_isLeeYang m n) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at h
  calc
    _ = (((m : ℂ) - n) • k85TargetL (m + n) +
          (if m + n = 0 then
            (((m : ℂ) ^ 3 - m) / 12 * leeYangCentralCharge) •
              (1 : End ℂ LeeYangFock) else 0)) x +
        k85TargetL n (k85TargetL m x) := eq_add_of_sub_eq h
    _ = _ := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      by_cases hmn : m + n = 0
      · simp only [if_pos hmn, LinearMap.smul_apply, Module.End.one_apply]
        abel
      · simp only [if_neg hmn, LinearMap.zero_apply]
        abel

theorem k85TargetL_one_negOne_top :
    k85TargetL 1 (k85TargetL (-1) k85TargetTop) =
      (-2 / 5 : ℂ) • k85TargetTop := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 1 (by norm_num), map_zero,
    show (1 : ℤ) + -1 = 0 by norm_num, k85TargetL_zero]
  simp only [if_pos rfl, Module.End.one_apply, Int.cast_one, Int.cast_negSucc,
    sub_neg_eq_add, one_add_one_eq_two, smul_smul]
  norm_num [k85ScreeningVirWeight, leeYangCentralCharge]

theorem k85TargetL_zero_negOne_top :
    k85TargetL 0 (k85TargetL (-1) k85TargetTop) =
      (4 / 5 : ℂ) • k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_zero, map_smul,
    show (0 : ℤ) + -1 = -1 by norm_num]
  norm_num
  push_cast
  rw [k85ScreeningVirWeight]
  module

theorem k85TargetL_one_negOne_sq_top :
    k85TargetL 1 (k85TargetL (-1) (k85TargetL (-1) k85TargetTop)) =
      (6 / 5 : ℂ) • k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_one_negOne_top, map_smul,
    show (1 : ℤ) + -1 = 0 by norm_num, k85TargetL_zero_negOne_top]
  push_cast
  norm_num [leeYangCentralCharge]
  module

theorem k85TargetL_one_negTwo_top :
    k85TargetL 1 (k85TargetL (-2) k85TargetTop) =
      (3 : ℂ) • k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 1 (by norm_num), map_zero,
    show (1 : ℤ) + -2 = -1 by norm_num]
  norm_num

theorem k85TargetL_two_negOne_top :
    k85TargetL 2 (k85TargetL (-1) k85TargetTop) = 0 := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 2 (by norm_num), map_zero,
    show (2 : ℤ) + -1 = 1 by norm_num,
    k85TargetL_pos_annihilate 1 (by norm_num)]
  norm_num

theorem k85TargetL_two_negOne_sq_top :
    k85TargetL 2 (k85TargetL (-1) (k85TargetL (-1) k85TargetTop)) =
      (-6 / 5 : ℂ) • k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_two_negOne_top, map_zero,
    show (2 : ℤ) + -1 = 1 by norm_num, k85TargetL_one_negOne_top]
  norm_num
  push_cast
  module

theorem k85TargetL_two_negTwo_top :
    k85TargetL 2 (k85TargetL (-2) k85TargetTop) =
      (-3 : ℂ) • k85TargetTop := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 2 (by norm_num), map_zero,
    show (2 : ℤ) + -2 = 0 by norm_num, k85TargetL_zero]
  simp only [if_pos rfl, Module.End.one_apply, smul_smul]
  norm_num [k85ScreeningVirWeight, leeYangCentralCharge]
  module

/-! ## The two target singular expressions -/

/-- The level-two singular expression `5 L_-1^2 v - 2 L_-2 v`. -/
def k85TargetSingularTwo : LeeYangFock :=
  (5 : ℂ) • k85TargetL (-1) (k85TargetL (-1) k85TargetTop) +
    (-2 : ℂ) • k85TargetL (-2) k85TargetTop

theorem k85TargetSingularTwo_L1 :
    k85TargetL 1 k85TargetSingularTwo = 0 := by
  rw [k85TargetSingularTwo, map_add, map_smul, map_smul,
    k85TargetL_one_negOne_sq_top, k85TargetL_one_negTwo_top,
    smul_smul, smul_smul]
  norm_num

theorem k85TargetSingularTwo_L2 :
    k85TargetL 2 k85TargetSingularTwo = 0 := by
  rw [k85TargetSingularTwo, map_add, map_smul, map_smul,
    k85TargetL_two_negOne_sq_top, k85TargetL_two_negTwo_top,
    smul_smul, smul_smul]
  norm_num

theorem k85TargetL_zero_negOne_sq_top :
    k85TargetL 0 (k85TargetL (-1) (k85TargetL (-1) k85TargetTop)) =
      (9 / 5 : ℂ) • k85TargetL (-1) (k85TargetL (-1) k85TargetTop) := by
  rw [k85TargetL_comm_apply, k85TargetL_zero_negOne_top, map_smul,
    show (0 : ℤ) + -1 = -1 by norm_num]
  norm_num
  push_cast
  module

theorem k85TargetL_one_negOne_cube_top :
    k85TargetL 1 (k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetTop))) =
      (24 / 5 : ℂ) • k85TargetL (-1) (k85TargetL (-1) k85TargetTop) := by
  rw [k85TargetL_comm_apply, k85TargetL_one_negOne_sq_top, map_smul,
    show (1 : ℤ) + -1 = 0 by norm_num, k85TargetL_zero_negOne_sq_top]
  norm_num [leeYangCentralCharge]
  push_cast
  module

theorem k85TargetL_one_negTwo_negOne_top :
    k85TargetL 1 (k85TargetL (-2) (k85TargetL (-1) k85TargetTop)) =
      (3 : ℂ) • k85TargetL (-1) (k85TargetL (-1) k85TargetTop) +
        (-2 / 5 : ℂ) • k85TargetL (-2) k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_one_negOne_top, map_smul,
    show (1 : ℤ) + -2 = -1 by norm_num]
  norm_num
  push_cast
  abel

theorem k85TargetL_one_negThree_top :
    k85TargetL 1 (k85TargetL (-3) k85TargetTop) =
      (4 : ℂ) • k85TargetL (-2) k85TargetTop := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 1 (by norm_num), map_zero,
    show (1 : ℤ) + -3 = -2 by norm_num]
  norm_num

theorem k85TargetL_two_negOne_cube_top :
    k85TargetL 2 (k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetTop))) =
      (12 / 5 : ℂ) • k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_two_negOne_sq_top, map_smul,
    show (2 : ℤ) + -1 = 1 by norm_num, k85TargetL_one_negOne_sq_top]
  norm_num
  push_cast
  module

theorem k85TargetL_two_negTwo_negOne_top :
    k85TargetL 2 (k85TargetL (-2) (k85TargetL (-1) k85TargetTop)) =
      k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply, k85TargetL_two_negOne_top, map_zero,
    show (2 : ℤ) + -2 = 0 by norm_num, k85TargetL_zero_negOne_top]
  norm_num [leeYangCentralCharge]
  push_cast
  module

theorem k85TargetL_two_negThree_top :
    k85TargetL 2 (k85TargetL (-3) k85TargetTop) =
      (5 : ℂ) • k85TargetL (-1) k85TargetTop := by
  rw [k85TargetL_comm_apply,
    k85TargetL_pos_annihilate 2 (by norm_num), map_zero,
    show (2 : ℤ) + -3 = -1 by norm_num]
  norm_num

/-- The level-three singular expression
`25 L_-1^3 v - 40 L_-2 L_-1 v - 4 L_-3 v`. -/
def k85TargetSingularThree : LeeYangFock :=
  (25 : ℂ) • k85TargetL (-1)
      (k85TargetL (-1) (k85TargetL (-1) k85TargetTop)) +
    (-40 : ℂ) • k85TargetL (-2) (k85TargetL (-1) k85TargetTop) +
    (-4 : ℂ) • k85TargetL (-3) k85TargetTop

theorem k85TargetSingularThree_L1 :
    k85TargetL 1 k85TargetSingularThree = 0 := by
  rw [k85TargetSingularThree, map_add, map_add, map_smul, map_smul, map_smul,
    k85TargetL_one_negOne_cube_top, k85TargetL_one_negTwo_negOne_top,
    k85TargetL_one_negThree_top]
  simp only [smul_add, smul_smul]
  norm_num

theorem k85TargetSingularThree_L2 :
    k85TargetL 2 k85TargetSingularThree = 0 := by
  rw [k85TargetSingularThree, map_add, map_add, map_smul, map_smul, map_smul,
    k85TargetL_two_negOne_cube_top, k85TargetL_two_negTwo_negOne_top,
    k85TargetL_two_negThree_top, smul_smul, smul_smul]
  norm_num
  module

/-- Candidate maximal null submodule in the weight `-1/5` target: the invariant closure of the
level-two and level-three singular expressions. -/
def k85TargetCandidateSeed : Submodule ℂ LeeYangFock :=
  Submodule.span ℂ {k85TargetSingularTwo, k85TargetSingularThree}

def k85TargetCandidateNull : Submodule ℂ LeeYangFock :=
  modeClosure k85TargetL k85TargetCandidateSeed

theorem k85TargetCandidateNull_preserves :
    ModeFamilyPreserves k85TargetCandidateNull k85TargetL :=
  modeClosure_preserves k85TargetL k85TargetCandidateSeed

/-- Exact BPZ/null-decoupling gate for the concrete two-singular target candidate. -/
theorem k85FockField_respects_targetCandidate_iff :
    FieldRespectsNullSubmodules k85SourceNull k85TargetCandidateNull k85FockField ↔
      ∀ t : ℤ, k85FockField t k85SourceSingular ∈ k85TargetCandidateNull :=
  k85FockField_respects_sourceNull_iff
    k85TargetCandidateNull k85TargetCandidateNull_preserves

/-- Since all odd half-power coefficients vanish, the remaining BPZ gate is equivalently the
integer-indexed family of arbitrary-momentum exponential coefficients. -/
theorem k85BPZ_iff_integerEEC :
    (∀ t : ℤ, k85FockField t k85SourceSingular ∈ k85TargetCandidateNull) ↔
      ∀ s : ℤ, LatExp.EEC k85FockCharge s k85SourceSingular ∈
        k85TargetCandidateNull := by
  constructor
  · intro h s
    have hs := h (2 * s)
    rw [k85FockField_of_eq (2 * s) s rfl] at hs
    exact hs
  · intro h t
    by_cases hm : EvenHalfPowerMatch t
    · obtain ⟨s, hs⟩ := hm
      rw [k85FockField_of_eq t s hs]
      exact h s
    · rw [k85FockField_of_not_match t hm, LinearMap.zero_apply]
      exact Submodule.zero_mem _

/-- Supplying the explicit BPZ coefficient membership gives a concrete quotient screening
field with no further Ward or closure obligations. -/
noncomputable def k85TargetCandidateDescentData
    (hBPZ : ∀ t : ℤ, k85FockField t k85SourceSingular ∈ k85TargetCandidateNull) :
    K85ScreeningDescentData k85FockVirasoroScreeningFieldData where
  sourceNull := k85SourceNull
  targetNull := k85TargetCandidateNull
  sourceMode_preserves := k85SourceNull_preserves
  targetMode_preserves := k85TargetCandidateNull_preserves
  field_preserves := k85FockField_respects_targetCandidate_iff.mpr hBPZ

end
end LeeYangTargetNull
end InverseDS
end VOA
