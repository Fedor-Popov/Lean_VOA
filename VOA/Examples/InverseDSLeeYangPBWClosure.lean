/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangBPZ

/-!
# Negative-Virasoro PBW closure for the inverse-DS Lee--Yang field

This leaf isolates the enveloping-algebra part of the coefficientwise BPZ calculation.  It
packages the numerator from `InverseDSLeeYangBPZ`, records the elementary negative-mode
reorderings used below, and verifies the first two PBW numerators directly as descendants of
the level-two and level-three target singular vectors.

The final section records the exact one-step recurrence.  Its remainder is the first point at
which induction on the four-term numerator ceases to be closed: two mixed PBW words and an
`L_{-5}` word appear.  Thus a uniform proof needs either a simultaneous PBW straightening
system containing these words or a graded maximal-submodule/character theorem.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangPBWClosure

open Module (End)
open ScreeningLowering
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFullFockWard
open LeeYangConcreteDescent LeeYangTargetNull LeeYangBPZ

noncomputable section

/-- The cleared four-term PBW numerator occurring on the right side of
`k85EEC_sourceSingular_PBWNumerator`. -/
def k85PBWNumerator (n : ℕ) : LeeYangFock :=
  (5 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
      k85TargetL (-2) (k85TargetL (-2) (k85TargetNegOnePower n)) +
    (-2 * (5 * (n : ℂ) + 11)) • k85TargetL (-2)
      (k85TargetNegOnePower (n + 2)) +
    (5 : ℂ) • k85TargetNegOnePower (n + 4) +
    (-3 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
      k85TargetL (-4) (k85TargetNegOnePower n)

theorem k85PBWNumerator_eq_clearedEEC (n : ℕ) :
    k85PBWNumerator n =
      ((n + 2).factorial : ℂ) •
        LatExp.EEC k85FockCharge (n : ℤ) k85SourceSingular := by
  rw [k85EEC_sourceSingular_PBWNumerator]
  rfl

theorem k85TargetSingularTwo_mem :
    k85TargetSingularTwo ∈ k85TargetCandidateNull := by
  apply seed_le_modeClosure k85TargetL k85TargetCandidateSeed
  apply Submodule.subset_span
  exact Set.mem_insert k85TargetSingularTwo {k85TargetSingularThree}

theorem k85TargetSingularThree_mem :
    k85TargetSingularThree ∈ k85TargetCandidateNull := by
  apply seed_le_modeClosure k85TargetL k85TargetCandidateSeed
  apply Submodule.subset_span
  exact Set.mem_insert_of_mem k85TargetSingularTwo (Set.mem_singleton _)

theorem k85TargetCandidateNull_mode_mem (m : ℤ) {x : LeeYangFock}
    (hx : x ∈ k85TargetCandidateNull) :
    k85TargetL m x ∈ k85TargetCandidateNull :=
  k85TargetCandidateNull_preserves m x hx

/-! ## Elementary negative-mode reorderings -/

theorem k85TargetL_negOne_negTwo (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-2) x) =
      k85TargetL (-2) (k85TargetL (-1) x) + k85TargetL (-3) x := by
  rw [k85TargetL_comm_apply]
  norm_num

theorem k85TargetL_negOne_negThree (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-3) x) =
      k85TargetL (-3) (k85TargetL (-1) x) +
        (2 : ℂ) • k85TargetL (-4) x := by
  rw [k85TargetL_comm_apply]
  norm_num

theorem k85TargetL_negOne_negFour (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-4) x) =
      k85TargetL (-4) (k85TargetL (-1) x) +
        (3 : ℂ) • k85TargetL (-5) x := by
  rw [k85TargetL_comm_apply]
  norm_num

theorem k85TargetL_negOne_negFive (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-5) x) =
      k85TargetL (-5) (k85TargetL (-1) x) +
        (4 : ℂ) • k85TargetL (-6) x := by
  rw [k85TargetL_comm_apply]
  norm_num

theorem k85TargetL_negThree_negTwo (x : LeeYangFock) :
    k85TargetL (-3) (k85TargetL (-2) x) =
      k85TargetL (-2) (k85TargetL (-3) x) - k85TargetL (-5) x := by
  rw [k85TargetL_comm_apply]
  norm_num [sub_eq_add_neg]

theorem k85TargetL_negFour_negTwo (x : LeeYangFock) :
    k85TargetL (-4) (k85TargetL (-2) x) =
      k85TargetL (-2) (k85TargetL (-4) x) -
        (2 : ℂ) • k85TargetL (-6) x := by
  rw [k85TargetL_comm_apply]
  norm_num [sub_eq_add_neg]

theorem k85TargetL_negOne_negTwo_sq (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-2) (k85TargetL (-2) x)) =
      k85TargetL (-2) (k85TargetL (-2) (k85TargetL (-1) x)) +
        k85TargetL (-2) (k85TargetL (-3) x) +
        k85TargetL (-3) (k85TargetL (-2) x) := by
  rw [k85TargetL_negOne_negTwo, k85TargetL_negOne_negTwo, map_add]

theorem k85TargetL_negOne_negOnePower (n : ℕ) :
    k85TargetL (-1) (k85TargetNegOnePower n) =
      k85TargetNegOnePower (n + 1) := by
  rw [k85TargetNegOnePower]

theorem k85TargetL_negOne_sq_negTwo (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-2) x)) =
      k85TargetL (-2) (k85TargetL (-1) (k85TargetL (-1) x)) +
        (2 : ℂ) • k85TargetL (-3) (k85TargetL (-1) x) +
        (2 : ℂ) • k85TargetL (-4) x := by
  rw [k85TargetL_negOne_negTwo, map_add, k85TargetL_negOne_negTwo,
    k85TargetL_negOne_negThree]
  module

theorem k85TargetL_negOne_cube_negTwo (x : LeeYangFock) :
    k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-2) x))) =
      k85TargetL (-2)
          (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-1) x))) +
        (3 : ℂ) • k85TargetL (-3)
          (k85TargetL (-1) (k85TargetL (-1) x)) +
        (6 : ℂ) • k85TargetL (-4) (k85TargetL (-1) x) +
        (6 : ℂ) • k85TargetL (-5) x := by
  rw [k85TargetL_negOne_sq_negTwo, map_add, map_add, map_smul, map_smul,
    k85TargetL_negOne_negTwo, k85TargetL_negOne_negThree,
    k85TargetL_negOne_negFour]
  simp only [smul_add, smul_smul]
  module

theorem k85TargetL_negOne_fourth_negTwo (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-2) x)))) =
      k85TargetL (-2) (k85TargetL (-1)
          (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-1) x)))) +
        (4 : ℂ) • k85TargetL (-3)
          (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-1) x))) +
        (12 : ℂ) • k85TargetL (-4)
          (k85TargetL (-1) (k85TargetL (-1) x)) +
        (24 : ℂ) • k85TargetL (-5) (k85TargetL (-1) x) +
        (24 : ℂ) • k85TargetL (-6) x := by
  rw [k85TargetL_negOne_cube_negTwo, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, k85TargetL_negOne_negTwo,
    k85TargetL_negOne_negThree, k85TargetL_negOne_negFour,
    k85TargetL_negOne_negFive]
  simp only [smul_add, smul_smul]
  module

theorem k85TargetL_negOne_sq_negThree (x : LeeYangFock) :
    k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-3) x)) =
      k85TargetL (-3) (k85TargetL (-1) (k85TargetL (-1) x)) +
        (4 : ℂ) • k85TargetL (-4) (k85TargetL (-1) x) +
        (6 : ℂ) • k85TargetL (-5) x := by
  rw [k85TargetL_negOne_negThree, map_add, map_smul,
    k85TargetL_negOne_negThree, k85TargetL_negOne_negFour]
  simp only [smul_add, smul_smul]
  module

theorem k85TargetL_negOne_cube_negThree (x : LeeYangFock) :
    k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-3) x))) =
      k85TargetL (-3)
          (k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-1) x))) +
        (6 : ℂ) • k85TargetL (-4)
          (k85TargetL (-1) (k85TargetL (-1) x)) +
        (18 : ℂ) • k85TargetL (-5) (k85TargetL (-1) x) +
        (24 : ℂ) • k85TargetL (-6) x := by
  rw [k85TargetL_negOne_sq_negThree, map_add, map_add, map_smul, map_smul,
    k85TargetL_negOne_negThree, k85TargetL_negOne_negFour,
    k85TargetL_negOne_negFive]
  simp only [smul_add, smul_smul]
  module

/-! ## A more economical level-three seed relation -/

/-- The two original singular vectors imply the reduced level-three relation
`5 L_{-2} L_{-1} v - L_{-3} v`.  This is the first overlap relation for PBW
straightening. -/
theorem k85TargetReducedSingularThree_mem :
    (5 : ℂ) • k85TargetL (-2) (k85TargetL (-1) k85TargetTop) +
        (-1 : ℂ) • k85TargetL (-3) k85TargetTop ∈
      k85TargetCandidateNull := by
  have hA2 : k85TargetL (-1) k85TargetSingularTwo ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem
  have hcomb : (5 : ℂ) • k85TargetL (-1) k85TargetSingularTwo +
      (-1 : ℂ) • k85TargetSingularThree ∈ k85TargetCandidateNull :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hA2)
      (Submodule.smul_mem _ _ k85TargetSingularThree_mem)
  rw [k85TargetSingularTwo, k85TargetSingularThree, map_add, map_smul, map_smul,
    k85TargetL_negOne_negTwo] at hcomb
  simp only [smul_add, smul_smul] at hcomb
  have hscaled : (6 : ℂ) •
      ((5 : ℂ) • k85TargetL (-2) (k85TargetL (-1) k85TargetTop) +
        (-1 : ℂ) • k85TargetL (-3) k85TargetTop) ∈
      k85TargetCandidateNull := by
    convert hcomb using 1
    module
  have hsix : (6 : ℂ) ≠ 0 := by norm_num
  exact (Submodule.smul_mem_iff k85TargetCandidateNull hsix).mp hscaled

/-! ## The first two numerator witnesses -/

theorem k85PBWNumerator_zero_descendant :
    k85PBWNumerator 0 =
      (-5 : ℂ) • k85TargetL (-2) k85TargetSingularTwo +
      (11 / 6 : ℂ) • k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo) +
      (-1 / 6 : ℂ) • k85TargetL (-1) k85TargetSingularThree := by
  rw [k85PBWNumerator]
  norm_num [k85TargetNegOnePower]
  rw [k85TargetSingularTwo, k85TargetSingularThree]
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [k85TargetL_negOne_sq_negTwo, k85TargetL_negOne_negTwo,
    k85TargetL_negOne_negThree]
  simp only [smul_add, smul_smul]
  module

theorem k85PBWNumerator_zero_mem :
    k85PBWNumerator 0 ∈ k85TargetCandidateNull := by
  rw [k85PBWNumerator_zero_descendant]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _
        (k85TargetCandidateNull_mode_mem (-2) k85TargetSingularTwo_mem))
      (Submodule.smul_mem _ _
        (k85TargetCandidateNull_mode_mem (-1)
          (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem))))
    (Submodule.smul_mem _ _
      (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularThree_mem))

theorem k85PBWNumerator_one_descendant :
    k85PBWNumerator 1 =
      (3 : ℂ) • k85TargetL (-3) k85TargetSingularTwo +
      (-5 / 3 : ℂ) • k85TargetL (-2)
        (k85TargetL (-1) k85TargetSingularTwo) +
      (1 / 6 : ℂ) • k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo)) +
      (-2 / 3 : ℂ) • k85TargetL (-2) k85TargetSingularThree +
      (1 / 6 : ℂ) • k85TargetL (-1)
        (k85TargetL (-1) k85TargetSingularThree) := by
  rw [k85PBWNumerator]
  norm_num [k85TargetNegOnePower]
  rw [k85TargetSingularTwo, k85TargetSingularThree]
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [k85TargetL_negOne_cube_negTwo, k85TargetL_negOne_sq_negTwo,
    k85TargetL_negOne_sq_negThree, k85TargetL_negThree_negTwo,
    k85TargetL_negOne_negTwo]
  simp only [map_add, smul_add, smul_smul, sub_eq_add_neg]
  module

theorem k85PBWNumerator_one_mem :
    k85PBWNumerator 1 ∈ k85TargetCandidateNull := by
  rw [k85PBWNumerator_one_descendant]
  have h2a : k85TargetL (-3) k85TargetSingularTwo ∈ k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-3) k85TargetSingularTwo_mem
  have h2b : k85TargetL (-2) (k85TargetL (-1) k85TargetSingularTwo) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-2)
      (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem)
  have h2c : k85TargetL (-1)
      (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo)) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1)
      (k85TargetCandidateNull_mode_mem (-1)
        (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem))
  have h3a : k85TargetL (-2) k85TargetSingularThree ∈ k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-2) k85TargetSingularThree_mem
  have h3b : k85TargetL (-1) (k85TargetL (-1) k85TargetSingularThree) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1)
      (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularThree_mem)
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _ (Submodule.smul_mem _ _ h2a)
          (Submodule.smul_mem _ _ h2b))
        (Submodule.smul_mem _ _ h2c))
      (Submodule.smul_mem _ _ h3a))
    (Submodule.smul_mem _ _ h3b)

theorem k85PBWNumerator_two_descendant :
    k85PBWNumerator 2 =
      (4 : ℂ) • k85TargetL (-4) k85TargetSingularTwo +
      (-32 / 9 : ℂ) • k85TargetL (-3)
        (k85TargetL (-1) k85TargetSingularTwo) +
      (10 / 9 : ℂ) • k85TargetL (-2)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo)) +
      (-1 / 9 : ℂ) • k85TargetL (-1) (k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo))) +
      (16 / 9 : ℂ) • k85TargetL (-3) k85TargetSingularThree +
      (-14 / 9 : ℂ) • k85TargetL (-2)
        (k85TargetL (-1) k85TargetSingularThree) +
      (2 / 9 : ℂ) • k85TargetL (-1)
        (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularThree)) := by
  rw [k85PBWNumerator]
  norm_num [k85TargetNegOnePower]
  rw [k85TargetSingularTwo, k85TargetSingularThree]
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [k85TargetL_negOne_fourth_negTwo, k85TargetL_negOne_cube_negTwo,
    k85TargetL_negOne_cube_negThree, k85TargetL_negOne_sq_negTwo,
    k85TargetL_negOne_negThree]
  simp only [k85TargetL_negOne_negTwo,
    k85TargetL_negThree_negTwo, k85TargetL_negFour_negTwo,
    map_add, map_smul, smul_add, smul_smul, sub_eq_add_neg]
  module

theorem k85PBWNumerator_two_mem :
    k85PBWNumerator 2 ∈ k85TargetCandidateNull := by
  rw [k85PBWNumerator_two_descendant]
  have h2a : k85TargetL (-4) k85TargetSingularTwo ∈ k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-4) k85TargetSingularTwo_mem
  have h2b : k85TargetL (-3) (k85TargetL (-1) k85TargetSingularTwo) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-3)
      (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem)
  have h2c : k85TargetL (-2)
      (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo)) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-2)
      (k85TargetCandidateNull_mode_mem (-1)
        (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem))
  have h2d : k85TargetL (-1) (k85TargetL (-1)
      (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularTwo))) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1)
      (k85TargetCandidateNull_mode_mem (-1)
        (k85TargetCandidateNull_mode_mem (-1)
          (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularTwo_mem)))
  have h3a : k85TargetL (-3) k85TargetSingularThree ∈ k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-3) k85TargetSingularThree_mem
  have h3b : k85TargetL (-2) (k85TargetL (-1) k85TargetSingularThree) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-2)
      (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularThree_mem)
  have h3c : k85TargetL (-1)
      (k85TargetL (-1) (k85TargetL (-1) k85TargetSingularThree)) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1)
      (k85TargetCandidateNull_mode_mem (-1)
        (k85TargetCandidateNull_mode_mem (-1) k85TargetSingularThree_mem))
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _
            (Submodule.add_mem _ (Submodule.smul_mem _ _ h2a)
              (Submodule.smul_mem _ _ h2b))
            (Submodule.smul_mem _ _ h2c))
          (Submodule.smul_mem _ _ h2d))
        (Submodule.smul_mem _ _ h3a))
      (Submodule.smul_mem _ _ h3b))
    (Submodule.smul_mem _ _ h3c)

/-! ## Exact one-step obstruction to a closed induction -/

/-- The six-term remainder left after applying `L_{-1}` to one PBW numerator and reordering
only the newly created leftmost mode.  In particular, the one-family induction creates mixed
`L_{-2}L_{-3}`, `L_{-3}L_{-2}`, and `L_{-5}` words. -/
def k85PBWStepRemainder (n : ℕ) : LeeYangFock :=
  (10 * ((n : ℂ) + 2)) •
      k85TargetL (-2) (k85TargetL (-2) (k85TargetNegOnePower (n + 1))) +
    (-10 : ℂ) • k85TargetL (-2) (k85TargetNegOnePower (n + 3)) +
    (-6 * ((n : ℂ) + 2)) •
      k85TargetL (-4) (k85TargetNegOnePower (n + 1)) +
    (-5 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
      (k85TargetL (-2) (k85TargetL (-3) (k85TargetNegOnePower n)) +
        k85TargetL (-3) (k85TargetL (-2) (k85TargetNegOnePower n))) +
    (2 * (5 * (n : ℂ) + 11)) •
      k85TargetL (-3) (k85TargetNegOnePower (n + 2)) +
    (9 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
      k85TargetL (-5) (k85TargetNegOnePower n)

/-- Exact successor identity.  This is constructive and uses only the Virasoro commutator;
it is the minimal recurrence generated by the four displayed PBW words. -/
theorem k85PBWNumerator_succ (n : ℕ) :
    k85PBWNumerator (n + 1) =
      k85TargetL (-1) (k85PBWNumerator n) + k85PBWStepRemainder n := by
  simp only [k85PBWNumerator, k85PBWStepRemainder, map_add, map_smul,
    k85TargetL_negOne_negOnePower]
  rw [k85TargetL_negOne_negTwo_sq, k85TargetL_negOne_negTwo,
    k85TargetL_negOne_negFour]
  simp only [k85TargetL_negOne_negOnePower, smul_add, smul_smul]
  push_cast
  module

theorem k85PBWStepRemainder_mem_of_numerators_mem (n : ℕ)
    (hn : k85PBWNumerator n ∈ k85TargetCandidateNull)
    (hsucc : k85PBWNumerator (n + 1) ∈ k85TargetCandidateNull) :
    k85PBWStepRemainder n ∈ k85TargetCandidateNull := by
  have hmode : k85TargetL (-1) (k85PBWNumerator n) ∈
      k85TargetCandidateNull :=
    k85TargetCandidateNull_mode_mem (-1) hn
  have hsub : k85PBWNumerator (n + 1) -
      k85TargetL (-1) (k85PBWNumerator n) ∈ k85TargetCandidateNull :=
    Submodule.sub_mem _ hsucc hmode
  have heq : k85PBWStepRemainder n = k85PBWNumerator (n + 1) -
      k85TargetL (-1) (k85PBWNumerator n) := by
    rw [k85PBWNumerator_succ]
    module
  rwa [heq]

theorem k85PBWNumerator_all_mem_of_remainder
    (hrem : ∀ n : ℕ, k85PBWStepRemainder n ∈ k85TargetCandidateNull) :
    ∀ n : ℕ, k85PBWNumerator n ∈ k85TargetCandidateNull := by
  intro n
  induction n with
  | zero => exact k85PBWNumerator_zero_mem
  | succ n ih =>
      change k85PBWNumerator (n + 1) ∈ k85TargetCandidateNull
      rw [k85PBWNumerator_succ n]
      exact Submodule.add_mem _
        (k85TargetCandidateNull_mode_mem (-1) ih) (hrem n)

/-- Uniform numerator closure is exactly the new remainder family.  The forward implication
uses invariance of the candidate null submodule; the reverse implication is the successor
identity above. -/
theorem k85PBWNumerator_all_mem_iff_remainder :
    (∀ n : ℕ, k85PBWNumerator n ∈ k85TargetCandidateNull) ↔
      ∀ n : ℕ, k85PBWStepRemainder n ∈ k85TargetCandidateNull := by
  constructor
  · intro h n
    exact k85PBWStepRemainder_mem_of_numerators_mem n (h n) (h (n + 1))
  · exact k85PBWNumerator_all_mem_of_remainder

theorem k85PBWStepRemainder_zero_mem :
    k85PBWStepRemainder 0 ∈ k85TargetCandidateNull :=
  k85PBWStepRemainder_mem_of_numerators_mem 0
    k85PBWNumerator_zero_mem k85PBWNumerator_one_mem

/-- The first two numerator certificates remove remainder index zero from the recurrence. -/
theorem k85PBWNumerator_all_mem_iff_remainder_succ :
    (∀ n : ℕ, k85PBWNumerator n ∈ k85TargetCandidateNull) ↔
      ∀ n : ℕ, k85PBWStepRemainder (n + 1) ∈ k85TargetCandidateNull := by
  constructor
  · intro h n
    exact k85PBWStepRemainder_mem_of_numerators_mem (n + 1)
      (h (n + 1)) (h (n + 2))
  · intro h
    apply k85PBWNumerator_all_mem_of_remainder
    intro n
    cases n with
    | zero => exact k85PBWStepRemainder_zero_mem
    | succ n => exact h n

theorem k85PBWStepRemainder_one_mem :
    k85PBWStepRemainder 1 ∈ k85TargetCandidateNull :=
  k85PBWStepRemainder_mem_of_numerators_mem 1
    k85PBWNumerator_one_mem k85PBWNumerator_two_mem

/-- The explicit certificates through numerator index two discharge the first two recurrence
remainders.  The first family not settled in this leaf is therefore remainder index two. -/
theorem k85PBWNumerator_all_mem_iff_remainder_addTwo :
    (∀ n : ℕ, k85PBWNumerator n ∈ k85TargetCandidateNull) ↔
      ∀ n : ℕ, k85PBWStepRemainder (n + 2) ∈ k85TargetCandidateNull := by
  constructor
  · intro h n
    exact k85PBWStepRemainder_mem_of_numerators_mem (n + 2)
      (h (n + 2)) (h (n + 3))
  · intro h
    apply k85PBWNumerator_all_mem_of_remainder
    intro n
    cases n with
    | zero => exact k85PBWStepRemainder_zero_mem
    | succ n =>
        cases n with
        | zero => exact k85PBWStepRemainder_one_mem
        | succ n => exact h n

theorem k85PBWNumerator_mem_iff_EEC (n : ℕ) :
    k85PBWNumerator n ∈ k85TargetCandidateNull ↔
      LatExp.EEC k85FockCharge (n : ℤ) k85SourceSingular ∈
        k85TargetCandidateNull := by
  rw [k85PBWNumerator_eq_clearedEEC]
  have hf : (((n + 2).factorial : ℂ) ≠ 0) := by
    exact_mod_cast Nat.factorial_ne_zero (n + 2)
  exact Submodule.smul_mem_iff k85TargetCandidateNull hf

/-- Coefficientwise nonnegative BPZ descent is reduced, without any scalar
denominators, to the mixed-word remainder family starting at index two. -/
theorem k85EEC_nat_all_mem_iff_PBW_remainder_addTwo :
    (∀ n : ℕ, LatExp.EEC k85FockCharge (n : ℤ) k85SourceSingular ∈
        k85TargetCandidateNull) ↔
      ∀ n : ℕ, k85PBWStepRemainder (n + 2) ∈ k85TargetCandidateNull := by
  constructor
  · intro h
    apply k85PBWNumerator_all_mem_iff_remainder_addTwo.mp
    intro n
    exact (k85PBWNumerator_mem_iff_EEC n).mpr (h n)
  · intro h n
    apply (k85PBWNumerator_mem_iff_EEC n).mp
    exact k85PBWNumerator_all_mem_iff_remainder_addTwo.mpr h n

/-!
## Remaining representation-theoretic input

The constructive route stops at `k85PBWNumerator_all_mem_iff_remainder_addTwo`: commuting the
leftmost `L_{-1}` does not preserve the four-word numerator ansatz.  It produces both orders of
the mixed `(2,3)` word and an `L_{-5}` word.  Repeating the same step produces unbounded PBW
partitions, so a closed induction needs a simultaneous straightening invariant (equivalently, a
proved terminating reduction system for the left submodule generated by the two singular
vectors), not another scalar identity.

The character/maximal-submodule route would instead need a graded highest-weight presentation of
this charged Fock module and a theorem identifying `k85TargetCandidateNull` with its maximal
proper submodule, or an equality of every graded dimension of the quotient with the Lee--Yang
`h = -1/5` irreducible character.  No such presentation, quotient grading, or Rocha--Caridi /
Rogers--Ramanujan character identity is available on the import path.  Consequently maximality
cannot currently turn the already-proved singular-vector membership into uniform membership of
the BPZ family.
-/

end
end LeeYangPBWClosure
end InverseDS
end VOA
