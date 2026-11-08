/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringGenerators
import Mathlib.Tactic.LinearCombination

/-! # The critical central-charge computation

The four identities of the `c = 26` lemma are proved for arbitrary central charge, including
the exact defect `c / 2 - 13`. No highest-weight condition is imposed on the
weight-minus-one vector. Only its weight and the Virasoro relations are used.
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

noncomputable def tildeNegativeTwo : Module.End ℂ H := M.L (-2) + (3 / 2 : ℂ) • (M.L (-1) * M.L (-1))

noncomputable def tildePositiveTwo : Module.End ℂ H := M.L 2 + (3 / 2 : ℂ) • (M.L 1 * M.L 1)

theorem tildeTwo_adjoint (x y : H) :
    M.B (M.tildePositiveTwo x) y = M.B x (M.tildeNegativeTwo y) := by
  simp only [tildePositiveTwo, tildeNegativeTwo, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.mul_apply, map_add, map_smul, M.L_adj]

theorem tildeNegativeTwo_mem_spurious (x : H) : M.tildeNegativeTwo x ∈ M.spurious :=
  M.spurious.add_mem (M.negative_L_mem_spurious 1 x)
    (M.spurious.smul_mem _ (M.negative_L_mem_spurious 0 (M.L (-1) x)))

theorem tildePositiveTwo_kVacuum (x : H) (hx : x ∈ M.kVacuum) :
    M.tildePositiveTwo x ∈ M.kVacuum :=
  M.kVacuum.add_mem (M.kVacuum_L_stable 1 x hx)
    (M.kVacuum.smul_mem _ (M.kVacuum_L_stable 0 _ (M.kVacuum_L_stable 0 x hx)))

theorem L_one_negative_one (x : H) :
    M.L 1 (M.L (-1) x) = M.L (-1) (M.L 1 x) + (2 : ℂ) • M.L 0 x := by
  have h := M.L_comm_apply 1 (-1) x
  norm_num at h
  linear_combination (norm := module) h

theorem L_two_negative_one (x : H) :
    M.L 2 (M.L (-1) x) = M.L (-1) (M.L 2 x) + (3 : ℂ) • M.L 1 x := by
  have h := M.L_comm_apply 2 (-1) x
  norm_num at h
  linear_combination (norm := module) h

theorem L_one_negative_two (x : H) :
    M.L 1 (M.L (-2) x) = M.L (-2) (M.L 1 x) + (3 : ℂ) • M.L (-1) x := by
  have h := M.L_comm_apply 1 (-2) x
  norm_num at h
  linear_combination (norm := module) h

theorem L_two_negative_two (x : H) :
    M.L 2 (M.L (-2) x) = M.L (-2) (M.L 2 x) +
      (4 : ℂ) • M.L 0 x + (M.c / 2) • x := by
  have h := M.L_comm_apply 2 (-2) x
  norm_num at h
  linear_combination (norm := module) h

theorem L_one_negative_one_weight (N : ℤ) (x : H) (hx : x ∈ M.wt N) :
    M.L 1 (M.L (-1) x) = M.L (-1) (M.L 1 x) + (2 * (N : ℂ)) • x := by
  rw [M.L_one_negative_one, M.L_zero N x hx, smul_smul]

theorem L_one_negative_square_weight (N : ℤ) (x : H) (hx : x ∈ M.wt N) :
    M.L 1 (M.L (-1) (M.L (-1) x)) =
      M.L (-1) (M.L (-1) (M.L 1 x)) + (4 * (N : ℂ) + 2) • M.L (-1) x := by
  have hw : M.L (-1) x ∈ M.wt (N + 1) := by simpa using M.L_wt (-1) N x hx
  rw [M.L_one_negative_one_weight (N + 1) _ hw, M.L_one_negative_one_weight N x hx]
  simp only [map_add, map_smul, Int.cast_add, Int.cast_one]
  module

/-- Identity (i), at weight zero. -/
theorem L_one_negative_one_weight_zero (x : H) (hx : x ∈ M.wt 0) :
    M.L 1 (M.L (-1) x) = M.L (-1) (M.L 1 x) := by
  simpa using M.L_one_negative_one_weight 0 x hx

/-- Identity (ii), at weight zero. -/
theorem tildePositiveTwo_negative_one_weight_zero (x : H) (hx : x ∈ M.wt 0) :
    M.tildePositiveTwo (M.L (-1) x) = M.L (-1) (M.tildePositiveTwo x) := by
  have hw : M.L 1 x ∈ M.wt (-1) := by simpa using M.L_wt 1 0 x hx
  simp only [tildePositiveTwo, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply]
  rw [M.L_two_negative_one, M.L_one_negative_one_weight_zero x hx,
    M.L_one_negative_one_weight (-1) _ hw]
  simp only [map_add, map_smul]
  norm_num
  module

/-- Identity (iii), at weight minus one. -/
theorem L_one_tildeNegativeTwo_weight_neg_one (x : H) (hx : x ∈ M.wt (-1)) :
    M.L 1 (M.tildeNegativeTwo x) = M.tildeNegativeTwo (M.L 1 x) := by
  simp only [tildeNegativeTwo, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_add, map_smul]
  rw [M.L_one_negative_two, M.L_one_negative_square_weight (-1) x hx]
  norm_num
  module

theorem L_two_negative_square_weight_neg_one (x : H) (hx : x ∈ M.wt (-1)) :
    M.L 2 (M.L (-1) (M.L (-1) x)) = M.L (-1) (M.L (-1) (M.L 2 x)) +
      (6 : ℂ) • M.L (-1) (M.L 1 x) - (6 : ℂ) • x := by
  rw [M.L_two_negative_one, M.L_two_negative_one,
    M.L_one_negative_one_weight (-1) x hx]
  simp only [map_add, map_smul]
  norm_num
  module

theorem L_one_square_negative_two_weight_neg_one (x : H) (hx : x ∈ M.wt (-1)) :
    M.L 1 (M.L 1 (M.L (-2) x)) = M.L (-2) (M.L 1 (M.L 1 x)) +
      (6 : ℂ) • M.L (-1) (M.L 1 x) - (6 : ℂ) • x := by
  rw [M.L_one_negative_two]
  simp only [map_add, map_smul]
  rw [M.L_one_negative_two, M.L_one_negative_one_weight (-1) x hx]
  norm_num
  module

theorem L_one_square_negative_square_weight_neg_one (x : H) (hx : x ∈ M.wt (-1)) :
    M.L 1 (M.L 1 (M.L (-1) (M.L (-1) x))) =
      M.L (-1) (M.L (-1) (M.L 1 (M.L 1 x))) -
        (8 : ℂ) • M.L (-1) (M.L 1 x) + (4 : ℂ) • x := by
  have hw : M.L 1 x ∈ M.wt (-2) := by simpa using M.L_wt 1 (-1) x hx
  rw [M.L_one_negative_square_weight (-1) x hx]
  simp only [map_add, map_smul]
  rw [M.L_one_negative_square_weight (-2) _ hw, M.L_one_negative_one_weight (-1) x hx]
  norm_num
  module

/-- Identity (iv), including the precise central-charge defect. -/
theorem tildeTwo_commutator_weight_neg_one (x : H) (hx : x ∈ M.wt (-1)) :
    M.tildePositiveTwo (M.tildeNegativeTwo x) =
      M.tildeNegativeTwo (M.tildePositiveTwo x) + (M.c / 2 - 13) • x := by
  simp only [tildePositiveTwo, tildeNegativeTwo, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.mul_apply, map_add, map_smul]
  rw [M.L_two_negative_two, M.L_zero (-1) x hx,
    M.L_two_negative_square_weight_neg_one x hx,
    M.L_one_square_negative_two_weight_neg_one x hx,
    M.L_one_square_negative_square_weight_neg_one x hx]
  norm_num
  module

/-- At central charge 26 the modified modes commute on weight minus one. -/
theorem tildeTwo_critical_commute (hc : M.c = 26) (x : H) (hx : x ∈ M.wt (-1)) :
    M.tildePositiveTwo (M.tildeNegativeTwo x) =
      M.tildeNegativeTwo (M.tildePositiveTwo x) := by
  rw [M.tildeTwo_commutator_weight_neg_one x hx, hc]
  norm_num

end VOA.Moonshine.ConwayNorton.StringModule
