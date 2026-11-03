/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteBilinearProducts

/-! # One-pair coefficients entering the cubic ghost self-product -/

namespace VOA.Sl2SemiInfinite

open Ghost SympFerm

/-- A high ghost annihilator also kills a contraction of a level-zero word.
The proof is the actual Clifford anticommutator. -/
theorem ghField_lower_ann_word (a b : Fin 2) (l : List (Fin 2))
    (j : ℤ) (hj : j < -1) :
    ghField a j (annBase (0, b) (ghostZeroWord l)) = 0 := by
  have hz := ghField_lower_word a l j hj
  rw [ghField, if_neg (by omega), annGh] at hz ⊢
  have h := annBase_anticomm (((-j - 1).toNat, a + 1) : ℕ × Fin 2)
    (0, b) (ghostZeroWord l)
  simpa only [hz, map_zero, add_zero] using h

/-- On level-zero words the quadratic ghost field has no coefficients below minus two. -/
theorem ghostQuadratic_lower_word (l : List (Fin 2)) (j : ℤ) (hj : j < -2) :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) j (ghostZeroWord l) = 0 := by
  change YGh ghostPairQuadratic j (ghostZeroWord l) = 0
  rw [ghostPairQuadratic_field, nprodε_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  rw [normalOrderedε_apply]
  split_ifs with hm
  · change ghField 0 m (ghField 1 (j - m) (ghostZeroWord l)) = 0
    rw [ghField_lower_word 1 l (j - m) (by omega), map_zero]
  · change (-1 : ℂ) • ghField 1 (j - m) (ghField 0 m (ghostZeroWord l)) = 0
    by_cases hm1 : m = -1
    · subst m
      rw [ghField_negOne_word]
      norm_num only
      rw [ghField_lower_ann_word 1 (0 + 1) l (j - -1) (by omega), smul_zero]
    · rw [ghField_lower_word 0 l m (by omega), map_zero, smul_zero]

/-- The regular coefficient of `:bc:` on a level-zero word has one
creation term and two derivative-contraction terms. -/
theorem ghostQuadratic_zero_word (l : List (Fin 2)) :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) 0 (ghostZeroWord l) =
      creBase (0, 0) (creBase (0, 1) (ghostZeroWord l)) +
      creBase (1, 0) (annBase (0, 0) (ghostZeroWord l)) -
      creBase (1, 1) (annBase (0, 1) (ghostZeroWord l)) := by
  change YGh ghostPairQuadratic 0 (ghostZeroWord l) = _
  rw [ghostPairQuadratic_field, nprodε_apply]
  rw [finsum_eq_sum_of_support_subset _ (s := {-1, 0, 1})]
  · norm_num [normalOrderedε_apply, ghField, annGh, creGh,
      show (1 : Fin 2) + 1 = 0 from by decide]
    abel
  · intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    apply hm
    rw [normalOrderedε_apply]
    split_ifs with hm0
    · change ghField 0 m (ghField 1 (0 - m) (ghostZeroWord l)) = 0
      rw [ghField_lower_word 1 l (0 - m) (by omega), map_zero]
    · change (-1 : ℂ) • ghField 1 (0 - m) (ghField 0 m (ghostZeroWord l)) = 0
      rw [ghField_lower_word 0 l m (by omega), map_zero, smul_zero]

/-- Three level-zero creators with a repeated species vanish. -/
theorem ghostZeroWord_repeat_tail (a : Fin 2) (l : List (Fin 2)) :
    ghostZeroWord (a :: a :: l) = 0 := by
  have h := creBase_anticomm (0, a) (0, a) (ghostZeroWord l)
  change ghostZeroWord (a :: a :: l) + ghostZeroWord (a :: a :: l) = 0 at h
  have h' : (2 : ℂ) • ghostZeroWord (a :: a :: l) = 0 := by simpa [two_smul] using h
  exact (smul_eq_zero.mp h').resolve_left (by norm_num)

/-- Interchanging adjacent creators changes the sign, including in longer words. -/
theorem ghostZeroWord_swap (a b : Fin 2) (l : List (Fin 2)) :
    ghostZeroWord (a :: b :: l) = -ghostZeroWord (b :: a :: l) := by
  have h := creBase_anticomm (0, a) (0, b) (ghostZeroWord l)
  change ghostZeroWord (a :: b :: l) + ghostZeroWord (b :: a :: l) = 0 at h
  exact eq_neg_of_add_eq_zero_left h

/-- A repeated creator at the tail of a word still gives zero. -/
theorem ghostZeroWord_repeat_end (a b : Fin 2) : ghostZeroWord [a, b, b] = 0 := by
  change creBase (0, a) (ghostZeroWord [b, b]) = 0
  rw [ghostZeroWord_repeat, map_zero]

/-- The regular basic `c` coefficient kills the quadratic word. -/
theorem ghField_c_zero_quad : ghField 1 0 (ghostZeroWord [0, 1]) = 0 := by
  rw [ghField_zero_word, ghostZeroWord_swap 1 0 [1], ghostZeroWord_repeat_end, neg_zero]

/-- The regular basic `b` coefficient kills the quadratic word. -/
theorem ghField_b_zero_quad : ghField 0 0 (ghostZeroWord [0, 1]) = 0 := by
  rw [ghField_zero_word, ghostZeroWord_repeat_tail]

/-- The regular quadratic coefficient on `b` is its first derivative creator. -/
theorem ghostQuadratic_zero_b :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) 0 (ghostZeroWord [0]) =
      ghField 0 1 (ghostZeroWord []) := by
  rw [ghostQuadratic_zero_word]
  have hz : creBase (0, 0) (creBase (0, 1) (ghostZeroWord [0])) = 0 := by
    change ghostZeroWord [0, 1, 0] = 0
    rw [ghostZeroWord_swap 0 1 [0], ghostZeroWord_repeat_end, neg_zero]
  rw [hz]
  simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil,
    ghField, creGh, ← stWordSF_nil]

/-- The regular quadratic coefficient on `c` is minus its first derivative creator. -/
theorem ghostQuadratic_zero_c :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) 0 (ghostZeroWord [1]) =
      -ghField 1 1 (ghostZeroWord []) := by
  rw [ghostQuadratic_zero_word]
  have hz : creBase (0, 0) (creBase (0, 1) (ghostZeroWord [1])) = 0 := by
    change ghostZeroWord [0, 1, 1] = 0
    exact ghostZeroWord_repeat_end 0 1
  rw [hz]
  simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil,
    ghField, creGh, ← stWordSF_nil]

end VOA.Sl2SemiInfinite
