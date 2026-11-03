/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCharge
import VOA.Examples.Sl2SemiInfiniteBilinearProducts

/-! # Explicit tensor coordinates for the cubic ghost correction -/

namespace VOA.Sl2SemiInfinite

open Module (End)
open Ghost SympFerm AffineVOA
open scoped BigOperators TensorProduct

/-- A ghost coefficient in the first pair acts in that factor. -/
theorem cGhost_first_triple (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (cGhost 0) s (ghostTripleWord l m n) =
      (ghField 1 s (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) s
    ((ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n) = _
  rw [tenY_left_ghostVac, ghostPair_single_left]

/-- A ghost coefficient in the second pair includes the first-pair parity. -/
theorem cGhost_second_triple (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (cGhost 1) s (ghostTripleWord l m n) =
      koszul 1 (l.length : ZMod 2) •
        ((ghostZeroWord l ⊗ₜ[ℂ] ghField 1 s (ghostZeroWord m)) ⊗ₜ[ℂ] ghostZeroWord n) := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord []) s
    ((ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n) = _
  rw [tenY_left_ghostVac, ghostPair_single_right, ← TensorProduct.smul_tmul']

/-- A ghost coefficient in the third pair includes the preceding parity. -/
theorem cGhost_last_triple (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (cGhost 2) s (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) •
        ((ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
          ghField 1 s (ghostZeroWord n)) :=
  tenY_last_unit_word 1 l m n s

theorem ghostTripleWord_cb_left (m n : List (Fin 2)) :
    ghostTripleWord [1, 0] m n = -ghostTripleWord [0, 1] m n := by
  simp only [ghostTripleWord, ghostZeroWord_cb, TensorProduct.neg_tmul]

theorem ghostTripleWord_cb_middle (l n : List (Fin 2)) :
    ghostTripleWord l [1, 0] n = -ghostTripleWord l [0, 1] n := by
  simp only [ghostTripleWord, ghostZeroWord_cb, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

set_option maxHeartbeats 800000 in
-- Expanding the three Chevalley currents leaves six exterior tensor products.
/-- The actual cubic state has three exterior tensor monomials. -/
theorem ghostBRSTState_tensor :
    ghostBRSTState =
      (2 : ℂ) • ghostTripleWord [0, 1] [] [1] -
      (2 : ℂ) • ghostTripleWord [] [0, 1] [1] -
      ghostTripleWord [1] [1] [0] := by
  unfold ghostBRSTState
  rw [Fin.sum_univ_three]
  change (1 / 2 : ℂ) •
    (sl2GhostSVA.Y (cGhost colE) 0 (ghostCurrent colE) +
      sl2GhostSVA.Y (cGhost colF) 0 (ghostCurrent colF) +
      sl2GhostSVA.Y (cGhost colH) 0 (ghostCurrent colH)) = _
  rw [ghostCurrent_e, ghostCurrent_f, ghostCurrent_h]
  simp only [map_sub, map_smul, ghostBilinear_tensor]
  norm_num only [colE, colF, colH, Fin.val_zero, Fin.val_one, Fin.reduceFinMk]
  simp only [cGhost_first_triple, cGhost_second_triple, cGhost_last_triple,
    ghField_zero_word, map_neg]
  norm_num only [List.length_cons, List.length_nil, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zero_add, add_zero, koszul_one_one, koszul_zero_right,
    koszul_one_two, neg_one_smul, one_smul, TensorProduct.neg_tmul, neg_neg]
  change (1 / 2 : ℂ) •
    (-ghostTripleWord [1] [1] [0] - (2 : ℂ) • ghostTripleWord [1, 0] [] [1] +
      ((2 : ℂ) • ghostTripleWord [] [1, 0] [1] - ghostTripleWord [1] [1] [0]) +
      ((2 : ℂ) • ghostTripleWord [0, 1] [] [1] -
        (2 : ℂ) • ghostTripleWord [] [0, 1] [1])) = _
  rw [ghostTripleWord_cb_left, ghostTripleWord_cb_middle]
  module

end VOA.Sl2SemiInfinite
