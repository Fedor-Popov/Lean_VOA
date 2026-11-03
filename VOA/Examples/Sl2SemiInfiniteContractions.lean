/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCurrents
import VOA.Examples.Sl2SemiInfiniteGhostEmbeddings

/-!
# Explicit ghost contractions

This file evaluates the genuine one-pair quadratic ghost field on its quadratic state.
The double pole is `+1` times the vacuum.  The sign is proved by the two Clifford
contractions and the minus sign in fermionic normal ordering.
-/

namespace VOA.Sl2SemiInfinite

open VOA.Ghost VOA.SympFerm
open Module (End)

/-- A basic ghost field cannot contract a level-zero word at exponent less than `-1`. -/
theorem ghField_lt_neg_one_zero (a : Fin 2) {j : ℤ} (hj : j < -1) (l : List (Fin 2)) :
    ghField a j (stWordSF (l.map fun b => ((0, b) : ℕ × Fin 2))) = 0 := by
  rw [ghField, if_neg (by omega)]
  change annBase (((-j - 1).toNat, a + 1) : ℕ × Fin 2)
    (stWordSF (l.map fun b => ((0, b) : ℕ × Fin 2))) = 0
  have hpos : (-j - 1).toNat ≠ 0 := by omega
  induction l with
  | nil => exact annBase_stWordSF_nil _
  | cons b l ih =>
    simp only [List.map_cons, annBase_stWordSF_cons, Prod.mk.injEq, hpos, false_and,
      if_false, zero_smul, ih, mul_zero, sub_zero]

/-- The word field of a single level-zero generator is the original ghost field. -/
theorem ghostWord_single_field (a : Fin 2) :
    YwordGh [((0, a) : ℕ × Fin 2)] = ghField a := by
  rw [YwordGh_cons]
  have hk : koszul 1 ((List.length ([] : SFWord) : ℕ) : ZMod 2) = 1 := by
    rw [List.length_nil, Nat.cast_zero, koszul_zero_right]
  rw [hk]
  trans ghGenField a 0
  · exact (nprodε_one _ _).trans (nprod_idField _)
  · simp [ghGenField]

/-- The one-pair quadratic state `b₍₋₁₎c`. -/
noncomputable def ghostPairQuadratic : FockSF :=
  stWordSF [((0, 0) : ℕ × Fin 2), ((0, 1) : ℕ × Fin 2)]

/-- The quadratic state is the genuine `(-1)`-product of the two ghost generators. -/
theorem ghostPairQuadratic_eq_product :
    mode (bcGhostSVA.Y (stWordSF [((0, 0) : ℕ × Fin 2)])) (-1)
      (stWordSF [((0, 1) : ℕ × Fin 2)]) = ghostPairQuadratic := by
  change YGh _ 0 _ = _
  rw [YGh_word, ghostWord_single_field, ghField, if_pos (by omega)]
  rfl

/-- The quadratic ghost state is even. -/
theorem ghostPairQuadratic_even : ghostPairQuadratic ∈ bcGhostSVA.parity 0 := by
  have h := stWordSF_mem_evenOdd
    [((0, 0) : ℕ × Fin 2), ((0, 1) : ℕ × Fin 2)]
  norm_num at h
  exact h

/-- Its reconstructed vertex field is the fermionic normal-ordered product `:bc:`. -/
theorem ghostPairQuadratic_field :
    YGh ghostPairQuadratic = nprodε (-1) (ghField_isField 0) (ghField_isField 1) := by
  rw [ghostPairQuadratic, YGh_word, YwordGh_cons]
  simp only [List.length_cons, List.length_nil, zero_add, Nat.cast_one, koszul_one_one]
  congr 1
  · simp [ghGenField]
  · exact ghostWord_single_field 1

/-- The actual quadratic ghost field has double pole `+1` on the quadratic state. -/
theorem ghostPairQuadratic_doublePole :
    mode (bcGhostSVA.Y ghostPairQuadratic) 1 ghostPairQuadratic = vacSF := by
  change YGh ghostPairQuadratic (-2) ghostPairQuadratic = vacSF
  rw [ghostPairQuadratic_field, nprodε_apply]
  rw [finsum_eq_single _ (-1)]
  · have hb : annBase (0,1) ghostPairQuadratic =
          -stWordSF [((0,0) : ℕ × Fin 2)] := by
      rw [ghostPairQuadratic, annBase_stWordSF_cons, annBase_stWordSF_cons,
        annBase_stWordSF_nil]
      norm_num [stWordSF_cons, stWordSF_nil]
    have hc : annBase (0,0) (stWordSF [((0,0) : ℕ × Fin 2)]) = vacSF := by
      rw [annBase_stWordSF_cons, annBase_stWordSF_nil]
      simp [stWordSF_nil]
    norm_num [normalOrderedε_apply, ghField, annGh, hb, hc,
      show (1 : Fin 2) + 1 = 0 from by decide, ← stWordSF_nil]
  · intro j hj
    rw [normalOrderedε_apply]
    split_ifs with hj0
    · have h := ghField_lt_neg_one_zero 1 (j := -2 - j) (by omega) [0, 1]
      simp only [List.map_cons, List.map_nil] at h
      change ghField 0 j (ghField 1 (-2 - j) _) = 0
      rw [ghostPairQuadratic, h, map_zero]
    · have h := ghField_lt_neg_one_zero 0 (j := j) (by omega) [0, 1]
      simp only [List.map_cons, List.map_nil] at h
      change (-1 : ℂ) • (ghField 1 (-2 - j) (ghField 0 j _)) = 0
      rw [ghostPairQuadratic, h, map_zero, smul_zero]

/-- The diagonal quadratic current is the unit embedding of the one-pair quadratic state. -/
theorem ghostBilinear_diagonal (a : Fin 3) :
    ghostBilinear a a = ghostEmbed a ghostPairQuadratic := by
  unfold ghostBilinear bGhost cGhost
  rw [ghostEmbed_mode]
  exact congrArg (ghostEmbed a) ghostPairQuadratic_eq_product

/-- Every diagonal pair contributes its actual double pole `+1`. -/
theorem ghostBilinear_diagonal_doublePole (a : Fin 3) :
    mode (sl2GhostSVA.Y (ghostBilinear a a)) 1 (ghostBilinear a a) =
      sl2GhostSVA.vacuum := by
  rw [ghostBilinear_diagonal, ghostEmbed_mode]
  exact (congrArg (ghostEmbed a) ghostPairQuadratic_doublePole).trans (ghostEmbed_vacuum a)

/-- Different diagonal quadratic currents have no double-pole contraction. -/
theorem ghostBilinear_diagonal_doublePole_of_ne {a b : Fin 3} (hab : a ≠ b) :
    mode (sl2GhostSVA.Y (ghostBilinear a a)) 1 (ghostBilinear b b) = 0 := by
  rw [ghostBilinear_diagonal, ghostBilinear_diagonal]
  exact ghostEmbed_mode_of_ne hab ghostPairQuadratic_even ghostPairQuadratic (by omega)

/-- The genuine Cartan ghost-current double pole is `8 = 4 κ(h,h)` times the vacuum.
This verifies the sign and normalisation of the level on the Cartan entry of the OPE. -/
theorem ghostCurrent_h_doublePole :
    mode (ghostCurrentField AffineVOA.colH) 1 (ghostCurrent AffineVOA.colH) =
      (4 * AffineVOA.kappa AffineVOA.colH AffineVOA.colH) • sl2GhostSVA.vacuum := by
  have h00 := ghostBilinear_diagonal_doublePole AffineVOA.colE
  have h11 := ghostBilinear_diagonal_doublePole AffineVOA.colF
  have h01 := ghostBilinear_diagonal_doublePole_of_ne
    (a := AffineVOA.colE) (b := AffineVOA.colF) (by decide)
  have h10 := ghostBilinear_diagonal_doublePole_of_ne
    (a := AffineVOA.colF) (b := AffineVOA.colE) (by decide)
  have hfield : sl2GhostSVA.Y (ghostCurrent AffineVOA.colH) (-2) =
      (2 : ℂ) • sl2GhostSVA.Y (ghostBilinear AffineVOA.colE AffineVOA.colE) (-2) -
      (2 : ℂ) • sl2GhostSVA.Y (ghostBilinear AffineVOA.colF AffineVOA.colF) (-2) := by
    rw [ghostCurrent_h, map_sub, map_smul, map_smul]
    rfl
  change sl2GhostSVA.Y (ghostCurrent AffineVOA.colH) (-2)
    (ghostCurrent AffineVOA.colH) = _
  rw [hfield, ghostCurrent_h]
  change sl2GhostSVA.Y _ (-2) _ = _ at h00 h11 h01 h10
  simp only [map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, h00, h01, h10, h11]
  norm_num [AffineVOA.kappa]
  module

/-!
The full matrix-unit bilinear tables are proved in `Sl2SemiInfiniteBilinearProducts`.
Their sums give `ghostAffineAction` in `Sl2SemiInfiniteGhostAffine`, including every
integer-mode commutator at level `+4`. The Cartan calculation above remains a direct
check of the normalization, independent of that later assembly.
-/

end VOA.Sl2SemiInfinite
