/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCubic
import VOA.Examples.Sl2SemiInfiniteCubicOnePair

/-! # Finite coefficient formulas for the cubic ghost field -/

namespace VOA.Sl2SemiInfinite

open Module (End)
open Ghost SympFerm
open scoped BigOperators TensorProduct

section Tensor
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- A double-pole factor and a simple-pole factor give three contributions to the residue. -/
theorem tenY_simplePole_of_lower_two_one
    (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (a x : A) (b y : B) {p q : ZMod 2} (hb : b ∈ W.parity p) (hx : x ∈ V.parity q)
    (hA : ∀ j : ℤ, j < -2 → V.Y a j x = 0)
    (hB : ∀ j : ℤ, j < -1 → W.Y b j y = 0) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] b) (-1) (x ⊗ₜ[ℂ] y) =
      koszul p q • ((V.Y a (-2) x ⊗ₜ[ℂ] W.Y b 1 y) +
        (V.Y a (-1) x ⊗ₜ[ℂ] W.Y b 0 y) +
        (V.Y a 0 x ⊗ₜ[ℂ] W.Y b (-1) y)) := by
  rw [tenY_tmul_homogeneous V W _ _ _ _ hb hx]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := {-2, -1, 0})]
  · norm_num
    abel
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    apply hj
    by_cases hj0 : j < -2
    · rw [hA j hj0, TensorProduct.zero_tmul]
    · rw [hB (-1 - j) (by omega), TensorProduct.tmul_zero]

end Tensor

/-- The quadratic current in the first pair acts only there. -/
theorem ghostPair_quad_left (l m : List (Fin 2)) (s : ℤ) :
    ghostPairSVA.Y (ghostZeroWord [0, 1] ⊗ₜ[ℂ] ghostZeroWord []) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      bcGhostSVA.Y (ghostZeroWord [0, 1]) s (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m :=
  tenY_left_ghostVac _ _ _ _ _

/-- The first cubic monomial, before specifying its input word. -/
theorem ghostTriple_qc_first_zero (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [0, 1] [] [1]) (-1) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) •
        (((bcGhostSVA.Y (ghostZeroWord [0, 1]) (-2) (ghostZeroWord l) ⊗ₜ[ℂ]
            ghostZeroWord m) ⊗ₜ[ℂ] ghField 1 1 (ghostZeroWord n)) +
        ((bcGhostSVA.Y (ghostZeroWord [0, 1]) (-1) (ghostZeroWord l) ⊗ₜ[ℂ]
            ghostZeroWord m) ⊗ₜ[ℂ] ghField 1 0 (ghostZeroWord n)) +
        ((bcGhostSVA.Y (ghostZeroWord [0, 1]) 0 (ghostZeroWord l) ⊗ₜ[ℂ]
            ghostZeroWord m) ⊗ₜ[ℂ] ghField 1 (-1) (ghostZeroWord n))) := by
  have hA : ∀ j : ℤ, j < -2 →
      ghostPairSVA.Y (ghostZeroWord [0, 1] ⊗ₜ[ℂ] ghostZeroWord []) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_quad_left, ghostQuadratic_lower_word l j hj, TensorProduct.zero_tmul]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ (-1) _ = _
  rw [tenY_simplePole_of_lower_two_one ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostPair_word_parity l m) hA (ghostSingle_lower 1 n)]
  simp only [ghostPair_quad_left, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- The second cubic monomial, before specifying its input word. -/
theorem ghostTriple_qc_second_zero (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [] [0, 1] [1]) (-1) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) •
        (((ghostZeroWord l ⊗ₜ[ℂ]
            bcGhostSVA.Y (ghostZeroWord [0, 1]) (-2) (ghostZeroWord m)) ⊗ₜ[ℂ]
          ghField 1 1 (ghostZeroWord n)) +
        ((ghostZeroWord l ⊗ₜ[ℂ]
            bcGhostSVA.Y (ghostZeroWord [0, 1]) (-1) (ghostZeroWord m)) ⊗ₜ[ℂ]
          ghField 1 0 (ghostZeroWord n)) +
        ((ghostZeroWord l ⊗ₜ[ℂ]
            bcGhostSVA.Y (ghostZeroWord [0, 1]) 0 (ghostZeroWord m)) ⊗ₜ[ℂ]
          ghField 1 (-1) (ghostZeroWord n))) := by
  have hA : ∀ j : ℤ, j < -2 →
      ghostPairSVA.Y (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [0, 1]) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_quad_right, ghostQuadratic_lower_word m j hj, TensorProduct.tmul_zero]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ (-1) _ = _
  rw [tenY_simplePole_of_lower_two_one ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostPair_word_parity l m) hA (ghostSingle_lower 1 n)]
  simp only [ghostPair_quad_right, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- The two-ghost field has no pole of order greater than two on a level-zero word. -/
theorem ghostPair_cc_lower (l m : List (Fin 2)) (s : ℤ) (hs : s < -2) :
    ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
  change TensorVA.tenY bcGhostSVA bcGhostSVA _ s _ = _
  rw [tenY_tmul_homogeneous bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostZeroWord_parity l)]
  have hz : (∑ᶠ j : ℤ, bcGhostSVA.Y (ghostZeroWord [1]) j (ghostZeroWord l) ⊗ₜ[ℂ]
      bcGhostSVA.Y (ghostZeroWord [1]) (s - j) (ghostZeroWord m)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < -1
    · rw [ghostSingle_lower 1 l j hj, TensorProduct.zero_tmul]
    · rw [ghostSingle_lower 1 m (s - j) (by omega), TensorProduct.tmul_zero]
  rw [hz, smul_zero]

/-- The double coefficient of the two-ghost field. -/
theorem ghostPair_cc_double (l m : List (Fin 2)) :
    ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) (-2)
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      koszul 1 (l.length : ZMod 2) •
        (ghField 1 (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 (-1) (ghostZeroWord m)) := by
  change TensorVA.tenY bcGhostSVA bcGhostSVA _ (-2) _ = _
  rw [tenY_doublePole_of_lower bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostZeroWord_parity l)
    (ghostSingle_lower 1 l) (ghostSingle_lower 1 m)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add]

/-- The simple coefficient of the two-ghost field. -/
theorem ghostPair_cc_simple (l m : List (Fin 2)) :
    ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) (-1)
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      koszul 1 (l.length : ZMod 2) •
        ((ghField 1 (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 0 (ghostZeroWord m)) +
          (ghField 1 0 (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 (-1) (ghostZeroWord m))) := by
  change TensorVA.tenY bcGhostSVA bcGhostSVA _ (-1) _ = _
  rw [tenY_simplePole_of_lower bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostZeroWord_parity l)
    (ghostSingle_lower 1 l) (ghostSingle_lower 1 m)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add]

/-- The regular coefficient of the two-ghost field retains the first derivatives. -/
theorem ghostPair_cc_regular (l m : List (Fin 2)) :
    ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) 0
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      koszul 1 (l.length : ZMod 2) •
        ((ghField 1 (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 1 (ghostZeroWord m)) +
          (ghField 1 0 (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 0 (ghostZeroWord m)) +
          (ghField 1 1 (ghostZeroWord l) ⊗ₜ[ℂ] ghField 1 (-1) (ghostZeroWord m))) := by
  change TensorVA.tenY bcGhostSVA bcGhostSVA _ 0 _ = _
  rw [tenY_tmul_homogeneous bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [1]) (ghostZeroWord_parity l)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := {-1, 0, 1})]
  · norm_num
    abel
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    apply hj
    by_cases hj0 : j < -1
    · rw [ghField_lower_word 1 l j hj0, TensorProduct.zero_tmul]
    · rw [ghField_lower_word 1 m (0 - j) (by omega), TensorProduct.tmul_zero]

/-- The remaining cubic monomial has three finite tensor-contraction contributions. -/
theorem ghostTriple_ccb_zero (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [1] [1] [0]) (-1) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) •
        ((ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) (-2)
            (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
          ghField 0 1 (ghostZeroWord n)) +
        (ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) (-1)
            (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
          ghField 0 0 (ghostZeroWord n)) +
        (ghostPairSVA.Y (ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [1]) 0
            (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
          ghField 0 (-1) (ghostZeroWord n))) := by
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ (-1) _ = _
  rw [tenY_simplePole_of_lower_two_one ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [0]) (ghostPair_word_parity l m)
    (ghostPair_cc_lower l m) (ghostSingle_lower 0 n)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add]

/-- Scalar multiplication of formal distributions is coefficientwise. -/
theorem formalDist_smul_coeff {A : Type*} [AddCommGroup A] [Module ℂ A]
    (r : ℂ) (F : FormalDist (Module.End ℂ A)) (s : ℤ) :
    (r • F) s = r • F s := rfl

/-- Subtraction of formal distributions is coefficientwise. -/
theorem formalDist_sub_coeff {A : Type*} [AddCommGroup A] [Module ℂ A]
    (F G : FormalDist (Module.End ℂ A)) (s : ℤ) :
    (F - G) s = F s - G s := rfl

set_option maxHeartbeats 1600000 in
-- Nine cubic tensor products, each reduced to at most six one-pair contractions.
/-- The cubic self-residue is the explicit derivative-ghost anomaly. -/
theorem ghostBRSTState_zero_self_tensor :
    mode (sl2GhostSVA.Y ghostBRSTState) 0 ghostBRSTState =
      (4 : ℂ) • ((ghField 1 1 (ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ]
        ghostZeroWord []) -
      (4 : ℂ) • ((ghostZeroWord [1] ⊗ₜ[ℂ] ghField 1 1 (ghostZeroWord [])) ⊗ₜ[ℂ]
        ghostZeroWord []) +
      (8 : ℂ) • ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ]
        ghField 1 1 (ghostZeroWord [1])) := by
  simp only [ghostBRSTState_tensor, mode_apply, neg_zero, zero_sub,
    map_sub, map_smul, formalDist_smul_coeff, formalDist_sub_coeff,
    LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [ghostTriple_qc_first_zero, ghostTriple_qc_second_zero, ghostTriple_ccb_zero,
    ghostPair_cc_double, ghostPair_cc_simple, ghostPair_cc_regular]
  simp only [ghField_c_zero_quad]
  simp only [ghostQuadratic_zero_c,
    ghostQuadratic_simple_nil, ghostQuadratic_simple_single, ghostQuadratic_simple_pair,
    ghostQuadratic_double_nil, ghostQuadratic_double_single, ghostQuadratic_double_pair,
    ghField_negOne_nil, ghField_negOne_single, ghField_negOne_pair,
    ghField_zero_word, ghostZeroWord_repeat, ghostZeroWord_cb]
  norm_num [koszul_one_two, show (1 : Fin 2) + 1 = 0 by decide,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, TensorProduct.add_tmul,
    TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  module

end VOA.Sl2SemiInfinite
