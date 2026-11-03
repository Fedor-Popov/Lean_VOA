/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteContractions

/-! # Singular products of the quadratic three-pair ghost currents -/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct BigOperators
open Ghost SympFerm

/-- A word made from level-zero creation operators in one ghost pair. -/
noncomputable def ghostZeroWord (l : List (Fin 2)) : FockSF :=
  stWordSF (l.map fun a => ((0, a) : ℕ × Fin 2))

/-- On a level-zero word the simple pole of `:bc:` is the difference of the
occupation operators. This formula is derived from fermionic normal ordering. -/
theorem ghostPairQuadratic_simplePole_word (l : List (Fin 2)) :
    YGh ghostPairQuadratic (-1) (ghostZeroWord l) =
      creBase (0, 0) (annBase (0, 0) (ghostZeroWord l)) -
      creBase (0, 1) (annBase (0, 1) (ghostZeroWord l)) := by
  rw [ghostPairQuadratic_field, nprodε_apply]
  rw [finsum_eq_sum_of_support_subset _ (s := {-1, 0})]
  · norm_num [normalOrderedε_apply, ghField, annGh, creGh,
      show (1 : Fin 2) + 1 = 0 from by decide]
    abel
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push_neg at hn
    apply hj
    rw [normalOrderedε_apply]
    split_ifs with hj0
    · have hz := ghField_lt_neg_one_zero 1 (j := -1 - j) (by omega) l
      change ghField 0 j (ghField 1 (-1 - j) _) = 0
      rw [ghostZeroWord, hz, map_zero]
    · have hz := ghField_lt_neg_one_zero 0 (j := j) (by omega) l
      change (-1 : ℂ) • ghField 1 (-1 - j) (ghField 0 j _) = 0
      rw [ghostZeroWord, hz, map_zero, smul_zero]

/-- The simple pole of the one-pair diagonal current with itself vanishes. -/
theorem ghostPairQuadratic_simplePole :
    mode (bcGhostSVA.Y ghostPairQuadratic) 0 ghostPairQuadratic = 0 := by
  change YGh ghostPairQuadratic (-1) (ghostZeroWord [0, 1]) = 0
  rw [ghostPairQuadratic_simplePole_word]
  simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil,
    creBase_stWordSF, ← stWordSF_nil, ← stWordSF_cons]
  exact creBase_anticomm (0, 0) (0, 1) vacSF

/-- Diagonal currents in the same ghost pair have zero simple pole. -/
theorem ghostBilinear_diagonal_simplePole (a : Fin 3) :
    mode (sl2GhostSVA.Y (ghostBilinear a a)) 0 (ghostBilinear a a) = 0 := by
  rw [ghostBilinear_diagonal, ghostEmbed_mode]
  change ghostEmbed a (mode (bcGhostSVA.Y ghostPairQuadratic) 0 ghostPairQuadratic) = 0
  rw [ghostPairQuadratic_simplePole, ghostEmbed_zero]

/-- Diagonal currents in distinct pairs have zero simple pole. -/
theorem ghostBilinear_diagonal_simplePole_of_ne {a b : Fin 3} (hab : a ≠ b) :
    mode (sl2GhostSVA.Y (ghostBilinear a a)) 0 (ghostBilinear b b) = 0 := by
  rw [ghostBilinear_diagonal, ghostBilinear_diagonal]
  exact ghostEmbed_mode_of_ne hab ghostPairQuadratic_even ghostPairQuadratic (by omega)

section TensorCoefficients

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- Coefficients of a tensor field on homogeneous pure tensors, with its Koszul sign explicit. -/
theorem tenY_tmul_homogeneous (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (a x : A) (b y : B) {p q : ZMod 2} (hb : b ∈ W.parity p) (hx : x ∈ V.parity q)
    (s : ℤ) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] b) s (x ⊗ₜ[ℂ] y) =
      koszul p q • ∑ᶠ j : ℤ, V.Y a j x ⊗ₜ[ℂ] W.Y b (s - j) y := by
  rw [TensorVA.tenY_tmul_parity V W a hb, TensorVA.kappaTen_tmul,
    (TensorVA.parGr V).koszulOp_homog p hx,
    ← TensorProduct.smul_tmul', map_smul, TensorVA.rawCoeff_tmul]

/-- A right-factor field on homogeneous tensors. -/
theorem tenY_right_unit_homogeneous (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (x : A) (b y : B) {p q : ZMod 2} (hb : b ∈ W.parity p) (hx : x ∈ V.parity q)
    (s : ℤ) :
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] b) s (x ⊗ₜ[ℂ] y) =
      koszul p q • (x ⊗ₜ[ℂ] W.Y b s y) := by
  rw [tenY_tmul_homogeneous V W _ _ _ _ hb hx]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]

/-- Two fields with at most a simple pole on the chosen inputs give two
single-contraction terms in the tensor simple pole. -/
theorem tenY_simplePole_of_lower (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (a x : A) (b y : B) {p q : ZMod 2} (hb : b ∈ W.parity p) (hx : x ∈ V.parity q)
    (hA : ∀ j : ℤ, j < -1 → V.Y a j x = 0)
    (hB : ∀ j : ℤ, j < -1 → W.Y b j y = 0) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] b) (-1) (x ⊗ₜ[ℂ] y) =
      koszul p q • ((V.Y a (-1) x ⊗ₜ[ℂ] W.Y b 0 y) +
        (V.Y a 0 x ⊗ₜ[ℂ] W.Y b (-1) y)) := by
  rw [tenY_tmul_homogeneous V W _ _ _ _ hb hx]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := {-1, 0})]
  · norm_num
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    apply hj
    by_cases hj0 : j < -1
    · rw [hA j hj0, TensorProduct.zero_tmul]
    · rw [hB (-1 - j) (by omega), TensorProduct.tmul_zero]

/-- The tensor double pole is the double contraction. -/
theorem tenY_doublePole_of_lower (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (a x : A) (b y : B) {p q : ZMod 2} (hb : b ∈ W.parity p) (hx : x ∈ V.parity q)
    (hA : ∀ j : ℤ, j < -1 → V.Y a j x = 0)
    (hB : ∀ j : ℤ, j < -1 → W.Y b j y = 0) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] b) (-2) (x ⊗ₜ[ℂ] y) =
      koszul p q • (V.Y a (-1) x ⊗ₜ[ℂ] W.Y b (-1) y) := by
  rw [tenY_tmul_homogeneous V W _ _ _ _ hb hx]
  rw [finsum_eq_single _ (-1)]
  · norm_num
  · intro j hj
    by_cases hj0 : j < -1
    · rw [hA j hj0, TensorProduct.zero_tmul]
    · rw [hB (-2 - j) (by omega), TensorProduct.tmul_zero]

end TensorCoefficients

/-- A level-zero word has its length parity. -/
theorem ghostZeroWord_parity (l : List (Fin 2)) :
    ghostZeroWord l ∈ bcGhostSVA.parity (l.length : ZMod 2) := by
  simpa only [List.length_map] using stWordSF_mem_evenOdd
    (l.map fun a => ((0, a) : ℕ × Fin 2))

/-- A singleton word has the basic ghost field. -/
theorem ghostZeroWord_single_field (a : Fin 2) :
    bcGhostSVA.Y (ghostZeroWord [a]) = ghField a := by
  change YGh (stWordSF [((0, a) : ℕ × Fin 2)]) = ghField a
  rw [YGh_word, ghostWord_single_field]

/-- The quadratic ghost state as a level-zero word. -/
theorem ghostPairQuadratic_eq_zeroWord : ghostPairQuadratic = ghostZeroWord [0, 1] := rfl

/-- Creation by the basic ghost at coefficient zero. -/
theorem ghField_zero_word (a : Fin 2) (l : List (Fin 2)) :
    ghField a 0 (ghostZeroWord l) = ghostZeroWord (a :: l) := by
  change creBase (0, a) (stWordSF _) = _
  exact creBase_stWordSF _ _

/-- The coefficient minus one is the conjugate-species contraction. -/
theorem ghField_negOne_word (a : Fin 2) (l : List (Fin 2)) :
    ghField a (-1) (ghostZeroWord l) = annBase (0, a + 1) (ghostZeroWord l) := rfl

/-- Reversing the two distinct level-zero generators changes the sign. -/
theorem ghostZeroWord_cb : ghostZeroWord [1, 0] = -ghostZeroWord [0, 1] := by
  have h := creBase_anticomm (0, 1) (0, 0) vacSF
  change ghostZeroWord [1, 0] + ghostZeroWord [0, 1] = 0 at h
  exact eq_neg_of_add_eq_zero_left h

/-- Repeated level-zero generators give zero. -/
theorem ghostZeroWord_repeat (a : Fin 2) : ghostZeroWord [a, a] = 0 := by
  have h := creBase_anticomm (0, a) (0, a) vacSF
  change ghostZeroWord [a, a] + ghostZeroWord [a, a] = 0 at h
  have h' : (2 : ℂ) • ghostZeroWord [a, a] = 0 := by simpa [two_smul] using h
  exact (smul_eq_zero.mp h').resolve_left (by norm_num)

/-- A quadratic ghost field has only the double-annihilation contribution at exponent minus two. -/
theorem ghostPairQuadratic_doublePole_word (l : List (Fin 2)) :
    YGh ghostPairQuadratic (-2) (ghostZeroWord l) =
      -annBase (0, 0) (annBase (0, 1) (ghostZeroWord l)) := by
  rw [ghostPairQuadratic_field, nprodε_apply]
  rw [finsum_eq_single _ (-1)]
  · norm_num [normalOrderedε_apply, ghField, annGh,
      show (1 : Fin 2) + 1 = 0 from by decide]
  · intro j hj
    rw [normalOrderedε_apply]
    split_ifs with hj0
    · have hz := ghField_lt_neg_one_zero 1 (j := -2 - j) (by omega) l
      change ghField 0 j (ghField 1 (-2 - j) _) = 0
      rw [ghostZeroWord, hz, map_zero]
    · have hz := ghField_lt_neg_one_zero 0 (j := j) (by omega) l
      change (-1 : ℂ) • ghField 1 (-2 - j) (ghField 0 j _) = 0
      rw [ghostZeroWord, hz, map_zero, smul_zero]

/-- A level-zero word in the three ordered ghost pairs. -/
noncomputable def ghostTripleWord (l m n : List (Fin 2)) : Sl2GhostSpace :=
  (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n

/-- A vacuum in the right ghost factor leaves only the left field. -/
theorem tenY_left_ghostVac {A : Type*} [AddCommGroup A] [Module ℂ A]
    (V : SuperVertexAlgebra A) (a x : A) (y : FockSF) (s : ℤ) :
    TensorVA.tenY V bcGhostSVA (a ⊗ₜ[ℂ] ghostZeroWord []) s (x ⊗ₜ[ℂ] y) =
      V.Y a s x ⊗ₜ[ℂ] y := tenY_left_unit V bcGhostSVA a x y s

/-- A singleton in the last ghost pair acts with the preceding word parity. -/
theorem tenY_last_unit_word (a : Fin 2) (l m n : List (Fin 2)) (s : ℤ) :
    TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [a]) s
      ((ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) •
        ((ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
          ghField a s (ghostZeroWord n)) := by
  have hp : (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ∈
      ghostPairSVA.parity ((l.length : ZMod 2) + (m.length : ZMod 2)) :=
    by
      apply TensorVA.tmul_mem_tenParity bcGhostSVA bcGhostSVA (ghostZeroWord_parity l)
      simpa using ghostZeroWord_parity m
  have h := tenY_right_unit_homogeneous ghostPairSVA bcGhostSVA
    (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) (ghostZeroWord [a]) (ghostZeroWord n)
    (ghostZeroWord_parity [a]) hp s
  simpa only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add] using h

/-- A singleton unit field in the right factor, including the parity sign. -/
theorem tenY_right_unit_word (a : Fin 2) (l m : List (Fin 2)) (s : ℤ) :
    TensorVA.tenY bcGhostSVA bcGhostSVA
      (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [a]) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      koszul 1 (l.length : ZMod 2) •
        (ghostZeroWord l ⊗ₜ[ℂ] ghField a s (ghostZeroWord m)) := by
  have h := tenY_right_unit_homogeneous bcGhostSVA bcGhostSVA
    (ghostZeroWord l) (ghostZeroWord [a]) (ghostZeroWord m)
    (ghostZeroWord_parity [a]) (ghostZeroWord_parity l) s
  simpa only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add] using h

set_option maxHeartbeats 800000 in
/-- Explicit exterior tensor representative of every quadratic ghost state. -/
theorem ghostBilinear_tensor (c b : Fin 3) : ghostBilinear c b =
    match c.val, b.val with
    | 0, 0 => ghostTripleWord [0, 1] [] []
    | 0, 1 => ghostTripleWord [0] [1] []
    | 0, _ => ghostTripleWord [0] [] [1]
    | 1, 0 => -ghostTripleWord [1] [0] []
    | 1, 1 => ghostTripleWord [] [0, 1] []
    | 1, _ => ghostTripleWord [] [0] [1]
    | _, 0 => -ghostTripleWord [1] [] [0]
    | _, 1 => -ghostTripleWord [] [1] [0]
    | _, _ => ghostTripleWord [] [] [0, 1] := by
  fin_cases c <;> fin_cases b
  · rw [ghostBilinear_diagonal]
    rfl
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [0] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) 0
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord []) = ((ghostZeroWord [0] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord [])
    rw [tenY_left_ghostVac ghostPairSVA]
    change (TensorVA.tenY bcGhostSVA bcGhostSVA _ 0 _ ⊗ₜ[ℂ] _) = _
    rw [tenY_left_ghostVac bcGhostSVA, ghostZeroWord_single_field, ghField_zero_word]
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [0] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) 0
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) = ((ghostZeroWord [0] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1])
    rw [tenY_left_ghostVac ghostPairSVA]
    change (TensorVA.tenY bcGhostSVA bcGhostSVA _ 0 _ ⊗ₜ[ℂ] _) = _
    rw [tenY_left_ghostVac bcGhostSVA, ghostZeroWord_single_field, ghField_zero_word]
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [0]) ⊗ₜ[ℂ] ghostZeroWord []) 0
      ((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) = -((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord [0]) ⊗ₜ[ℂ] ghostZeroWord [])
    rw [tenY_left_ghostVac ghostPairSVA]
    change (TensorVA.tenY bcGhostSVA bcGhostSVA _ 0 _ ⊗ₜ[ℂ] _) = _
    rw [tenY_right_unit_word, ghField_zero_word]
    norm_num [TensorProduct.neg_tmul]
  · rw [ghostBilinear_diagonal]
    rfl
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [0]) ⊗ₜ[ℂ] ghostZeroWord []) 0
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) = ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [0]) ⊗ₜ[ℂ] ghostZeroWord [1])
    rw [tenY_left_ghostVac ghostPairSVA]
    change (TensorVA.tenY bcGhostSVA bcGhostSVA _ 0 _ ⊗ₜ[ℂ] _) = _
    rw [tenY_right_unit_word, ghField_zero_word]
    norm_num [TensorProduct.neg_tmul]
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [0]) 0
      ((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) = -((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [0])
    rw [tenY_last_unit_word, ghField_zero_word]
    norm_num
  · change TensorVA.tenY ghostPairSVA bcGhostSVA
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [0]) 0
      ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord []) = -((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord [0])
    rw [tenY_last_unit_word, ghField_zero_word]
    norm_num
  · rw [ghostBilinear_diagonal]
    rfl

/-- Basic contractions on the vacuum. -/
theorem ghField_negOne_nil (a : Fin 2) : ghField a (-1) (ghostZeroWord []) = 0 := by
  rw [ghField_negOne_word]
  exact annBase_stWordSF_nil _

/-- Basic contractions on one creation operator. -/
theorem ghField_negOne_single (a b : Fin 2) :
    ghField a (-1) (ghostZeroWord [b]) =
      if a + 1 = b then ghostZeroWord [] else 0 := by
  rw [ghField_negOne_word]
  simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil,
    ← stWordSF_nil]

/-- A basic contraction on the two-generator word. -/
theorem ghField_negOne_pair (a : Fin 2) :
    ghField a (-1) (ghostZeroWord [0, 1]) =
      if a = 0 then -ghostZeroWord [0] else ghostZeroWord [1] := by
  rw [ghField_negOne_word]
  fin_cases a <;> simp [ghostZeroWord,
    annBase_stWordSF_cons, annBase_stWordSF_nil, creBase_stWordSF,
    ← stWordSF_nil, ← stWordSF_cons]

/-- The quadratic zero mode kills the vacuum. -/
theorem ghostQuadratic_simple_nil :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-1) (ghostZeroWord []) = 0 := by
  change YGh ghostPairQuadratic (-1) (ghostZeroWord []) = 0
  rw [ghostPairQuadratic_simplePole_word]
  simp [ghostZeroWord, annBase_stWordSF_nil, ← stWordSF_nil]

/-- The quadratic zero mode gives opposite signs on the two species. -/
theorem ghostQuadratic_simple_single (a : Fin 2) :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-1) (ghostZeroWord [a]) =
      if a = 0 then ghostZeroWord [0] else -ghostZeroWord [1] := by
  change YGh ghostPairQuadratic (-1) (ghostZeroWord [a]) = _
  rw [ghostPairQuadratic_simplePole_word]
  fin_cases a <;> simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil,
    creBase_stWordSF, ← stWordSF_nil, ← stWordSF_cons]

/-- The quadratic zero mode kills the quadratic state. -/
theorem ghostQuadratic_simple_pair :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-1) (ghostZeroWord [0, 1]) = 0 :=
  ghostPairQuadratic_simplePole

/-- No double contraction is possible on the vacuum. -/
theorem ghostQuadratic_double_nil :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-2) (ghostZeroWord []) = 0 := by
  change YGh ghostPairQuadratic (-2) (ghostZeroWord []) = 0
  rw [ghostPairQuadratic_doublePole_word]
  simp [ghostZeroWord, annBase_stWordSF_nil, ← stWordSF_nil]

/-- No double contraction is possible on a singleton. -/
theorem ghostQuadratic_double_single (a : Fin 2) :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-2) (ghostZeroWord [a]) = 0 := by
  change YGh ghostPairQuadratic (-2) (ghostZeroWord [a]) = _
  rw [ghostPairQuadratic_doublePole_word]
  fin_cases a <;> simp [ghostZeroWord, annBase_stWordSF_cons, annBase_stWordSF_nil, ← stWordSF_nil]

/-- The diagonal double contraction has positive sign. -/
theorem ghostQuadratic_double_pair :
    bcGhostSVA.Y (ghostZeroWord [0, 1]) (-2) (ghostZeroWord [0, 1]) =
      ghostZeroWord [] := ghostPairQuadratic_doublePole

/-- The parity of a two-pair word is the sum of its factor lengths. -/
theorem ghostPair_word_parity (l m : List (Fin 2)) :
    ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m ∈
      ghostPairSVA.parity ((l.length : ZMod 2) + (m.length : ZMod 2)) :=
  by
    apply TensorVA.tmul_mem_tenParity bcGhostSVA bcGhostSVA (ghostZeroWord_parity l)
    simpa using ghostZeroWord_parity m

/-- A basic ghost cannot annihilate a higher level in a level-zero word. -/
theorem ghField_lower_word (a : Fin 2) (l : List (Fin 2)) (j : ℤ) (hj : j < -1) :
    ghField a j (ghostZeroWord l) = 0 := ghField_lt_neg_one_zero a hj l

/-- A singleton ghost has no coefficient below minus one on level-zero words. -/
theorem ghostSingle_lower (a : Fin 2) (l : List (Fin 2)) (j : ℤ) (hj : j < -1) :
    bcGhostSVA.Y (ghostZeroWord [a]) j (ghostZeroWord l) = 0 := by
  rw [ghostZeroWord_single_field]
  exact ghField_lt_neg_one_zero a hj l

/-- A singleton field in the first ghost pair. -/
theorem ghostPair_single_left (a : Fin 2) (l m : List (Fin 2)) (s : ℤ) :
    ghostPairSVA.Y (ghostZeroWord [a] ⊗ₜ[ℂ] ghostZeroWord []) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      ghField a s (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m := by
  change TensorVA.tenY bcGhostSVA bcGhostSVA _ s _ = _
  rw [tenY_left_ghostVac, ghostZeroWord_single_field]

/-- A singleton field in the second ghost pair. -/
theorem ghostPair_single_right (a : Fin 2) (l m : List (Fin 2)) (s : ℤ) :
    ghostPairSVA.Y (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [a]) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      koszul 1 (l.length : ZMod 2) •
        (ghostZeroWord l ⊗ₜ[ℂ] ghField a s (ghostZeroWord m)) :=
  tenY_right_unit_word a l m s

/-- The quadratic field in the second pair is even. -/
theorem ghostPair_quad_right (l m : List (Fin 2)) (s : ℤ) :
    ghostPairSVA.Y (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [0, 1]) s
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) =
      ghostZeroWord l ⊗ₜ[ℂ] bcGhostSVA.Y (ghostZeroWord [0, 1]) s (ghostZeroWord m) :=
  tenY_right_unit_even bcGhostSVA bcGhostSVA ghostPairQuadratic_even _ _ s

/-- The quadratic field in the first pair. -/
theorem ghostTriple_quad_first (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (ghostTripleWord [0, 1] [] []) s (ghostTripleWord l m n) =
      (bcGhostSVA.Y (ghostZeroWord [0, 1]) s (ghostZeroWord l) ⊗ₜ[ℂ]
        ghostZeroWord m) ⊗ₜ[ℂ] ghostZeroWord n := by
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ s _ = _
  rw [tenY_left_ghostVac]
  change (TensorVA.tenY bcGhostSVA bcGhostSVA _ s _ ⊗ₜ[ℂ] _) = _
  rw [tenY_left_ghostVac]

/-- The quadratic field in the second pair. -/
theorem ghostTriple_quad_second (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (ghostTripleWord [] [0, 1] []) s (ghostTripleWord l m n) =
      (ghostZeroWord l ⊗ₜ[ℂ]
        bcGhostSVA.Y (ghostZeroWord [0, 1]) s (ghostZeroWord m)) ⊗ₜ[ℂ] ghostZeroWord n := by
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ s _ = _
  rw [tenY_left_ghostVac, ghostPair_quad_right]

/-- The quadratic field in the last pair. -/
theorem ghostTriple_quad_last (l m n : List (Fin 2)) (s : ℤ) :
    sl2GhostSVA.Y (ghostTripleWord [] [] [0, 1]) s (ghostTripleWord l m n) =
      (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ]
        bcGhostSVA.Y (ghostZeroWord [0, 1]) s (ghostZeroWord n) :=
  tenY_right_unit_even ghostPairSVA bcGhostSVA ghostPairQuadratic_even _ _ s

/-- The simple pole of a quadratic field occupying firstTwo ghost pairs. -/
theorem ghostTriple_firstTwo_simple (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [a] [b] []) (-1) (ghostTripleWord l m n) =
      koszul 1 (l.length : ZMod 2) • (((ghField a (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghField b (0) (ghostZeroWord m)) ⊗ₜ[ℂ] ghostZeroWord n) + ((ghField a (0) (ghostZeroWord l) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord m)) ⊗ₜ[ℂ] ghostZeroWord n)) := by
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_left_ghostVac]
  change (TensorVA.tenY bcGhostSVA bcGhostSVA _ _ _ ⊗ₜ[ℂ] _) = _
  rw [tenY_simplePole_of_lower bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostZeroWord_parity l)
    (ghostSingle_lower a l) (ghostSingle_lower b m)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add, ← TensorProduct.smul_tmul', TensorProduct.add_tmul, smul_add]

/-- The double pole of a quadratic field occupying firstTwo ghost pairs. -/
theorem ghostTriple_firstTwo_double (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [a] [b] []) (-2) (ghostTripleWord l m n) =
      koszul 1 (l.length : ZMod 2) • ((ghField a (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord m)) ⊗ₜ[ℂ] ghostZeroWord n) := by
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_left_ghostVac]
  change (TensorVA.tenY bcGhostSVA bcGhostSVA _ _ _ ⊗ₜ[ℂ] _) = _
  rw [tenY_doublePole_of_lower bcGhostSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostZeroWord_parity l)
    (ghostSingle_lower a l) (ghostSingle_lower b m)]
  simp only [ghostZeroWord_single_field, List.length_cons, List.length_nil,
    Nat.cast_one, zero_add, ← TensorProduct.smul_tmul', TensorProduct.add_tmul, smul_add]

/-- The simple pole of a quadratic field occupying firstLast ghost pairs. -/
theorem ghostTriple_firstLast_simple (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [a] [] [b]) (-1) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) • (((ghField a (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghField b (0) (ghostZeroWord n)) + ((ghField a (0) (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord n))) := by
  have hA : ∀ j : ℤ, j < -1 →
      ghostPairSVA.Y (ghostZeroWord [a] ⊗ₜ[ℂ] ghostZeroWord []) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_single_left, ghField_lower_word a l j hj, TensorProduct.zero_tmul]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_simplePole_of_lower ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostPair_word_parity l m) hA (ghostSingle_lower b n)]
  simp only [ghostPair_single_left, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- The double pole of a quadratic field occupying firstLast ghost pairs. -/
theorem ghostTriple_firstLast_double (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [a] [] [b]) (-2) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) • ((ghField a (-1) (ghostZeroWord l) ⊗ₜ[ℂ] ghostZeroWord m) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord n)) := by
  have hA : ∀ j : ℤ, j < -1 →
      ghostPairSVA.Y (ghostZeroWord [a] ⊗ₜ[ℂ] ghostZeroWord []) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_single_left, ghField_lower_word a l j hj, TensorProduct.zero_tmul]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_doublePole_of_lower ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostPair_word_parity l m) hA (ghostSingle_lower b n)]
  simp only [ghostPair_single_left, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- The simple pole of a quadratic field occupying lastTwo ghost pairs. -/
theorem ghostTriple_lastTwo_simple (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [] [a] [b]) (-1) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) • (((koszul 1 (l.length : ZMod 2) • (ghostZeroWord l ⊗ₜ[ℂ] ghField a (-1) (ghostZeroWord m))) ⊗ₜ[ℂ] ghField b (0) (ghostZeroWord n)) + ((koszul 1 (l.length : ZMod 2) • (ghostZeroWord l ⊗ₜ[ℂ] ghField a (0) (ghostZeroWord m))) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord n))) := by
  have hA : ∀ j : ℤ, j < -1 →
      ghostPairSVA.Y (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [a]) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_single_right, ghField_lower_word a m j hj,
      TensorProduct.tmul_zero, smul_zero]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_simplePole_of_lower ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostPair_word_parity l m) hA (ghostSingle_lower b n)]
  simp only [ghostPair_single_right, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- The double pole of a quadratic field occupying lastTwo ghost pairs. -/
theorem ghostTriple_lastTwo_double (a b : Fin 2) (l m n : List (Fin 2)) :
    sl2GhostSVA.Y (ghostTripleWord [] [a] [b]) (-2) (ghostTripleWord l m n) =
      koszul 1 ((l.length : ZMod 2) + (m.length : ZMod 2)) • ((koszul 1 (l.length : ZMod 2) • (ghostZeroWord l ⊗ₜ[ℂ] ghField a (-1) (ghostZeroWord m))) ⊗ₜ[ℂ] ghField b (-1) (ghostZeroWord n)) := by
  have hA : ∀ j : ℤ, j < -1 →
      ghostPairSVA.Y (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [a]) j
        (ghostZeroWord l ⊗ₜ[ℂ] ghostZeroWord m) = 0 := by
    intro j hj
    rw [ghostPair_single_right, ghField_lower_word a m j hj,
      TensorProduct.tmul_zero, smul_zero]
  dsimp only [ghostTripleWord]
  change TensorVA.tenY ghostPairSVA bcGhostSVA _ _ _ = _
  rw [tenY_doublePole_of_lower ghostPairSVA bcGhostSVA _ _ _ _
    (ghostZeroWord_parity [b]) (ghostPair_word_parity l m) hA (ghostSingle_lower b n)]
  simp only [ghostPair_single_right, ghostZeroWord_single_field,
    List.length_cons, List.length_nil, Nat.cast_one, zero_add]

/-- Negation of formal distributions is coefficientwise. -/
theorem formalDist_neg_coeff {A : Type*} [AddCommGroup A] [Module ℂ A]
    (F : FormalDist (Module.End ℂ A)) (s : ℤ) : (-F) s = -(F s) := rfl

/-- Parity two is even. -/
theorem koszul_one_two : koszul 1 2 = 1 := by
  rw [show (2 : ZMod 2) = 0 from by decide, koszul_zero_right]

set_option maxHeartbeats 1600000 in
-- The four colour indices give eighty-one finite exterior-algebra identities.
/-- The simple-pole table of all nine matrix-unit ghost bilinears. -/
theorem ghostBilinear_simplePole (c b e d : Fin 3) :
    mode (sl2GhostSVA.Y (ghostBilinear c b)) 0 (ghostBilinear e d) =
      (if b = e then ghostBilinear c d else 0) -
      (if c = d then ghostBilinear e b else 0) := by
  fin_cases c <;> fin_cases b <;> fin_cases e <;> fin_cases d <;>
    norm_num [ghostBilinear_tensor, mode, formalDist_neg_coeff, LinearMap.neg_apply,
      koszul_one_two,
      ghostTriple_quad_first, ghostTriple_quad_second, ghostTriple_quad_last,
      ghostTriple_firstTwo_simple, ghostTriple_firstLast_simple, ghostTriple_lastTwo_simple,
      ghostQuadratic_simple_nil, ghostQuadratic_simple_single, ghostQuadratic_simple_pair,
      ghField_negOne_nil, ghField_negOne_single, ghField_negOne_pair,
      ghField_zero_word, ghostZeroWord_cb, ghostZeroWord_repeat,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  all_goals simp [ghostTripleWord, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
    sub_eq_add_neg, add_comm]

set_option maxHeartbeats 1600000 in
-- The four colour indices give eighty-one finite exterior-algebra identities.
/-- The double-pole table of all nine matrix-unit ghost bilinears. -/
theorem ghostBilinear_doublePole (c b e d : Fin 3) :
    mode (sl2GhostSVA.Y (ghostBilinear c b)) 1 (ghostBilinear e d) =
      if b = e ∧ c = d then sl2GhostSVA.vacuum else 0 := by
  fin_cases c <;> fin_cases b <;> fin_cases e <;> fin_cases d <;>
    norm_num [ghostBilinear_tensor, mode, formalDist_neg_coeff, LinearMap.neg_apply,
      koszul_one_two,
      ghostTriple_quad_first, ghostTriple_quad_second, ghostTriple_quad_last,
      ghostTriple_firstTwo_double, ghostTriple_firstLast_double, ghostTriple_lastTwo_double,
      ghostQuadratic_double_nil, ghostQuadratic_double_single, ghostQuadratic_double_pair,
      ghField_negOne_nil, ghField_negOne_single, ghField_negOne_pair,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  all_goals rfl

end VOA.Sl2SemiInfinite
