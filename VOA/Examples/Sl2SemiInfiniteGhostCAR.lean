/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteTranslation
import VOA.Examples.Sl2SemiInfiniteContractions

/-!
# Ghost anticommutators from actual state products

The three ghost states have weight zero. Their nonnegative state products vanish
by the nonnegative weight support, and translation covariance upgrades this to
the complete ghost-mode anticommutation relations.
-/

namespace VOA.Sl2SemiInfinite

/-- Every nonnegative product of two weight-zero ghosts vanishes. -/
theorem cGhost_nonneg_product (a b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (cGhost a)) n (cGhost b) = 0 := by
  have h := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a)
    (cGhost b) (cGhost_weight b) n
  have hbot : sl2GhostSVA.grading (0 + 0 - (n : ℂ) - 1) = ⊥ := by
    apply natSupported_sl2GhostSVA
    rintro ⟨m, hm⟩
    have hm' : ((m : ℤ) : ℂ) = ((-n - 1 : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have : (m : ℤ) = -n - 1 := by exact_mod_cast hm'
    omega
  rw [hbot] at h
  exact h

/-- All six-index choices of the actual `c` ghost modes anticommute. -/
theorem cGhost_modes_anticomm (a b : Fin 3) (m n : ℤ) :
    mode (sl2GhostSVA.Y (cGhost a)) m * mode (sl2GhostSVA.Y (cGhost b)) n
      + mode (sl2GhostSVA.Y (cGhost b)) n * mode (sl2GhostSVA.Y (cGhost a)) m = 0 := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound
    (cGhost_odd a) (cGhost_odd b) 0
    (fun j _ => cGhost_nonneg_product a b j (by omega)) m n
  simpa only [Finset.range_zero, Finset.sum_empty, koszul_one_one, neg_smul,
    one_smul, sub_neg_eq_add] using h

open scoped TensorProduct
open Module (End)

/-- A homogeneous right-factor field acts with the prescribed Koszul sign. -/
theorem tenY_right_unit_parity {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {p q : ZMod 2} {b : B} (hb : b ∈ W.parity p) {x : A} (hx : x ∈ V.parity q)
    (y : B) (s : ℤ) :
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] b) s (x ⊗ₜ[ℂ] y) =
      koszul p q • (x ⊗ₜ[ℂ] W.Y b s y) := by
  rw [TensorVA.tenY_tmul_parity V W _ hb, TensorVA.kappaTen_tmul,
    (TensorVA.parGr V).koszulOp_homog p hx,
    ← TensorProduct.smul_tmul', map_smul, TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]

/-- Fields embedded in distinct pairs have no singular products, including odd fields. -/
theorem ghostEmbed_Y_of_ne_parity {a b : Fin 3} (hab : a ≠ b)
    {p q : ZMod 2} {x y : SympFerm.FockSF}
    (hx : x ∈ Ghost.bcGhostSVA.parity p) (hy : y ∈ Ghost.bcGhostSVA.parity q)
    {s : ℤ} (hs : s < 0) : sl2GhostSVA.Y (ghostEmbed a x) s (ghostEmbed b y) = 0 := by
  have hyL : y ⊗ₜ[ℂ] SympFerm.vacSF ∈ ghostPairSVA.parity q := by
    change y ⊗ₜ[ℂ] SympFerm.vacSF ∈
      TensorVA.tenParity Ghost.bcGhostSVA Ghost.bcGhostSVA q
    apply TensorVA.tmul_mem_tenParity Ghost.bcGhostSVA Ghost.bcGhostSVA hy
    simpa only [sub_self] using Ghost.bcGhostSVA.vacuum_parity
  have hyR : SympFerm.vacSF ⊗ₜ[ℂ] y ∈ ghostPairSVA.parity q := by
    change SympFerm.vacSF ⊗ₜ[ℂ] y ∈
      TensorVA.tenParity Ghost.bcGhostSVA Ghost.bcGhostSVA q
    apply TensorVA.tmul_mem_tenParity Ghost.bcGhostSVA Ghost.bcGhostSVA
      Ghost.bcGhostSVA.vacuum_parity
    simpa only [sub_zero] using hy
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((SympFerm.vacSF ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SympFerm.vacSF) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (x ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SympFerm.vacSF = 0
    rw [tenY_left_unit, TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] y) = 0
    rw [tenY_left_unit, TensorVA.Ycoeff_vacuum_neg ghostPairSVA _ hs,
      TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] SympFerm.vacSF) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] x) s
      (y ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) ⊗ₜ[ℂ] SympFerm.vacSF = 0
    rw [tenY_right_unit_parity _ _ hx hy,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.tmul_zero, smul_zero, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] y) = 0
    rw [tenY_left_unit, TensorVA.Ycoeff_vacuum_neg ghostPairSVA _ hs,
      TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] x) s
      ((y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) = 0
    rw [tenY_right_unit_parity _ _ hx hyL,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.tmul_zero, smul_zero]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] x) s
      ((SympFerm.vacSF ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) = 0
    rw [tenY_right_unit_parity _ _ hx hyR,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.tmul_zero, smul_zero]

/-- The two species in any of the three actual ghost pairs (`0 = b`, `1 = c`). -/
noncomputable def ghostGenerator (a : Fin 3) (i : Fin 2) : Sl2GhostSpace :=
  ghostEmbed a (SympFerm.stWordSF [((0, i) : ℕ × Fin 2)])

@[simp] theorem ghostGenerator_zero (a : Fin 3) : ghostGenerator a 0 = bGhost a := rfl
@[simp] theorem ghostGenerator_one (a : Fin 3) : ghostGenerator a 1 = cGhost a := rfl

theorem ghostGenerator_odd (a : Fin 3) (i : Fin 2) :
    ghostGenerator a i ∈ sl2GhostSVA.parity 1 := by
  fin_cases i
  · exact bGhost_odd a
  · exact cGhost_odd a

private theorem ghostSingleton_odd (i : Fin 2) :
    SympFerm.stWordSF [((0, i) : ℕ × Fin 2)] ∈ Ghost.bcGhostSVA.parity 1 := by
  exact SympFerm.stWordSF_mem_evenOdd [((0, i) : ℕ × Fin 2)]

/-- The full nonnegative product table of the six actual ghost generators. -/
theorem ghostGenerator_nonneg_product (a b : Fin 3) (i j : Fin 2)
    (n : ℤ) (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (ghostGenerator a i)) n (ghostGenerator b j) =
      if a = b ∧ i + 1 = j ∧ n = 0 then sl2GhostSVA.vacuum else 0 := by
  by_cases hab : a = b
  · subst b
    unfold ghostGenerator
    rw [ghostEmbed_mode]
    change ghostEmbed a (Ghost.YGh _ (-n - 1) _) = _
    rw [Ghost.YGh_word, ghostWord_single_field]
    by_cases hn0 : n = 0
    · subst n
      simp only [neg_zero, zero_sub]
      rw [Ghost.ghField, if_neg (by omega)]
      change ghostEmbed a (SympFerm.annBase (0, i + 1)
        (SympFerm.stWordSF [((0, j) : ℕ × Fin 2)])) = _
      rw [SympFerm.annBase_stWordSF_cons, SympFerm.annBase_stWordSF_nil]
      by_cases hij : i + 1 = j
      · simp [hij, SympFerm.stWordSF_nil]
      · simp [hij]
    · have hz := ghField_lt_neg_one_zero i (j := -n - 1) (by omega) [j]
      simp only [List.map_cons, List.map_nil] at hz
      rw [hz, ghostEmbed_zero, if_neg (by tauto)]
  · change sl2GhostSVA.Y (ghostEmbed a _) (-n - 1) (ghostEmbed b _) = _
    rw [ghostEmbed_Y_of_ne_parity hab (ghostSingleton_odd i) (ghostSingleton_odd j)
      (by omega), if_neg (by tauto)]

/-- The canonical anticommutation relations of the six actual ghost modes.
The delta is `m + n + 1 = 0` because both indices use vertex-algebra modes. -/
theorem ghostGenerator_modes_anticomm (a b : Fin 3) (i j : Fin 2) (m n : ℤ) :
    mode (sl2GhostSVA.Y (ghostGenerator a i)) m *
        mode (sl2GhostSVA.Y (ghostGenerator b j)) n
      + mode (sl2GhostSVA.Y (ghostGenerator b j)) n *
        mode (sl2GhostSVA.Y (ghostGenerator a i)) m =
      if a = b ∧ i + 1 = j ∧ m + n + 1 = 0 then LinearMap.id else 0 := by
  have hc := translationCovariant_sl2GhostSVA.mode_commutator_bound
    (ghostGenerator_odd a i) (ghostGenerator_odd b j) 1
    (fun r hr => by rw [ghostGenerator_nonneg_product a b i j r (by omega),
      if_neg (by omega)]) m n
  simp only [koszul_one_one, neg_smul, one_smul, sub_neg_eq_add,
    Finset.sum_range_one, gBinom_zero, Nat.cast_zero, sub_zero] at hc
  rw [hc, ghostGenerator_nonneg_product a b i j 0 (by omega)]
  by_cases h : a = b ∧ i + 1 = j
  · rw [if_pos (by tauto), sl2GhostSVA.vacuum_Y, mode_apply, FormalDist.one_apply]
    by_cases hmn : m + n + 1 = 0
    · rw [if_pos (by omega), if_pos (by tauto)]
      rfl
    · rw [if_neg (by omega), if_neg (by tauto)]
  · rw [if_neg (by tauto), map_zero]
    rw [if_neg (by tauto)]
    rfl

/-- Actual antighost modes anticommute in all three pairs. -/
theorem bGhost_modes_anticomm (a b : Fin 3) (m n : ℤ) :
    mode (sl2GhostSVA.Y (bGhost a)) m * mode (sl2GhostSVA.Y (bGhost b)) n
      + mode (sl2GhostSVA.Y (bGhost b)) n * mode (sl2GhostSVA.Y (bGhost a)) m = 0 := by
  simpa using ghostGenerator_modes_anticomm a b 0 0 m n

/-- Actual mixed ghost modes have the canonical delta anticommutator. -/
theorem bGhost_cGhost_modes_anticomm (a b : Fin 3) (m n : ℤ) :
    mode (sl2GhostSVA.Y (bGhost a)) m * mode (sl2GhostSVA.Y (cGhost b)) n
      + mode (sl2GhostSVA.Y (cGhost b)) n * mode (sl2GhostSVA.Y (bGhost a)) m =
      if a = b ∧ m + n + 1 = 0 then LinearMap.id else 0 := by
  simpa using ghostGenerator_modes_anticomm a b 0 1 m n

end VOA.Sl2SemiInfinite
