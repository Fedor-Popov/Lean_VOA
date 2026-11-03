/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroFiltrationTranslation
import VOA.Examples.VirasoroLengthTwoArithmetic

/-!
# The universal length-two Virasoro quasi-primaries

This file defines the PBW-normalized vector `lengthTwoQ c m = Q_{2m}` in the universal
Virasoro vacuum module and proves directly that it is quasi-primary for `m ≥ 2`.

The proof uses only the Virasoro commutator, the vacuum relation, and the two elementary
coefficient identities in `VirasoroLengthTwoArithmetic`.  In particular it uses neither the
project PBW axiom nor a simple-module character theorem.
-/

set_option linter.style.longLine false

open scoped BigOperators

namespace VOA

namespace VirGradedUnitarity

open VOA.VirModule VOA.VirGoodFil

variable (c : ℂ)

/-- View the rational two-mode coefficient as a complex scalar. These coefficients
weight the pairs of creation modes whose energies add to 2m. -/
private noncomputable def aCoeffC (m j : ℕ) : ℂ := (lengthTwoACoeff m j : ℂ)

/-- The complex coefficient of the single-mode correction L₋₂ₘ𝟙. Together
with the two-mode terms it makes the complete state annihilated by L₁. -/
private noncomputable def bCoeffC (m : ℕ) : ℂ := (lengthTwoBCoeff m : ℂ)

/-- The off-diagonal part of `Q_{2m}`, with the larger creation mode written first. -/
noncomputable def lengthTwoQOffDiag (m : ℕ) : VirUniv c :=
  (2 : ℂ) • ∑ j ∈ Finset.range (m - 2),
    aCoeffC m j • negWordVir c [2 * m - 4 - j, j]

/-- The PBW-normalized length-two quasi-primary `Q_{2m}`.

For `m ≥ 2` this is
`2 ∑_{j=0}^{m-3} a_{m,j} L_{-(2m-2-j)}L_{-(j+2)}𝟙
  + a_{m,m-2}L_{-m}²𝟙 + b_mL_{-2m}𝟙`.
The first sum is empty at `m = 2`. -/
noncomputable def lengthTwoQ (m : ℕ) : VirUniv c :=
  lengthTwoQOffDiag c m
    + aCoeffC m (m - 2) • negWordVir c [m - 2, m - 2]
    + bCoeffC m • negWordVir c [2 * m - 2]

/-! ## `L₁` on words of length one and two -/

/-- `L₁L₋₂𝟙 = 0`. -/
theorem Lop_one_negWordVir_single_zero : Lop c 1 (negWordVir c [0]) = 0 := by
  have h := Lop_apply_bracket c 1 (-2) (vacVec c)
  have hv1 : Lop c 1 (vacVec c) = 0 := Lop_vacuum c (by norm_num)
  have hvm1 : Lop c (-1) (vacVec c) = 0 := Lop_vacuum c (by norm_num)
  rw [hv1, map_zero, if_neg (by omega : ¬((1 : ℤ) + (-2) = 0)),
    zero_smul, add_zero, show ((1 : ℤ) : ℂ) - ((-2 : ℤ) : ℂ) = 3 by norm_num,
    show (1 : ℤ) + (-2) = -1 by norm_num, hvm1, smul_zero,
    add_zero] at h
  simpa only [negWordVir_cons, negWordVir_nil] using h

/-- `L₁L₋(i+3)𝟙 = (i+4)L₋(i+2)𝟙`. -/
theorem Lop_one_negWordVir_single_succ (i : ℕ) :
    Lop c 1 (negWordVir c [i + 1]) =
      ((i : ℂ) + 4) • negWordVir c [i] := by
  have h := Lop_apply_bracket c 1 (-((i : ℤ) + 1) - 2) (vacVec c)
  have hv1 : Lop c 1 (vacVec c) = 0 := Lop_vacuum c (by norm_num)
  rw [hv1, map_zero,
    if_neg (by omega : ¬((1 : ℤ) + (-((i : ℤ) + 1) - 2) = 0)), zero_smul, add_zero,
    show (1 : ℤ) + (-((i : ℤ) + 1) - 2) = -(i : ℤ) - 2 by ring,
    show ((1 : ℤ) : ℂ) - ((-((i : ℤ) + 1) - 2 : ℤ) : ℂ) = (i : ℂ) + 4 by
      push_cast; ring] at h
  simpa only [negWordVir_cons, negWordVir_nil, show (-(i + 1 : ℕ) : ℤ) - 2 =
      -((i : ℤ) + 1) - 2 by push_cast; ring, zero_add] using h

/-- The `j=0` endpoint of the length-two commutator calculation. -/
theorem Lop_one_negWordVir_pair_zero (i : ℕ) :
    Lop c 1 (negWordVir c [i + 1, 0]) =
      ((i : ℂ) + 4) • negWordVir c [i, 0] := by
  have h := Lop_apply_bracket c 1 (-((i : ℤ) + 1) - 2) (negWordVir c [0])
  rw [Lop_one_negWordVir_single_zero, map_zero,
    if_neg (by omega : ¬((1 : ℤ) + (-((i : ℤ) + 1) - 2) = 0)), zero_smul, add_zero,
    show (1 : ℤ) + (-((i : ℤ) + 1) - 2) = -(i : ℤ) - 2 by ring,
    show ((1 : ℤ) : ℂ) - ((-((i : ℤ) + 1) - 2 : ℤ) : ℂ) = (i : ℂ) + 4 by
      push_cast; ring, zero_add] at h
  simpa only [negWordVir_cons, show (-(i + 1 : ℕ) : ℤ) - 2 =
      -((i : ℤ) + 1) - 2 by push_cast; ring] using h

/-- The interior length-two commutator calculation. -/
theorem Lop_one_negWordVir_pair_succ (i j : ℕ) :
    Lop c 1 (negWordVir c [i + 1, j + 1]) =
      ((i : ℂ) + 4) • negWordVir c [i, j + 1]
        + ((j : ℂ) + 4) • negWordVir c [i + 1, j] := by
  have h := Lop_apply_bracket c 1 (-((i : ℤ) + 1) - 2) (negWordVir c [j + 1])
  rw [Lop_one_negWordVir_single_succ,
    if_neg (by omega : ¬((1 : ℤ) + (-((i : ℤ) + 1) - 2) = 0)), zero_smul, add_zero,
    show (1 : ℤ) + (-((i : ℤ) + 1) - 2) = -(i : ℤ) - 2 by ring,
    show ((1 : ℤ) : ℂ) - ((-((i : ℤ) + 1) - 2 : ℤ) : ℂ) = (i : ℂ) + 4 by
      push_cast; ring] at h
  rw [map_smul] at h
  simpa only [negWordVir_cons, show (-(i + 1 : ℕ) : ℤ) - 2 =
      -((i : ℤ) + 1) - 2 by push_cast; ring, add_comm] using h

/-- The remaining diagonal endpoint at `m = 2`: `L₁L₋₂²𝟙 = 3L₋₃𝟙`. -/
theorem Lop_one_negWordVir_pair_zero_zero :
    Lop c 1 (negWordVir c [0, 0]) = (3 : ℂ) • negWordVir c [1] := by
  have h := Lop_apply_bracket c 1 (-2) (negWordVir c [0])
  rw [Lop_one_negWordVir_single_zero, map_zero,
    if_neg (by omega : ¬((1 : ℤ) + (-2) = 0)), zero_smul, add_zero,
    show ((1 : ℤ) : ℂ) - ((-2 : ℤ) : ℂ) = 3 by norm_num,
    show (1 : ℤ) + (-2) = -1 by norm_num, zero_add] at h
  have ht := VirGoodFil.Lop_neg_one_negWordVir_cons c 0 ([] : List ℕ)
  rw [VirGoodFil.Lop_neg_one_negWordVir_nil, map_zero, zero_add] at ht
  norm_num at ht
  rw [ht] at h
  simpa only [negWordVir_cons, negWordVir_nil] using h

/-! ## Telescoping the coefficient recurrence -/

/-- The rational `a`-coefficient recurrence, cast to `ℂ`. -/
theorem aCoeffC_recurrence (m j : ℕ) (hjm : j + 3 ≤ m) :
    aCoeffC m j * (2 * (m : ℂ) - 1 - j) +
      aCoeffC m (j + 1) * (j + 4) = 0 := by
  unfold aCoeffC
  exact_mod_cast lengthTwoACoeff_recurrence m j hjm

/-- The residual rational `b`-coefficient identity, cast to `ℂ`. -/
theorem bCoeffC_residual (m : ℕ) (hm : 2 ≤ m) :
    (2 * (m : ℂ) + 1) * bCoeffC m +
      ((m : ℂ) + 1) * aCoeffC m (m - 2) = 0 := by
  unfold aCoeffC bCoeffC
  exact_mod_cast lengthTwoBCoeff_residual m hm

/-- The diagonal exact-length-two coefficient never vanishes.  This is the scalar input for the
triangular associated-graded independence argument. -/
theorem lengthTwoADiagonal_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    ((lengthTwoACoeff m (m - 2) : ℚ) : ℂ) ≠ 0 := by
  have htop : Nat.choose (2 * m - 1) (m - 2) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.choose_pos (by omega : m - 2 ≤ 2 * m - 1))
  have hbot : Nat.choose (m - 2 + 3) 3 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ m - 2 + 3))
  have hq : lengthTwoACoeff m (m - 2) ≠ 0 := by
    unfold lengthTwoACoeff
    exact div_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast htop))
      (by exact_mod_cast hbot)
  exact_mod_cast hq

/-- A partial off-diagonal sum has only its last uncancelled `L₁` boundary term. -/
theorem Lop_one_lengthTwoQOffDiag_partial (m k : ℕ) (hm : 2 ≤ m)
    (hk : k + 3 ≤ m) :
    Lop c 1 ((2 : ℂ) • ∑ j ∈ Finset.range (k + 1),
        aCoeffC m j • negWordVir c [2 * m - 4 - j, j]) =
      (2 * aCoeffC m k * (2 * (m : ℂ) - 1 - k)) •
        negWordVir c [2 * m - 5 - k, k] := by
  induction k with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_smul]
      simp only [Nat.sub_zero]
      have hi : 2 * m - 4 = (2 * m - 5) + 1 := by omega
      rw [hi, Lop_one_negWordVir_pair_zero]
      have hcast : ((2 * m - 5 : ℕ) : ℂ) = 2 * (m : ℂ) - 5 := by
        rw [Nat.cast_sub (by omega : 5 ≤ 2 * m)]
        push_cast
        ring
      rw [hcast]
      module
  | succ k ih =>
      have hk' : k + 3 ≤ m := by omega
      rw [Finset.sum_range_succ, smul_add, map_add, ih hk']
      simp only [map_smul]
      have hi : 2 * m - 4 - (k + 1) = (2 * m - 5 - (k + 1)) + 1 := by omega
      rw [hi, Lop_one_negWordVir_pair_succ]
      have htarget : 2 * m - 5 - (k + 1) + 1 = 2 * m - 5 - k := by omega
      rw [htarget]
      have hrec := aCoeffC_recurrence m k (by omega)
      have hout : (((2 * m - 5 - (k + 1) : ℕ) : ℂ) + 4) =
          2 * (m : ℂ) - 1 - ((k + 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega : k + 1 ≤ 2 * m - 5)]
        rw [Nat.cast_sub (by omega : 5 ≤ 2 * m)]
        push_cast
        ring
      rw [hout]
      have hcancel :
          2 * aCoeffC m k * (2 * (m : ℂ) - 1 - k) +
            2 * aCoeffC m (k + 1) * ((k : ℂ) + 4) = 0 := by
        calc
          _ = 2 * (aCoeffC m k * (2 * (m : ℂ) - 1 - k) +
                aCoeffC m (k + 1) * ((k : ℂ) + 4)) := by ring
          _ = 0 := by rw [hrec, mul_zero]
      calc
        _ = (2 * aCoeffC m k * (2 * (m : ℂ) - 1 - k) +
              2 * aCoeffC m (k + 1) * ((k : ℂ) + 4)) •
                negWordVir c [2 * m - 5 - k, k]
            + (2 * aCoeffC m (k + 1) *
                (2 * (m : ℂ) - 1 - ((k + 1 : ℕ) : ℂ))) •
                negWordVir c [2 * m - 5 - (k + 1), k + 1] := by module
        _ = _ := by rw [hcancel, zero_smul, zero_add]

/-- The action of `L₁` on the complete off-diagonal portion of `Q_{2m}`. -/
theorem Lop_one_lengthTwoQOffDiag (m : ℕ) (hm : 3 ≤ m) :
    Lop c 1 (lengthTwoQOffDiag c m) =
      (2 * aCoeffC m (m - 3) * ((m : ℂ) + 2)) •
        negWordVir c [m - 2, m - 3] := by
  rw [lengthTwoQOffDiag, show m - 2 = (m - 3) + 1 by omega]
  have h := Lop_one_lengthTwoQOffDiag_partial c m (m - 3) (by omega) (by omega)
  have hmode : 2 * m - 5 - (m - 3) = m - 2 := by omega
  have hindex : m - 3 + 1 = m - 2 := by omega
  have hcoef : 2 * (m : ℂ) - 1 - ((m - 3 : ℕ) : ℂ) = (m : ℂ) + 2 := by
    rw [Nat.cast_sub (by omega : 3 ≤ m)]
    push_cast
    ring
  simpa only [hmode, hindex, hcoef] using h

/-- The diagonal word contributes both the last length-two boundary term and a merged
length-one term. -/
theorem Lop_one_negWordVir_diagonal (m : ℕ) (hm : 3 ≤ m) :
    Lop c 1 (negWordVir c [m - 2, m - 2]) =
      (2 * ((m : ℂ) + 1)) • negWordVir c [m - 2, m - 3]
        + ((m : ℂ) + 1) • negWordVir c [2 * m - 3] := by
  have hpair := Lop_one_negWordVir_pair_succ c (m - 3) (m - 3)
  have hswap := negWordVir_swap c (m - 3) (m - 2) ([] : List ℕ)
  simp only [show m - 3 + 1 = m - 2 by omega] at hpair
  rw [hswap] at hpair
  have hmerge : m - 3 + (m - 2) + 2 = 2 * m - 3 := by omega
  rw [hmerge] at hpair
  have hcoef : (((m - 3 : ℕ) : ℂ) + 4) = (m : ℂ) + 1 := by
    rw [Nat.cast_sub (by omega : 3 ≤ m)]
    push_cast
    ring
  rw [hcoef] at hpair
  have hdiff : ((m - 2 : ℕ) : ℂ) - ((m - 3 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 3 ≤ m)]
    push_cast
    ring
  rw [hdiff, one_smul] at hpair
  rw [hpair]
  module

/-- The length-one summand in `Q_{2m}` contributes its residual term. -/
theorem Lop_one_negWordVir_last (m : ℕ) (hm : 2 ≤ m) :
    Lop c 1 (negWordVir c [2 * m - 2]) =
      (2 * (m : ℂ) + 1) • negWordVir c [2 * m - 3] := by
  have h := Lop_one_negWordVir_single_succ c (2 * m - 3)
  have hindex : 2 * m - 3 + 1 = 2 * m - 2 := by omega
  have hcoef : (((2 * m - 3 : ℕ) : ℂ) + 4) = 2 * (m : ℂ) + 1 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * m)]
    push_cast
    ring
  simpa only [hindex, hcoef] using h

/-! ## The quasi-primary and filtration theorems -/

/-- **The explicit length-two vector is quasi-primary.** -/
theorem lengthTwoQ_quasiPrimary (m : ℕ) (hm : 2 ≤ m) :
    Lop c 1 (lengthTwoQ c m) = 0 := by
  rcases eq_or_lt_of_le hm with rfl | hm'
  · rw [lengthTwoQ, lengthTwoQOffDiag]
    norm_num [aCoeffC, bCoeffC, lengthTwoACoeff, lengthTwoBCoeff,
      Nat.choose, Lop_one_negWordVir_pair_zero_zero, Lop_one_negWordVir_single_succ]
    module
  · rw [lengthTwoQ, map_add, map_add, Lop_one_lengthTwoQOffDiag c m hm', map_smul,
      Lop_one_negWordVir_diagonal c m hm', map_smul, Lop_one_negWordVir_last c m hm]
    have hrec := aCoeffC_recurrence m (m - 3) (by omega)
    have hres := bCoeffC_residual m hm
    have hcast : (((m - 3 : ℕ) : ℂ) + 4) = (m : ℂ) + 1 := by
      rw [Nat.cast_sub (by omega : 3 ≤ m)]
      push_cast
      ring
    have hcast' : 2 * (m : ℂ) - 1 - ((m - 3 : ℕ) : ℂ) = (m : ℂ) + 2 := by
      rw [Nat.cast_sub (by omega : 3 ≤ m)]
      push_cast
      ring
    rw [hcast, hcast'] at hrec
    rw [show m - 3 + 1 = m - 2 by omega] at hrec
    have hlen :
        2 * aCoeffC m (m - 3) * ((m : ℂ) + 2) +
          aCoeffC m (m - 2) * (2 * ((m : ℂ) + 1)) = 0 := by
      calc
        _ = 2 * (aCoeffC m (m - 3) * ((m : ℂ) + 2) +
              aCoeffC m (m - 2) * ((m : ℂ) + 1)) := by ring
        _ = 0 := by rw [hrec, mul_zero]
    have hone :
        aCoeffC m (m - 2) * ((m : ℂ) + 1) +
          bCoeffC m * (2 * (m : ℂ) + 1) = 0 := by
      calc
        _ = (2 * (m : ℂ) + 1) * bCoeffC m +
              ((m : ℂ) + 1) * aCoeffC m (m - 2) := by ring
        _ = 0 := hres
    calc
      _ = (2 * aCoeffC m (m - 3) * ((m : ℂ) + 2) +
            aCoeffC m (m - 2) * (2 * ((m : ℂ) + 1))) •
              negWordVir c [m - 2, m - 3]
          + (aCoeffC m (m - 2) * ((m : ℂ) + 1) +
              bCoeffC m * (2 * (m : ℂ) + 1)) •
                negWordVir c [2 * m - 3] := by module
      _ = 0 := by rw [hlen, hone]; simp

/-- The normalization check `Q₄ = L₋₂²𝟙 - (3/5)L₋₄𝟙`. -/
theorem lengthTwoQ_two :
    lengthTwoQ c 2 = negWordVir c [0, 0] - (3 / 5 : ℂ) • negWordVir c [2] := by
  rw [lengthTwoQ, lengthTwoQOffDiag]
  norm_num [aCoeffC, bCoeffC, lengthTwoACoeff, lengthTwoBCoeff, Nat.choose]
  module

/-- The normalization check
`Q₆ = 2L₋₄L₋₂𝟙 - (5/4)L₋₃²𝟙 + (5/7)L₋₆𝟙`. -/
theorem lengthTwoQ_three :
    lengthTwoQ c 3 = (2 : ℂ) • negWordVir c [2, 0]
      - (5 / 4 : ℂ) • negWordVir c [1, 1]
      + (5 / 7 : ℂ) • negWordVir c [4] := by
  rw [lengthTwoQ, lengthTwoQOffDiag]
  norm_num [aCoeffC, bCoeffC, lengthTwoACoeff, lengthTwoBCoeff, Nat.choose]
  module

/-- `Q_{2m}` is homogeneous of weight `2m`. -/
theorem lengthTwoQ_mem_grading (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoQ c m ∈ gradingVir c (2 * m : ℤ) := by
  rw [lengthTwoQ]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · rw [lengthTwoQOffDiag]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro j hj
      rw [Finset.mem_range] at hj
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨[2 * m - 4 - j, j], ?_, rfl⟩
      simp only [energyVir_cons, energyVir_nil]
      omega
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨[m - 2, m - 2], ?_, rfl⟩
      simp only [energyVir_cons, energyVir_nil]
      omega
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨[2 * m - 2], ?_, rfl⟩
    simp only [energyVir_cons, energyVir_nil]
    omega

/-- `Q_{2m}` belongs to the PBW-length-two filtration step. -/
theorem lengthTwoQ_mem_virFil (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoQ c m ∈ virFil c 2 (2 * m : ℤ) := by
  rw [lengthTwoQ]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · rw [lengthTwoQOffDiag]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro j hj
      rw [Finset.mem_range] at hj
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨[2 * m - 4 - j, j], ?_, ?_, by simp, rfl⟩
      · apply SortedWord.cons (sortedWord_singleton j)
        simp only [List.mem_singleton]
        intro b hb
        subst b
        omega
      · simp only [energyVir_cons, energyVir_nil]
        omega
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨[m - 2, m - 2], ?_, ?_, by simp, rfl⟩
      · exact SortedWord.cons (sortedWord_singleton _) (by simp)
      · simp only [energyVir_cons, energyVir_nil]
        omega
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨[2 * m - 2], sortedWord_singleton _, ?_, by simp, rfl⟩
    simp only [energyVir_cons, energyVir_nil]
    omega

end VirGradedUnitarity

end VOA
