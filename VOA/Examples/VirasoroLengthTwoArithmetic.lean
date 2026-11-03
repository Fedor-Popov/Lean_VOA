/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Arithmetic for the length-two Virasoro quasi-primary norms

This file isolates the elementary rational inequalities used in the all-weight, creation-word-
length-two
graded-unitarity argument for the boundary minimal models `M(2, 2n+1)`.

The conventional phrase "PBW length" labels the filtration; this arithmetic file uses no PBW
theorem, basis theorem, or VOA representation theory.

The norm formula for the new quasi-primary `Q_{2m}` has the factor

`c * (c + rho m)`,

where `rho m` is the rational function defined below.  The main results are the exact consecutive
difference formula and the uniform bound `0 < rho m ≤ 22 / 5` for `m ≥ 2`.

This is deliberately a VOA-independent arithmetic leaf.  It does not assert the norm formula;
later files may import it after that representation-theoretic identity has been proved.

## References

* `GradedUnitarityVirasoro.tex`, equations `rho-m`, `rho-difference`, and `rho-bound`.
-/

namespace VOA

namespace VirGradedUnitarity

/-- The coefficient `a_{m,j}` in the creation-word-normalized length-two quasi-primary `Q_{2m}`. -/
def lengthTwoACoeff (m j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * (Nat.choose (2 * m - 1) j : ℚ) / (Nat.choose (j + 3) 3 : ℚ)

/-- The coefficient `b_m` of `L_{-2m}` in the creation-word-normalized length-two quasi-primary
`Q_{2m}`. -/
def lengthTwoBCoeff (m : ℕ) : ℚ :=
  (-1 : ℚ) ^ (m + 1) * 3 / ((m : ℚ) * (m + 1) * (2 * m + 1)) *
    (Nat.choose (2 * m) m : ℚ)

/-- Neighboring length-two coefficients cancel after applying `L₁`.  The hypothesis is precisely
the range `0 ≤ j ≤ m-3` occurring in the off-diagonal sum for `Q_{2m}`. -/
theorem lengthTwoACoeff_recurrence (m j : ℕ) (hjm : j + 3 ≤ m) :
    lengthTwoACoeff m j * (2 * (m : ℚ) - 1 - j) +
      lengthTwoACoeff m (j + 1) * (j + 4) = 0 := by
  have hjK : j ≤ 2 * m - 1 := by omega
  have hchooseNat := Nat.choose_succ_right_eq (2 * m - 1) j
  have hchoose :
      (Nat.choose (2 * m - 1) (j + 1) : ℚ) * (j + 1) =
        (Nat.choose (2 * m - 1) j : ℚ) * (2 * (m : ℚ) - 1 - j) := by
    calc
      (Nat.choose (2 * m - 1) (j + 1) : ℚ) * (j + 1) =
          (Nat.choose (2 * m - 1) j : ℚ) * (2 * m - 1 - j : ℕ) := by
            exact_mod_cast hchooseNat
      _ = (Nat.choose (2 * m - 1) j : ℚ) * (2 * (m : ℚ) - 1 - j) := by
        rw [Nat.cast_sub hjK, Nat.cast_sub (by omega : 1 ≤ 2 * m)]
        push_cast
        ring
  have hdenNat := Nat.choose_mul_succ_eq (j + 3) 3
  have hden :
      (Nat.choose (j + 3) 3 : ℚ) * (j + 4) =
        (Nat.choose (j + 4) 3 : ℚ) * (j + 1) := by
    exact_mod_cast hdenNat
  have hd0 : (Nat.choose (j + 3) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ j + 3)))
  have hd1 : (Nat.choose (j + 4) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ j + 4)))
  have hcross :
      (Nat.choose (2 * m - 1) j : ℚ) * (2 * (m : ℚ) - 1 - j) *
          (Nat.choose (j + 4) 3 : ℚ) =
        (Nat.choose (j + 3) 3 : ℚ) * (Nat.choose (2 * m - 1) (j + 1) : ℚ) *
          (j + 4) := by
    calc
      (Nat.choose (2 * m - 1) j : ℚ) * (2 * (m : ℚ) - 1 - j) *
          (Nat.choose (j + 4) 3 : ℚ) =
          ((Nat.choose (2 * m - 1) (j + 1) : ℚ) * (j + 1)) *
            (Nat.choose (j + 4) 3 : ℚ) := by rw [hchoose]
      _ = (Nat.choose (2 * m - 1) (j + 1) : ℚ) *
          ((Nat.choose (j + 4) 3 : ℚ) * (j + 1)) := by ring
      _ = (Nat.choose (2 * m - 1) (j + 1) : ℚ) *
          ((Nat.choose (j + 3) 3 : ℚ) * (j + 4)) := by rw [← hden]
      _ = (Nat.choose (j + 3) 3 : ℚ) * (Nat.choose (2 * m - 1) (j + 1) : ℚ) *
          (j + 4) := by ring
  unfold lengthTwoACoeff
  simp only [show j + 1 + 3 = j + 4 by omega]
  rw [pow_succ]
  field_simp [hd0, hd1]
  rw [hcross]
  ring

/-- The remaining length-one term after applying `L₁` to `Q_{2m}` cancels against its
`L_{-2m}` coefficient. -/
theorem lengthTwoBCoeff_residual (m : ℕ) (hm : 2 ≤ m) :
    (2 * (m : ℚ) + 1) * lengthTwoBCoeff m +
      ((m : ℚ) + 1) * lengthTwoACoeff m (m - 2) = 0 := by
  have hm1 : 1 ≤ m := by omega
  have hmTwo : m ≤ 2 * m - 1 := by omega
  have hsign : (-1 : ℚ) ^ (m + 1) = -((-1 : ℚ) ^ (m - 2)) := by
    rw [show m + 1 = (m - 2) + 3 by omega, pow_add]
    norm_num
  have hdoubleNat : Nat.choose (2 * m) m = 2 * Nat.choose (2 * m - 1) (m - 1) := by
    have hpascal := Nat.choose_succ_succ (2 * m - 1) (m - 1)
    rw [show (2 * m - 1).succ = 2 * m by omega,
      show (m - 1).succ = m by omega] at hpascal
    have hsym := Nat.choose_symm hmTwo
    rw [show 2 * m - 1 - m = m - 1 by omega] at hsym
    calc
      Nat.choose (2 * m) m =
          Nat.choose (2 * m - 1) (m - 1) + Nat.choose (2 * m - 1) m := by
            exact hpascal
      _ = Nat.choose (2 * m - 1) (m - 1) + Nat.choose (2 * m - 1) (m - 1) := by
        rw [hsym]
      _ = 2 * Nat.choose (2 * m - 1) (m - 1) := by omega
  have hadjNat :
      Nat.choose (2 * m - 1) (m - 1) * (m - 1) =
        Nat.choose (2 * m - 1) (m - 2) * (m + 1) := by
    have hadj := Nat.choose_succ_right_eq (2 * m - 1) (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega,
      show 2 * m - 1 - (m - 2) = m + 1 by omega] at hadj
    exact hadj
  have hmagNat :
      Nat.choose (2 * m) m * (m - 1) =
        2 * Nat.choose (2 * m - 1) (m - 2) * (m + 1) := by
    rw [hdoubleNat, mul_assoc, hadjNat]
    ring
  have hmag :
      (Nat.choose (2 * m) m : ℚ) * ((m : ℚ) - 1) =
        2 * (Nat.choose (2 * m - 1) (m - 2) : ℚ) * (m + 1) := by
    calc
      (Nat.choose (2 * m) m : ℚ) * ((m : ℚ) - 1) =
          (Nat.choose (2 * m) m : ℚ) * (m - 1 : ℕ) := by
            rw [Nat.cast_sub hm1]
            norm_num
      _ = 2 * (Nat.choose (2 * m - 1) (m - 2) : ℚ) * (m + 1) := by
        exact_mod_cast hmagNat
  have hdenStepNat := Nat.choose_succ_right_eq (m + 1) 2
  have hdenStep :
      (Nat.choose (m + 1) 3 : ℚ) * 3 =
        (Nat.choose (m + 1) 2 : ℚ) * ((m : ℚ) - 1) := by
    calc
      (Nat.choose (m + 1) 3 : ℚ) * 3 =
          (Nat.choose (m + 1) 2 : ℚ) * (m + 1 - 2 : ℕ) := by
            exact_mod_cast hdenStepNat
      _ = (Nat.choose (m + 1) 2 : ℚ) * ((m : ℚ) - 1) := by
        rw [show m + 1 - 2 = m - 1 by omega, Nat.cast_sub hm1]
        norm_num
  have hchooseTwo := Nat.cast_choose_two (K := ℚ) (m + 1)
  have hden :
      (Nat.choose (m + 1) 3 : ℚ) * 6 =
        ((m : ℚ) + 1) * m * (m - 1) := by
    calc
      (Nat.choose (m + 1) 3 : ℚ) * 6 =
          ((Nat.choose (m + 1) 3 : ℚ) * 3) * 2 := by ring
      _ = ((Nat.choose (m + 1) 2 : ℚ) * ((m : ℚ) - 1)) * 2 := by rw [hdenStep]
      _ = (((m : ℚ) + 1) * m / 2 * (m - 1)) * 2 := by
        rw [hchooseTwo]
        push_cast
        ring
      _ = ((m : ℚ) + 1) * m * (m - 1) := by ring
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hp1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2p1 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  have hchooseDen : (Nat.choose (m + 1) 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 3 ≤ m + 1)))
  have hfinal :
      3 * (Nat.choose (2 * m) m : ℚ) * (Nat.choose (m + 1) 3 : ℚ) =
        (m : ℚ) * (m + 1) ^ 2 * (Nat.choose (2 * m - 1) (m - 2) : ℚ) := by
    calc
      3 * (Nat.choose (2 * m) m : ℚ) * (Nat.choose (m + 1) 3 : ℚ) =
          (Nat.choose (2 * m) m : ℚ) *
            ((Nat.choose (m + 1) 3 : ℚ) * 6) / 2 := by ring
      _ = (Nat.choose (2 * m) m : ℚ) *
          (((m : ℚ) + 1) * m * (m - 1)) / 2 := by rw [hden]
      _ = ((Nat.choose (2 * m) m : ℚ) * (m - 1)) * ((m + 1) * m) / 2 := by ring
      _ = (2 * (Nat.choose (2 * m - 1) (m - 2) : ℚ) * (m + 1)) *
          ((m + 1) * m) / 2 := by rw [hmag]
      _ = (m : ℚ) * (m + 1) ^ 2 * (Nat.choose (2 * m - 1) (m - 2) : ℚ) := by ring
  unfold lengthTwoBCoeff lengthTwoACoeff
  simp only [show m - 2 + 3 = m + 1 by omega]
  rw [hsign]
  field_simp [hm0, hp1, h2p1, hchooseDen]
  rw [hfinal]
  ring

/-- The positive rational root occurring in the squared norm of the length-two quasi-primary
`Q_{2m}`; see `GradedUnitarityVirasoro.tex`, equation `rho-m`. -/
def lengthTwoRho (m : ℕ) : ℚ :=
  36 * (4 * (m : ℚ) ^ 2 - 2 * m - 1) /
    ((m : ℚ) * (m - 1) * (m + 1) * (2 * m - 3) * (2 * m - 1) * (2 * m + 1))

/-- The exact consecutive-difference identity for `lengthTwoRho`; this is equation
`rho-difference` of `GradedUnitarityVirasoro.tex`. -/
theorem lengthTwoRho_sub_succ (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoRho m - lengthTwoRho (m + 1) =
      36 * (4 * (m : ℚ) + 1) * (8 * (m : ℚ) ^ 2 + 4 * m - 9) /
        ((m : ℚ) * (m - 1) * (m + 1) * (m + 2) *
          (2 * m - 3) * (2 * m - 1) * (2 * m + 1) * (2 * m + 3)) := by
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hm1 : (m : ℚ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp1 : (m : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hp2 : (m : ℚ) + 2 ≠ 0 := ne_of_gt (by linarith)
  have h2m3 : 2 * (m : ℚ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℚ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2p1 : 2 * (m : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have h2p3 : 2 * (m : ℚ) + 3 ≠ 0 := ne_of_gt (by linarith)
  have hquadMinus : 3 - 8 * (m : ℚ) + 4 * (m : ℚ) ^ 2 ≠ 0 := by
    have hprod : 0 < (2 * (m : ℚ) - 3) * (2 * m - 1) :=
      mul_pos (by linarith) (by linarith)
    apply ne_of_gt
    nlinarith
  have hquadPlus : -1 + 4 * (m : ℚ) ^ 2 ≠ 0 := by
    have hprod : 0 < (2 * (m : ℚ) - 1) * (2 * m + 1) :=
      mul_pos (by linarith) (by linarith)
    apply ne_of_gt
    nlinarith
  have hquadMinus' : 3 - (m : ℚ) * 8 + (m : ℚ) ^ 2 * 4 ≠ 0 := by
    simpa [mul_comm] using hquadMinus
  have hquadPlus' : -1 + (m : ℚ) ^ 2 * 4 ≠ 0 := by
    simpa [mul_comm] using hquadPlus
  unfold lengthTwoRho
  push_cast
  field_simp [hm0, hm1, hp1, hp2, h2m3, h2m1, h2p1, h2p3, hquadMinus', hquadPlus']
  ring_nf
  field_simp [hquadMinus', hquadPlus']
  ring

/-- The root `lengthTwoRho m` is strictly positive throughout its relevant range `m ≥ 2`. -/
theorem lengthTwoRho_pos (m : ℕ) (hm : 2 ≤ m) : 0 < lengthTwoRho m := by
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hnum : 0 < 4 * (m : ℚ) ^ 2 - 2 * m - 1 := by
    have hprod : 0 ≤ ((m : ℚ) - 2) * (4 * m + 6) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hm0 : 0 < (m : ℚ) := by linarith
  have hm1 : 0 < (m : ℚ) - 1 := by linarith
  have hp1 : 0 < (m : ℚ) + 1 := by linarith
  have h2m3 : 0 < 2 * (m : ℚ) - 3 := by linarith
  have h2m1 : 0 < 2 * (m : ℚ) - 1 := by linarith
  have h2p1 : 0 < 2 * (m : ℚ) + 1 := by linarith
  have hden :
      0 < (m : ℚ) * (m - 1) * (m + 1) * (2 * m - 3) * (2 * m - 1) * (2 * m + 1) := by
    positivity
  unfold lengthTwoRho
  exact div_pos (mul_pos (by norm_num) hnum) hden

/-- The sequence `lengthTwoRho` is strictly decreasing for natural indices `m ≥ 2`. -/
theorem lengthTwoRho_succ_lt (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoRho (m + 1) < lengthTwoRho m := by
  rw [← sub_pos]
  rw [lengthTwoRho_sub_succ m hm]
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hquad : 0 < 8 * (m : ℚ) ^ 2 + 4 * m - 9 := by
    have hprod : 0 ≤ ((m : ℚ) - 2) * (8 * m + 20) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hm0 : 0 < (m : ℚ) := by linarith
  have hm1 : 0 < (m : ℚ) - 1 := by linarith
  have hp1 : 0 < (m : ℚ) + 1 := by linarith
  have hp2 : 0 < (m : ℚ) + 2 := by linarith
  have h2m3 : 0 < 2 * (m : ℚ) - 3 := by linarith
  have h2m1 : 0 < 2 * (m : ℚ) - 1 := by linarith
  have h2p1 : 0 < 2 * (m : ℚ) + 1 := by linarith
  have h2p3 : 0 < 2 * (m : ℚ) + 3 := by linarith
  have hden :
      0 < (m : ℚ) * (m - 1) * (m + 1) * (m + 2) *
        (2 * m - 3) * (2 * m - 1) * (2 * m + 1) * (2 * m + 3) := by
    positivity
  exact div_pos (by positivity) hden

/-- The initial value of the root sequence is `rho_2 = 22/5`. -/
@[simp] theorem lengthTwoRho_two : lengthTwoRho 2 = 22 / 5 := by
  norm_num [lengthTwoRho]

/-- Uniform upper bound for the root in the length-two norm formula. -/
theorem lengthTwoRho_le_twentyTwo_fifths (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoRho m ≤ 22 / 5 := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      exact (lengthTwoRho_succ_lt m hm).le.trans ih

/-- The combined sign range needed in the length-two graded-unitarity proof:
`0 < rho_m ≤ 22/5` for every `m ≥ 2`. -/
theorem lengthTwoRho_mem_Ioc (m : ℕ) (hm : 2 ≤ m) :
    lengthTwoRho m ∈ Set.Ioc (0 : ℚ) (22 / 5) :=
  ⟨lengthTwoRho_pos m hm, lengthTwoRho_le_twentyTwo_fifths m hm⟩

/-- The central charge `c_{2,2n+1}` of the boundary Virasoro minimal model, regarded as a rational
number. -/
def boundaryMinimalCentralCharge (n : ℕ) : ℚ :=
  1 - 3 * (2 * (n : ℚ) - 1) ^ 2 / (2 * n + 1)

/-- Exact distance between `-c_{2,2n+1}` and the largest length-two root `22/5`. -/
theorem neg_boundaryMinimalCentralCharge_sub_twentyTwo_fifths (n : ℕ) :
    -boundaryMinimalCentralCharge n - 22 / 5 =
      6 * ((n : ℚ) - 2) * (10 * n + 1) / (5 * (2 * n + 1)) := by
  have hden : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  unfold boundaryMinimalCentralCharge
  field_simp [hden]
  ring

/-- For every boundary-model index `n ≥ 2`, one has `-c_{2,2n+1} ≥ 22/5`. -/
theorem neg_boundaryMinimalCentralCharge_sub_twentyTwo_fifths_nonneg
    (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ -boundaryMinimalCentralCharge n - 22 / 5 := by
  rw [neg_boundaryMinimalCentralCharge_sub_twentyTwo_fifths]
  have hnQ : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  positivity

end VirGradedUnitarity

end VOA
