/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningResidueFunctional
import VOA.Examples.VirasoroScreeningShiftCoefficient

/-!
# Actual screening mode coefficients expressed by residues

The finite oscillator coefficients and the auxiliary power-sum derivation
are compared in one linear functional. The resulting formulas describe
the actual charged modes, including their momentum and background terms.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open InverseDS.LeeYangFockVirasoro
open scoped BigOperators

/-- The monomial power-sum chain rule may be summed over the full energy
range: every index outside the occupation support contributes zero. -/
theorem screeningFunctional_raising_range (r s t n : ℕ) (d : ℕ →₀ ℕ)
    (hd : Finsupp.weight (fun k => k+1) d + n = r*s) :
    screeningFunctional r s t (powerSumRaising n (monomial d 1)) =
      ∑ i ∈ Finset.range (r*s), ((i+1:ℕ):ℚ) * (d i:ℚ) *
        screeningFunctional r s t
          (monomial (d - Finsupp.single i 1 + Finsupp.single (i+n) 1) 1) := by
  classical
  rw [powerSumRaising_monomial, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_subset
  · intro i hi
    have he := Finsupp.le_weight_of_ne_zero' (fun k : ℕ => k+1)
      (Finsupp.mem_support_iff.mp hi)
    dsimp only at he
    exact Finset.mem_range.mpr (by omega)
  · intro i hi hni
    simp [Finsupp.notMem_support_iff.mp hni]

/-- The actual shift coefficient is the screening prefactor times the
residue of the power-sum raising derivation. -/
theorem screeningFockState_shift_functional (r s t n : ℕ) (β : ℚ) (d : ℕ →₀ ℕ)
    (hd : Finsupp.weight (fun k => k+1) d + n = r*s) :
    coeff (fockOccupation d) (fockShiftDerivation n (screeningFockState r s t β)) =
      ((screeningPrefactor β d * screeningFunctional r s t
        (powerSumRaising n (monomial d 1))) : ℂ) := by
  rw [screeningFockState_shift_coeff r s t n β d hd,
    screeningFunctional_raising_range r s t n d hd]
  simp only [screeningFunctional_apply]

/-- A single actual oscillator derivative inserts its matching formal
power-sum variable into the residue. -/
theorem screeningFockState_derivative_functional (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (i : ℕ)
    (hd : Finsupp.weight (fun k => k+1) d + (i+1) = r*s) :
    coeff (fockOccupation d) (pderiv (i,0) (screeningFockState r s t β)) =
      ((β / ((i+1:ℕ):ℚ) * screeningPrefactor β d *
        screeningFunctional r s t (X i * monomial d 1)) : ℂ) := by
  rw [screeningFockState_pderiv_coeff r s t β d i hd, screeningFunctional_apply]
  congr 3
  rw [monomial_add_single, pow_one, mul_comm]

/-- Two derivatives at the first oscillator insert the square of the
first power sum; the repeated-occupation factorial is already cancelled. -/
theorem screeningFockState_second_derivative_functional (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (hd : Finsupp.weight (fun k => k+1) d + 2 = r*s) :
    coeff (fockOccupation d) (pderiv (0,0) (pderiv (0,0) (screeningFockState r s t β))) =
      ((β^2 * screeningPrefactor β d *
        screeningFunctional r s t (X 0 ^ 2 * monomial d 1)) : ℂ) := by
  have hw : Finsupp.weight (fun k => k+1) d + (0+1) + (0+1) = r*s := by omega
  rw [screeningFockState_two_pderiv_coeff r s t β d 0 0 hw, screeningFunctional_apply]
  have he : (monomial (d + Finsupp.single 0 1 + Finsupp.single 0 1) 1 : MvPolynomial ℕ ℚ) =
      X 0 ^ 2 * monomial d 1 := by
    rw [monomial_add_single, monomial_add_single, pow_one]
    ring
  rw [he]
  simp only [Nat.cast_zero, Nat.cast_one, Rat.cast_one, zero_add, div_one, pow_two]

/-- The coefficient of the actual first charged Virasoro mode is precisely
the first residue Ward expression, before the parameter substitution. -/
theorem screeningFockState_L1_coefficient (r s t : ℕ) (β ell p : ℚ)
    (d : ℕ →₀ ℕ) (hd : Finsupp.weight (fun k => k+1) d + 1 = r*s) :
    coeff (fockOccupation d)
      (sectorVirasoro (ell:ℂ) (p:ℂ) 1 (screeningFockState r s t β)) =
      ((screeningPrefactor β d *
        (screeningFunctional r s t (powerSumRaising 1 (monomial d 1)) +
          2*β*(p-2*ell)*screeningFunctional r s t (X 0 * monomial d 1))) : ℂ) := by
  rw [sectorVirasoro_one_differential, coeff_add, coeff_smul,
    screeningFockState_shift_functional r s t 1 β d hd,
    screeningFockState_derivative_functional r s t β d 0 hd]
  push_cast
  norm_num
  ring

/-- The actual second charged coefficient is the second residue expression:
the raising term, beta squared times p1 squared, and the momentum term p2. -/
theorem screeningFockState_L2_coefficient (r s t : ℕ) (β ell p : ℚ)
    (d : ℕ →₀ ℕ) (hd : Finsupp.weight (fun k => k+1) d + 2 = r*s) :
    coeff (fockOccupation d)
      (sectorVirasoro (ell:ℂ) (p:ℂ) 2 (screeningFockState r s t β)) =
      ((screeningPrefactor β d *
        (screeningFunctional r s t (powerSumRaising 2 (monomial d 1)) +
          β^2*screeningFunctional r s t (X 0 ^ 2 * monomial d 1) +
          2*β*(p-3*ell)*screeningFunctional r s t (X 1 * monomial d 1))) : ℂ) := by
  rw [sectorVirasoro_two_differential, coeff_add, coeff_add, coeff_smul,
    screeningFockState_shift_functional r s t 2 β d hd,
    screeningFockState_second_derivative_functional r s t β d hd,
    screeningFockState_derivative_functional r s t β d 1 hd]
  push_cast
  norm_num
  ring

end VOA.VirasoroScreening
