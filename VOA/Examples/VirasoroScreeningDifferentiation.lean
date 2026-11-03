/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningFactorial

/-!
# Actual screening derivative coefficients

Differentiation increases the occupation read from the source by one. The
new multiplicity cancels its factorial, leaving beta divided by the mode
energy. Applying the same statement twice automatically handles coincident
indices; no assumption that the two oscillators are different is needed.
All identities refer to the actual finite complex Fock polynomial.
-/
namespace VOA.VirasoroScreening
open HeisenbergN

/-- The one-colour embedding preserves each oscillator multiplicity. -/
theorem fockOccupation_apply (d : ℕ →₀ ℕ) (i : ℕ) : fockOccupation d (i,0) = d i := by
  exact Finsupp.mapDomain_apply (fun _ _ h => congrArg Prod.fst h) d i

/-- Adding an oscillator commutes with the one-colour embedding. -/
theorem fockOccupation_add_single (d : ℕ →₀ ℕ) (i : ℕ) :
    fockOccupation (d + Finsupp.single i 1) =
      fockOccupation d + Finsupp.single (i,0) 1 := by
  simp [fockOccupation, Finsupp.mapDomain_add]

/-- After cancelling the new multiplicity, one derivative leaves beta
 divided by the positive mode energy. -/
theorem screeningPrefactor_derivative (β : ℚ) (d : ℕ →₀ ℕ) (i : ℕ) :
    ((d i+1:ℕ):ℚ) * screeningPrefactor β (d + Finsupp.single i 1) =
      (β / ((i+1:ℕ):ℚ)) * screeningPrefactor β d := by
  have h := screeningPrefactor_add_single β d i
  have hi : ((i+1:ℕ):ℚ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hi)
  calc
    _ = β * screeningPrefactor β d := by simpa only [mul_assoc] using h
    _ = _ := by field_simp

/-- Inserting an oscillator inserts the matching power sum in the exact
auxiliary monomial. The substitution is an algebra map, so there is no
formal exponential series to justify. -/
theorem screening_powerSum_add_single (r : ℕ) (d : ℕ →₀ ℕ) (i : ℕ) :
    powerSumSubstitution (Fin r) (MvPolynomial.monomial (d + Finsupp.single i 1) 1) =
      powerSumSubstitution (Fin r) (MvPolynomial.monomial d 1) *
        MvPolynomial.psum (Fin r) ℚ (i+1) := by
  rw [MvPolynomial.monomial_add_single, pow_one, map_mul]
  simp [powerSumSubstitution]

/-- Exact coefficient of the first derivative of the ACTUAL finite
screening state at every occupation of the required output energy. -/
theorem screeningFockState_pderiv_coeff (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (i : ℕ)
    (hd : Finsupp.weight (fun j => j+1) d + (i+1) = r*s) :
    MvPolynomial.coeff (fockOccupation d)
      (MvPolynomial.pderiv (i,0) (screeningFockState r s t β)) =
      ((β / ((i+1:ℕ):ℚ) * screeningPrefactor β d *
        screeningMoment r s t (powerSumSubstitution (Fin r)
          (MvPolynomial.monomial (d + Finsupp.single i 1) 1))) : ℂ) := by
  rw [screening_pderiv_coeff, fockOccupation_apply, ← fockOccupation_add_single]
  have hw : Finsupp.weight weightFnN (fockOccupation (d + Finsupp.single i 1)) = r*s := by
    rw [fockOccupation_weight, map_add, Finsupp.weight_single]
    simpa using hd
  rw [screeningFockState_coeff r s t β _ hw, plain_fockOccupation, screeningFockCoefficient]
  norm_cast
  rw [← mul_assoc, screeningPrefactor_derivative]

/-- Exact coefficients after TWO oscillator derivatives, including equal
indices. Repeated occurrences are handled by the two factorial cancellations. -/
theorem screeningFockState_two_pderiv_coeff (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (i j : ℕ)
    (hd : Finsupp.weight (fun k => k+1) d + (i+1) + (j+1) = r*s) :
    MvPolynomial.coeff (fockOccupation d)
      (MvPolynomial.pderiv (i,0) (MvPolynomial.pderiv (j,0) (screeningFockState r s t β))) =
      (((β / ((i+1:ℕ):ℚ)) * (β / ((j+1:ℕ):ℚ)) * screeningPrefactor β d *
        screeningMoment r s t (powerSumSubstitution (Fin r)
          (MvPolynomial.monomial (d + Finsupp.single i 1 + Finsupp.single j 1) 1))) : ℂ) := by
  rw [screening_pderiv_coeff, fockOccupation_apply, ← fockOccupation_add_single]
  have hw : Finsupp.weight (fun k => k+1) (d + Finsupp.single i 1) + (j+1) = r*s := by
    rw [map_add, Finsupp.weight_single]
    simpa using hd
  rw [screeningFockState_pderiv_coeff r s t β _ j hw]
  norm_cast
  have h := screeningPrefactor_derivative β d i
  linear_combination (β / ((j+1:ℕ):ℚ) *
    screeningMoment r s t (powerSumSubstitution (Fin r)
      (MvPolynomial.monomial (d + Finsupp.single i 1 + Finsupp.single j 1) 1))) * h

end VOA.VirasoroScreening
