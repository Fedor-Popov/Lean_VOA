/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningDifferentiation

/-!
# Moving one oscillator inside the actual screening polynomial

A shift term first differentiates at one oscillator and then multiplies by
another. The two factorial cancellations turn its coefficient into the
corresponding power-sum derivative: the output multiplicity, multiplied by
its energy. These statements concern each actual finite polynomial term;
summing the shift derivation and applying the residue Ward identities is
still a separate step.
-/
namespace VOA.VirasoroScreening
open HeisenbergN

/-- Removing an oscillator commutes with the one-colour occupation embedding.
There is no positivity premise: both sides use natural truncated subtraction. -/
theorem fockOccupation_sub_single (d : ℕ →₀ ℕ) (i : ℕ) :
    fockOccupation (d - Finsupp.single i 1) =
      fockOccupation d - Finsupp.single (i,0) 1 := by
  ext ⟨j,a⟩
  have ha : a=0 := Subsingleton.elim _ _
  subst a
  simp only [fockOccupation_apply, Finsupp.tsub_apply]
  by_cases h : j=i
  · subst j; simp
  · simp [h, Ne.symm h]

/-- Removing a present oscillator reverses the factorial cancellation.
This identity avoids division by beta and remains true when beta is zero. -/
theorem screeningPrefactor_remove (β : ℚ) (d : ℕ →₀ ℕ) (i : ℕ) (hi : 0<d i) :
    ((i+1:ℕ):ℚ) * (d i:ℚ) * screeningPrefactor β d =
      β * screeningPrefactor β (d - Finsupp.single i 1) := by
  have hr : d - Finsupp.single i 1 + Finsupp.single i 1 = d := by
    ext k
    by_cases hk : k=i
    · subst k
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.tsub_apply, hk, Ne.symm hk]
  have h := screeningPrefactor_add_single β (d - Finsupp.single i 1) i
  rw [hr] at h
  have he : ((d - Finsupp.single i 1 : ℕ →₀ ℕ) i) + 1 = d i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  simpa only [he] using h

/-- Exact coefficient of one oscillator-migration term. Its input and output
energies are explicit, so no untruncated exponential is being differentiated. -/
theorem screeningFockState_migration_coeff (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (i j : ℕ) (hi : 0<d i)
    (hd : Finsupp.weight (fun k => k+1) (d - Finsupp.single i 1) + (j+1) = r*s) :
    ((j+1:ℕ):ℂ) * MvPolynomial.coeff (fockOccupation d)
      (MvPolynomial.X (i,0) *
        MvPolynomial.pderiv (j,0) (screeningFockState r s t β)) =
      ((((i+1:ℕ):ℚ) * (d i:ℚ) * screeningPrefactor β d *
        screeningMoment r s t (powerSumSubstitution (Fin r)
          (MvPolynomial.monomial
            (d - Finsupp.single i 1 + Finsupp.single j 1) 1))) : ℂ) := by
  classical
  rw [MvPolynomial.coeff_X_mul', if_pos (by
    simpa only [Finsupp.mem_support_iff, fockOccupation_apply] using (Nat.ne_of_gt hi)),
    ← fockOccupation_sub_single, screeningFockState_pderiv_coeff r s t β _ j hd]
  norm_cast
  have hj : ((j+1:ℕ):ℚ) ≠ 0 := by positivity
  simp only [Nat.cast_mul]
  rw [screeningPrefactor_remove β d i hi]
  field_simp

/-- Multiplication by an absent output oscillator contributes zero. Together
with the preceding formula this covers every occupation, including boundaries. -/
theorem screeningFockState_migration_coeff_zero (r s t : ℕ) (β : ℚ)
    (d : ℕ →₀ ℕ) (i j : ℕ) (hi : d i=0) :
    MvPolynomial.coeff (fockOccupation d)
      (MvPolynomial.X (i,0) *
        MvPolynomial.pderiv (j,0) (screeningFockState r s t β)) = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul', if_neg]
  simpa only [Finsupp.mem_support_iff, fockOccupation_apply, hi, ne_eq, not_true_eq_false,
    not_false_eq_true]

end VOA.VirasoroScreening
