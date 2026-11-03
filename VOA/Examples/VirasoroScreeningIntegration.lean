/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningWardWeight

/-!
# Finite coefficient integration by parts

At a common target exponent D, the sum of z_i^(n+1) partial_i has the same
coefficient as (D-n) times multiplication by the nth power sum. Combining
this with the proved Vandermonde product rule gives the two exact residue
Ward identities for every Laurent test expression. These concern the
auxiliary residue; the actual Fock positive-mode identification is separate.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra

/-- Reading one Laurent coefficient is a rational linear functional. -/
noncomputable def laurentCoefficient {r : ℕ} (e : Fin r → ℤ) :
    Laurent (Fin r → ℤ) →ₗ[ℚ] ℚ where
  toFun P := P e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite power sum, allowing any signed integer power. -/
noncomputable def laurentPowerSum (r : ℕ) (n : ℤ) : Laurent (Fin r → ℤ) :=
  ∑ i : Fin r, single (n • unitExponent r i) 1

/-- Exact integration by parts at a uniform multiexponent. No contour,
convergence or vanishing boundary condition is involved. -/
theorem screening_coefficient_integration (r : ℕ) (n D : ℤ)
    (P : Laurent (Fin r → ℤ)) :
    laurentCoefficient (fun _ => D) (screeningVectorField r n P) =
      ((D-n:ℤ):ℚ) * laurentCoefficient (fun _ => D) (laurentPowerSum r n * P) := by
  change screeningVectorField r n P (fun _ => D) = _
  rw [screeningVectorField_apply]
  simp only [laurentPowerSum, Finset.sum_mul, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = ((D-n:ℤ):ℚ) * ((single (n • unitExponent r i) 1 * P : Laurent (Fin r → ℤ)) (fun _ => D))
  rw [single_mul_apply, one_mul]
  simp only [sub_eq_add_neg, add_comm]

/-- A polynomial logarithmic derivative of a weight yields a finite residue
Ward identity. This general product-rule lemma will be applied to the two
explicit Vandermonde derivatives, not taken as a representation assumption. -/
theorem screening_coefficient_ward (r : ℕ) (n D : ℤ)
    (W K P : Laurent (Fin r → ℤ))
    (hW : screeningVectorField r n W = K*W) :
    laurentCoefficient (fun _ => D)
      (W*screeningVectorField r n P +
        (K - ((D-n:ℤ):ℚ) • laurentPowerSum r n)*W*P) = 0 := by
  have h := screening_coefficient_integration r n D (W*P)
  rw [screeningVectorField_mul, hW, map_add] at h
  have he : W*screeningVectorField r n P +
      (K - ((D-n:ℤ):ℚ) • laurentPowerSum r n)*W*P =
      W*screeningVectorField r n P + K*W*P -
        ((D-n:ℤ):ℚ) • (laurentPowerSum r n*(W*P)) := by
    simp only [sub_mul, smul_mul_assoc]
    ring
  rw [he, map_sub, map_add, map_smul]
  change _ + _ - ((D-n:ℤ):ℚ) * _ = 0
  linear_combination h

/-- The exact first residue Ward identity for the actual Vandermonde
weight and every finite Laurent test expression. -/
theorem screening_residue_first_ward (r s t : ℕ) (P : Laurent (Fin r → ℤ)) :
    laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ))
      (vandermondeLaurent r^(2*t)*screeningVectorField r 1 P +
        (((2*t:ℕ):ℚ) • (∑ ij ∈ variablePairs r,
          (screeningVariable r ij.1 + screeningVariable r ij.2)) -
          (((((r-1)*t+s:ℕ):ℤ)-1:ℤ):ℚ) • laurentPowerSum r 1) *
            vandermondeLaurent r^(2*t)*P) = 0 := by
  apply screening_coefficient_ward
  simpa only [smul_mul_assoc, Nat.cast_smul_eq_nsmul] using
    screeningVectorField_one_vandermonde r t

/-- The exact second residue Ward identity. Its target-exponent subtraction
is integral, so it remains valid even below degree two. -/
theorem screening_residue_second_ward (r s t : ℕ) (P : Laurent (Fin r → ℤ)) :
    laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ))
      (vandermondeLaurent r^(2*t)*screeningVectorField r 2 P +
        (((2*t:ℕ):ℚ) • (∑ ij ∈ variablePairs r,
          (screeningVariable r ij.1^2 + screeningVariable r ij.1*screeningVariable r ij.2 +
            screeningVariable r ij.2^2)) -
          (((((r-1)*t+s:ℕ):ℤ)-2:ℤ):ℚ) • laurentPowerSum r 2) *
            vandermondeLaurent r^(2*t)*P) = 0 := by
  apply screening_coefficient_ward
  simpa only [smul_mul_assoc, Nat.cast_smul_eq_nsmul] using
    screeningVectorField_two_vandermonde r t

end VOA.VirasoroScreening
