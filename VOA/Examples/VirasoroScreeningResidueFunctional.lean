/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningPowerSumDerivative
import VOA.Examples.VirasoroScreeningPairSums

/-!
# Screening residues as a linear functional on power sums

The residue becomes a rational linear functional on formal power-sum
polynomials. The two auxiliary Ward identities then become exact linear
relations between its values. Their coefficients use rational subtraction;
in particular the second identity remains correct at rank one.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra MvPolynomial

/-- The actual finite screening residue, after power-sum substitution,
as a rational linear functional. -/
noncomputable def screeningFunctional (r s t : ℕ) : MvPolynomial ℕ ℚ →ₗ[ℚ] ℚ :=
  (laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ))).comp
    ((LinearMap.mulLeft ℚ (vandermondeLaurent r^(2*t))).comp
      (powerSumLaurent r).toLinearMap)

/-- Evaluating the linear functional is exactly the existing screening moment. -/
theorem screeningFunctional_apply (r s t : ℕ) (P : MvPolynomial ℕ ℚ) :
    screeningFunctional r s t P =
      screeningMoment r s t (powerSumSubstitution (Fin r) P) := rfl

/-- The first unordered-pair multiplier is a single power sum times its
rational Ward coefficient. Positive rank permits removal of r-1's truncation. -/
theorem screening_first_multiplier (r s t : ℕ) (hr : 0 < r) :
    (((2*t:ℕ):ℚ) • (∑ ij ∈ variablePairs r,
        (screeningVariable r ij.1 + screeningVariable r ij.2)) -
      (((((r-1)*t+s:ℕ):ℤ)-1:ℤ):ℚ) • laurentPowerSum r 1) =
      (((r:ℚ)-1)*(t:ℚ)+1-(s:ℚ)) • laurentPowerSum r 1 := by
  rw [screening_pair_sum]
  have hp : laurentPowerSum r 1 = ∑ i : Fin r, screeningVariable r i := by
    simpa using laurentPowerSum_nat r 1
  rw [← hp, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← sub_smul]
  congr 1
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  push_cast
  ring

/-- The second pair multiplier is t times the square of the first power
sum plus the signed rational coefficient of the second power sum. -/
theorem screening_second_multiplier (r s t : ℕ) (hr : 0 < r) :
    (((2*t:ℕ):ℚ) • (∑ ij ∈ variablePairs r,
      (screeningVariable r ij.1^2 + screeningVariable r ij.1*screeningVariable r ij.2 +
        screeningVariable r ij.2^2)) -
      (((((r-1)*t+s:ℕ):ℤ)-2:ℤ):ℚ) • laurentPowerSum r 2) =
      (t:ℚ) • (laurentPowerSum r 1)^2 +
        (((r:ℚ)-2)*(t:ℚ)+2-(s:ℚ)) • laurentPowerSum r 2 := by
  have hp1 : laurentPowerSum r 1 = ∑ i : Fin r, screeningVariable r i := by
    simpa using laurentPowerSum_nat r 1
  have hp2 : laurentPowerSum r 2 = ∑ i : Fin r, screeningVariable r i^2 := by
    simpa using laurentPowerSum_nat r 2
  have hs := screening_pair_square r (screeningVariable r)
  rw [← hp1, ← hp2] at hs
  have he : (∑ ij ∈ variablePairs r,
      (screeningVariable r ij.1^2 + screeningVariable r ij.1*screeningVariable r ij.2 +
        screeningVariable r ij.2^2)) =
      (r-1) • laurentPowerSum r 2 +
        ∑ ij ∈ variablePairs r, screeningVariable r ij.1*screeningVariable r ij.2 := by
    rw [show (fun ij : Fin r × Fin r =>
      screeningVariable r ij.1^2 + screeningVariable r ij.1*screeningVariable r ij.2 +
        screeningVariable r ij.2^2) = (fun ij =>
      (screeningVariable r ij.1^2 + screeningVariable r ij.2^2) +
        screeningVariable r ij.1*screeningVariable r ij.2) by funext ij; ring,
      Finset.sum_add_distrib, screening_pair_sum r (fun i => screeningVariable r i^2), ← hp2]
  rw [he, hs, ← Nat.cast_smul_eq_nsmul ℚ]
  simp only [two_mul]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  push_cast
  module

/-- The first actual residue Ward identity, entirely in the finite
polynomial algebra of power sums. -/
theorem screeningFunctional_first_ward (r s t : ℕ) (hr : 0 < r)
    (P : MvPolynomial ℕ ℚ) :
    screeningFunctional r s t (powerSumRaising 1 P) +
      (((r:ℚ)-1)*(t:ℚ)+1-(s:ℚ)) * screeningFunctional r s t (X 0 * P) = 0 := by
  have h := screening_residue_first_ward r s t (powerSumLaurent r P)
  have hw := screeningVectorField_powerSumLaurent r 1 P
  norm_num only [Nat.cast_ofNat] at hw
  rw [screening_first_multiplier r s t hr, hw] at h
  have hx : powerSumLaurent r (X 0) = laurentPowerSum r 1 := by
    simpa using powerSumLaurent_X r 0
  change laurentCoefficient _ (_ + _) = 0 at h
  rw [map_add, smul_mul_assoc, smul_mul_assoc, map_smul] at h
  simp only [smul_eq_mul] at h
  have h0 : screeningFunctional r s t (X 0 * P) =
      laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ))
        ((laurentPowerSum r 1 * vandermondeLaurent r^(2*t)) * powerSumLaurent r P) := by
    change laurentCoefficient _ (_ * powerSumLaurent r _) = _
    rw [map_mul (powerSumLaurent r), hx]
    congr 1
    ring
  rw [h0]
  exact h

/-- The second actual residue Ward identity includes both power-sum
insertions, with no natural subtraction in its scalar coefficient. -/
theorem screeningFunctional_second_ward (r s t : ℕ) (hr : 0 < r)
    (P : MvPolynomial ℕ ℚ) :
    screeningFunctional r s t (powerSumRaising 2 P) +
      (t:ℚ) * screeningFunctional r s t (X 0 ^ 2 * P) +
      (((r:ℚ)-2)*(t:ℚ)+2-(s:ℚ)) * screeningFunctional r s t (X 1 * P) = 0 := by
  have h := screening_residue_second_ward r s t (powerSumLaurent r P)
  have hw := screeningVectorField_powerSumLaurent r 2 P
  norm_num only [Nat.cast_ofNat] at hw
  rw [screening_second_multiplier r s t hr, hw] at h
  have hx0 : powerSumLaurent r (X 0) = laurentPowerSum r 1 := by
    simpa using powerSumLaurent_X r 0
  have hx1 : powerSumLaurent r (X 1) = laurentPowerSum r 2 := by
    simpa using powerSumLaurent_X r 1
  change laurentCoefficient _ (_ + _) = 0 at h
  simp only [add_mul, smul_mul_assoc, map_add, map_smul] at h
  simp only [smul_eq_mul] at h
  have h0 : screeningFunctional r s t (X 0 ^ 2 * P) =
      laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ)) (((laurentPowerSum r 1)^2 * vandermondeLaurent r^(2*t)) *
        powerSumLaurent r P) := by
    change laurentCoefficient _ (_ * powerSumLaurent r _) = _
    rw [map_mul (powerSumLaurent r), map_pow (powerSumLaurent r), hx0]
    congr 1
    ring
  have h1 : screeningFunctional r s t (X 1 * P) =
      laurentCoefficient (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ)) ((laurentPowerSum r 2 * vandermondeLaurent r^(2*t)) *
        powerSumLaurent r P) := by
    change laurentCoefficient _ (_ * powerSumLaurent r _) = _
    rw [map_mul (powerSumLaurent r), hx1]
    congr 1
    ring
  rw [h0,h1]
  exact (add_assoc _ _ _).trans h

end VOA.VirasoroScreening
