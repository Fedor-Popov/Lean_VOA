/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningIntegration
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The finite power-sum chain rule

The auxiliary vector field sends the kth power sum to k times the
(k+n)th power sum. We realize this rule as a derivation of the polynomial
algebra on formal power-sum variables, then prove compatibility with actual
Laurent substitution on every polynomial. No independence of the power
sums, analytic series or extra representation assumption is needed.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra

/-- Positive Laurent power sums are sums of ordinary powers of the
auxiliary variables. This fixes the integer-exponent convention. -/
theorem laurentPowerSum_nat (r k : ℕ) :
    laurentPowerSum r k = ∑ i : Fin r, screeningVariable r i ^ k := by
  simp only [laurentPowerSum, screeningVariable, single_pow, one_pow]
  congr 1

/-- The actual finite Laurent vector field raises a power sum by n and
multiplies it by its original positive exponent. -/
theorem screeningVectorField_powerSum (r n k : ℕ) :
    screeningVectorField r n (laurentPowerSum r k) =
      (k:ℚ) • laurentPowerSum r ((k+n:ℕ):ℤ) := by
  rw [laurentPowerSum_nat, laurentPowerSum_nat, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : screeningVectorField r n (screeningVariable r i) =
      screeningVariable r i ^ n * screeningVariable r i := by
    rw [screeningVectorField_variable, pow_succ]
  rw [screeningVectorField_power r n _ _ h k]
  congr 1
  rw [← pow_add, Nat.add_comm]

/-- Substituting ordinary power sums and then embedding into Laurent
polynomials is one algebra map. -/
noncomputable def powerSumLaurent (r : ℕ) :
    MvPolynomial ℕ ℚ →ₐ[ℚ] Laurent (Fin r → ℤ) :=
  (auxiliaryLaurent r).comp (powerSumSubstitution (Fin r))

/-- The formal variable i represents the power sum of positive degree i+1. -/
theorem powerSumLaurent_X (r i : ℕ) :
    powerSumLaurent r (MvPolynomial.X i) = laurentPowerSum r ((i+1:ℕ):ℤ) := by
  rw [laurentPowerSum_nat]
  simp [powerSumLaurent, powerSumSubstitution, MvPolynomial.psum,
    auxiliaryLaurent, screeningVariable]

/-- Raising formal power sums by n, with their original degree as coefficient,
is a genuine polynomial derivation. -/
noncomputable def powerSumRaising (n : ℕ) :
    Derivation ℚ (MvPolynomial ℕ ℚ) (MvPolynomial ℕ ℚ) :=
  MvPolynomial.mkDerivation ℚ (fun i => ((i+1:ℕ):ℚ) • MvPolynomial.X (i+n))

/-- Substitution intertwines the formal power-sum derivation with the
actual auxiliary Laurent vector field on every finite polynomial. -/
theorem screeningVectorField_powerSumLaurent (r n : ℕ) (P : MvPolynomial ℕ ℚ) :
    screeningVectorField r n (powerSumLaurent r P) =
      powerSumLaurent r (powerSumRaising n P) := by
  have h1 : screeningVectorField r n 1 = 0 := by
    have h := screeningVectorField_mul r n 1 1
    simp only [one_mul, mul_one] at h
    linear_combination -h
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.C_eq_smul_one]
    simp [h1]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, screeningVectorField_mul, hP, powerSumLaurent_X,
      screeningVectorField_powerSum, (powerSumRaising n).leibniz]
    simp only [powerSumRaising, MvPolynomial.mkDerivation_X, map_add,
      map_smul, smul_eq_mul, map_mul, powerSumLaurent_X]
    have he : i+1+n=i+n+1 := by omega
    rw [he]
    ring

/-- The finite monomial chain rule. A chosen occurrence of power sum i+1
is replaced by i+n+1; its multiplicity and its old degree are the coefficient. -/
theorem powerSumRaising_monomial (n : ℕ) (d : ℕ →₀ ℕ) :
    powerSumRaising n (MvPolynomial.monomial d 1) =
      ∑ i ∈ d.support, (((i+1:ℕ):ℚ) * (d i:ℚ)) •
        MvPolynomial.monomial (d - Finsupp.single i 1 + Finsupp.single (i+n) 1) 1 := by
  classical
  rw [powerSumRaising, MvPolynomial.mkDerivation_monomial, one_smul]
  change (∑ i ∈ d.support, MvPolynomial.monomial (d - Finsupp.single i 1) (d i:ℚ) •
    (((i+1:ℕ):ℚ) • MvPolynomial.X (i+n))) = _
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul, MvPolynomial.X, MvPolynomial.monomial_mul,
    MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

end VOA.VirasoroScreening
