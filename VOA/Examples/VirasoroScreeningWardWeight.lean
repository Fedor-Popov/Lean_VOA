/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningDerivation

/-!
# Polynomial Ward identities for the screening weight

All identities live in the finite Laurent algebra. Differentiating each
Vandermonde factor gives a polynomial multiple of that factor; hence no
inverse differences or assumptions about distinct numerical variables occur.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra

/-- A single auxiliary variable as a Laurent monomial. -/
noncomputable def screeningVariable (r : ℕ) (i : Fin r) : Laurent (Fin r → ℤ) :=
  single (unitExponent r i) 1

/-- The vector field sends z_i to z_i^(n+1), with all other summands zero. -/
theorem screeningVectorField_variable (r n : ℕ) (j : Fin r) :
    screeningVectorField r n (screeningVariable r j) = screeningVariable r j^(n+1) := by
  classical
  simp only [screeningVectorField, screeningVariable, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, laurentEuler_single]
  rw [Finset.sum_eq_single j]
  · simp only [unitExponent, Pi.single_eq_same, Int.cast_one, mul_one,
      single_mul_single, single_pow, one_pow]
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  · intro i hi hij
    simp [unitExponent, Pi.single_eq_of_ne hij]
    rfl
  · simp

/-- A product of polynomial eigenvectors has logarithmic multiplier the
sum of the individual multipliers, without ever dividing by the factors. -/
theorem screeningVectorField_product {I : Type*} (r : ℕ) (n : ℤ)
    (S : Finset I) (P Q : I → Laurent (Fin r → ℤ))
    (h : ∀ i ∈ S, screeningVectorField r n (P i) = Q i*P i) :
    screeningVectorField r n (∏ i ∈ S, P i) = (∑ i ∈ S, Q i)*(∏ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h1 : screeningVectorField r n 1 = 0 := by
      have hh := screeningVectorField_mul r n 1 1
      simp only [one_mul, mul_one] at hh
      linear_combination -hh
    simp [h1]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, screeningVectorField_mul,
      h i (Finset.mem_insert_self i S), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    ring

/-- Raising a polynomial eigenvector to a natural power multiplies its
logarithmic multiplier by that power. -/
theorem screeningVectorField_power (r : ℕ) (n : ℤ)
    (P Q : Laurent (Fin r → ℤ)) (h : screeningVectorField r n P = Q*P) (k : ℕ) :
    screeningVectorField r n (P^k) = (k:ℚ) • (Q*P^k) := by
  induction k with
  | zero =>
    have hh := screeningVectorField_mul r n 1 1
    simp only [one_mul, mul_one] at hh
    simp only [pow_zero, Nat.cast_zero, zero_smul]
    linear_combination -hh
  | succ k ih =>
    rw [pow_succ, screeningVectorField_mul, ih, h]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, smul_mul_assoc]
    congr 1 <;> ring

/-- First Ward differentiation of the entire Vandermonde weight. The
multiplier is the finite sum of z_i+z_j over its unordered pairs. -/
theorem screeningVectorField_one_vandermonde (r t : ℕ) :
    screeningVectorField r 1 (vandermondeLaurent r^(2*t)) =
      (2*t:ℕ) • ((∑ ij ∈ variablePairs r,
        (screeningVariable r ij.1 + screeningVariable r ij.2)) *
          vandermondeLaurent r^(2*t)) := by
  have h : screeningVectorField r 1 (vandermondeLaurent r) =
      (∑ ij ∈ variablePairs r, (screeningVariable r ij.1 + screeningVariable r ij.2)) *
        vandermondeLaurent r := by
    apply screeningVectorField_product
    intro ij hij
    change screeningVectorField r (1:ℕ) (screeningVariable r ij.1 - screeningVariable r ij.2) = _
    rw [map_sub, screeningVectorField_variable, screeningVectorField_variable]
    norm_num
    unfold screeningVariable
    ring
  simpa only [Nat.cast_smul_eq_nsmul] using screeningVectorField_power r 1 _ _ h (2*t)

/-- Second Ward differentiation of the entire Vandermonde weight. Each
pair contributes z_i squared plus z_i*z_j plus z_j squared. -/
theorem screeningVectorField_two_vandermonde (r t : ℕ) :
    screeningVectorField r 2 (vandermondeLaurent r^(2*t)) =
      (2*t:ℕ) • ((∑ ij ∈ variablePairs r,
        (screeningVariable r ij.1^2 + screeningVariable r ij.1*screeningVariable r ij.2 +
          screeningVariable r ij.2^2)) * vandermondeLaurent r^(2*t)) := by
  have h : screeningVectorField r 2 (vandermondeLaurent r) =
      (∑ ij ∈ variablePairs r, (screeningVariable r ij.1^2 +
        screeningVariable r ij.1*screeningVariable r ij.2 + screeningVariable r ij.2^2)) *
        vandermondeLaurent r := by
    apply screeningVectorField_product
    intro ij hij
    change screeningVectorField r (2:ℕ) (screeningVariable r ij.1 - screeningVariable r ij.2) = _
    rw [map_sub, screeningVectorField_variable, screeningVectorField_variable]
    norm_num
    unfold screeningVariable
    ring
  simpa only [Nat.cast_smul_eq_nsmul] using screeningVectorField_power r 2 _ _ h (2*t)

end VOA.VirasoroScreening
