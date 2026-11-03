/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QBinomialSum

/-!
# Summing the three residual species

Equation (5.15) of Arakawa--Dai: the three locally finite sums reduce to
`(q)_n^2 / ((q)_infinity^2 (q)_(2n+1))`.
-/

namespace VOA.QSeries
open scoped BigOperators
variable {R : Type*} [CommRing R]
noncomputable section

/-- The three residual sums, with their positive exponents made explicit. -/
def residualSum (n : ℕ) : PowerSeries R :=
  powerShiftSum (n + 1) fun s =>
    reciprocalQFactorial s * eulerSum (n + s + 1) *
      eulerSum (n + 1) * reciprocalQFactorial n

/-- Sum the two independent species first, using Euler's identity. -/
theorem residualSum_eq_qBinomial (n : ℕ) :
    (residualSum n : PowerSeries R) =
      qBinomialSum (n + 1) (n + 1) * qFactorial PowerSeries.X n * reciprocalEuler ^ 2 := by
  unfold residualSum
  have hf : (fun s => (reciprocalQFactorial s : PowerSeries R) * eulerSum (n + s + 1) *
      eulerSum (n + 1) * reciprocalQFactorial n) =
      (fun s => qBinomialCoeff (PowerSeries.X ^ (n + 1)) s *
        (qFactorial PowerSeries.X n * reciprocalEuler ^ 2)) := by
    funext s
    rw [eulerSum_eq (n + s + 1) (by omega), eulerSum_eq (n + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [qFactorial_add]
    unfold qBinomialCoeff
    calc
      _ = (pochhammer (PowerSeries.X ^ (n + 1)) PowerSeries.X s *
          reciprocalQFactorial s) * (qFactorial PowerSeries.X n * reciprocalEuler ^ 2) *
          (qFactorial PowerSeries.X n * (reciprocalQFactorial n : PowerSeries R)) := by ring
      _ = _ := by rw [qFactorial_mul_reciprocal, mul_one]
  rw [hf, powerShiftSum_mul (n + 1) (by omega)]
  simp only [qBinomialSum, mul_assoc]

/-- The residual-species identity, including the boundary case `n=0`. -/
theorem residualSum_eq (n : ℕ) :
    (residualSum n : PowerSeries R) =
      qFactorial PowerSeries.X n ^ 2 * reciprocalEuler ^ 2 *
        reciprocalQFactorial (2 * n + 1) := by
  rw [residualSum_eq_qBinomial, qBinomialSum_eq (n + 1) (n + 1) (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  have hi : n + 1 + (n + 1) - 1 = 2 * n + 1 := by omega
  rw [hi]
  ring

/-- Equality of all coefficients through a fixed truncation. -/
def TruncEq (D : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ i, i ≤ D → PowerSeries.coeff i f = PowerSeries.coeff i g

@[refl] theorem TruncEq.refl (D : ℕ) (f : PowerSeries R) : TruncEq D f f :=
  fun _ _ => rfl

theorem TruncEq.mul {D : ℕ} {f g h k : PowerSeries R}
    (hf : TruncEq D f g) (hh : TruncEq D h k) : TruncEq D (f * h) (g * k) := by
  intro i hi
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega), hh ij.2 (by omega)]

/-- A common cutoff computes every coefficient through `D` of a positive-order sum. -/
theorem truncEq_powerShiftSum (A : ℕ) (hA : 0 < A)
    (B : ℕ → PowerSeries R) (D : ℕ) :
    TruncEq D (powerShiftSum A B)
      (∑ j ∈ Finset.range (D + 1), PowerSeries.X ^ (A * j) * B j) :=
  fun i hi => coeff_powerShiftSum A hA B i D hi

/-- The nested definition is exactly the paper's three-variable sum, degree by degree,
with a proved sufficient finite cube cutoff. -/
theorem coeff_residualSum (n D : ℕ) :
    PowerSeries.coeff D (residualSum n : PowerSeries R) =
      PowerSeries.coeff D
        (∑ s ∈ Finset.range (D + 1), ∑ t ∈ Finset.range (D + 1),
          ∑ c ∈ Finset.range (D + 1),
          PowerSeries.X ^ ((n + 1) * (s + t + c) + s * t) *
            reciprocalQFactorial n * reciprocalQFactorial s *
              reciprocalQFactorial t * reciprocalQFactorial c) := by
  rw [residualSum, coeff_powerShiftSum (n + 1) (by omega) _ D D le_rfl, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  let T : PowerSeries R := ∑ t ∈ Finset.range (D + 1),
    PowerSeries.X ^ ((n + s + 1) * t) * reciprocalQFactorial t
  let C : PowerSeries R := ∑ c ∈ Finset.range (D + 1),
    PowerSeries.X ^ ((n + 1) * c) * reciprocalQFactorial c
  have ht : TruncEq D (eulerSum (n + s + 1) : PowerSeries R) T :=
    truncEq_powerShiftSum _ (by omega) _ D
  have hc : TruncEq D (eulerSum (n + 1) : PowerSeries R) C :=
    truncEq_powerShiftSum _ (by omega) _ D
  have he := (TruncEq.refl D (PowerSeries.X ^ ((n + 1) * s))).mul
    ((((TruncEq.refl D (reciprocalQFactorial s)).mul ht).mul hc).mul
      (TruncEq.refl D (reciprocalQFactorial n)))
  rw [he D le_rfl]
  congr 1
  dsimp [T, C]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro c _
  have hexp : (n + 1) * (s + t + c) + s * t =
      (n + 1) * s + (n + s + 1) * t + (n + 1) * c := by ring
  rw [hexp, pow_add, pow_add]
  ring

end
end VOA.QSeries
