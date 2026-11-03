/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QEuler

/-!
# The infinite q-binomial theorem at positive integral powers

For `A,B > 0`, the algebraic sum `(q^B;q)_j q^(A*j)/(q)_j` is
`(q)_(A-1)/(q)_(A+B-1)`. This is the precise positive-order specialization
used in the residual-variable summation of Arakawa--Dai.
-/

namespace VOA.QSeries

open scoped BigOperators
variable {R : Type*} [CommRing R]
noncomputable section

/-- The positive-order q-binomial sum. -/
def qBinomialSum (A B : ℕ) : PowerSeries R :=
  powerShiftSum A (qBinomialCoeff (PowerSeries.X ^ B))

/-- The coefficient recurrence induces the q-binomial functional equation after substitution. -/
theorem qBinomialSum_recurrence (A B : ℕ) (hA : 0 < A) :
    (1 - PowerSeries.X ^ A) * (qBinomialSum A B : PowerSeries R) =
      (1 - PowerSeries.X ^ (A + B)) * qBinomialSum (A + 1) B := by
  let C : ℕ → PowerSeries R := qBinomialCoeff (PowerSeries.X ^ B)
  let D : ℕ → PowerSeries R := fun j => (1 - PowerSeries.X ^ j) * C j
  have hD0 : D 0 = 0 := by simp [D]
  have hDsucc : ∀ j, D (j + 1) = (1 - PowerSeries.X ^ (B + j)) * C j := by
    intro j
    simpa only [D, C, pow_add] using qBinomialCoeff_recurrence (PowerSeries.X ^ B) j
  have hs := powerShiftSum_succ A hA D
  rw [hD0, zero_add] at hs
  have ht : powerShiftSum A (fun j => D (j + 1)) =
      qBinomialSum A B - PowerSeries.X ^ B * qBinomialSum (A + 1) B := by
    have hf : powerShiftSum A (fun j => D (j + 1)) =
        powerShiftSum A (fun j => C j - (PowerSeries.X ^ j * C j) * PowerSeries.X ^ B) := by
      apply powerShiftSum_congr
      intro j
      rw [hDsucc, pow_add]
      ring
    rw [hf, powerShiftSum_sub A hA, powerShiftSum_mul A hA]
    have hshift := powerShiftSum_add_exponent A 1 C
    simp only [Nat.one_mul] at hshift
    rw [← hshift]
    simp only [qBinomialSum, C]
    ring
  rw [ht] at hs
  have hd : qBinomialSum A B - qBinomialSum (A + 1) B = powerShiftSum A D := by
    rw [qBinomialSum, qBinomialSum, powerShiftSum_add_exponent A 1]
    simp only [Nat.one_mul]
    rw [← powerShiftSum_sub A hA]
    apply powerShiftSum_congr
    intro j
    simp only [D, C]
    ring
  rw [hs] at hd
  rw [pow_add]
  linear_combination hd

/-- Far enough along the parameter sequence, every fixed truncation equals `1`. -/
theorem coeff_qBinomialSum_of_lt (A B d : ℕ) (hd : d < A) :
    PowerSeries.coeff d (qBinomialSum A B : PowerSeries R) = PowerSeries.coeff d 1 := by
  rw [qBinomialSum, coeff_powerShiftSum A (by omega) _ d d le_rfl, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [PowerSeries.coeff_X_pow_mul']
    have hAj : A ≤ A * j := by have hjpos := Nat.pos_of_ne_zero hj; nlinarith
    simp [show ¬ A * j ≤ d by omega]
  · simp

/-- The finite-product quotient expected from the q-binomial theorem. -/
def qBinomialProduct (A B : ℕ) : PowerSeries R :=
  qFactorial PowerSeries.X (A - 1) * reciprocalQFactorial (A + B - 1)

/-- The quotient satisfies the same first-order recurrence. -/
theorem qBinomialProduct_recurrence (A B : ℕ) (hA : 0 < A) :
    (1 - PowerSeries.X ^ A) * (qBinomialProduct A B : PowerSeries R) =
      (1 - PowerSeries.X ^ (A + B)) * qBinomialProduct (A + 1) B := by
  have hpred : A - 1 + 1 = A := by omega
  have hpredB : A + B - 1 + 1 = A + B := by omega
  have hnext : A + 1 + B - 1 = A + B := by omega
  simp only [qBinomialProduct]
  rw [show A + 1 - 1 = A by omega, hnext]
  calc
    _ = qFactorial PowerSeries.X A * (reciprocalQFactorial (A + B - 1) : PowerSeries R) := by
      have hfac : (qFactorial PowerSeries.X A : PowerSeries R) =
          qFactorial PowerSeries.X (A - 1) * (1 - PowerSeries.X ^ A) := by
        simpa only [hpred] using qFactorial_succ (PowerSeries.X : PowerSeries R) (A - 1)
      rw [hfac]
      ring
    _ = _ := by
      have h := one_sub_X_pow_mul_reciprocalQFactorial (R := R) (A + B - 1)
      rw [hpredB] at h
      rw [mul_comm (1 - PowerSeries.X ^ (A + B)), mul_assoc]
      rw [mul_comm (reciprocalQFactorial (A + B)), h]

/-- The finite-product quotient also approaches `1` coefficientwise. -/
theorem coeff_qBinomialProduct_of_lt (A B d : ℕ) (hB : 0 < B) (hd : d < A) :
    PowerSeries.coeff d (qBinomialProduct A B : PowerSeries R) = PowerSeries.coeff d 1 := by
  unfold qBinomialProduct
  calc
    _ = PowerSeries.coeff d ((euler : PowerSeries R) * reciprocalQFactorial (A + B - 1)) := by
      apply coeff_mul_congr_left_upto
      intro i hi
      exact (coeff_euler i (A - 1) (by omega)).symm
    _ = PowerSeries.coeff d ((euler : PowerSeries R) * reciprocalEuler) := by
      rw [mul_comm, mul_comm (euler : PowerSeries R)]
      apply coeff_mul_congr_left_upto
      intro i hi
      exact (coeff_reciprocalEuler i (A + B - 1) (by omega)).symm
    _ = _ := by rw [euler_mul_reciprocal]

/-- Recurrence plus stable tail truncations determines the positive-parameter sequence. -/
theorem positive_sequence_unique (B : ℕ) (F G : ℕ → PowerSeries R)
    (hF : ∀ A, 0 < A → (1 - PowerSeries.X ^ A) * F A =
      (1 - PowerSeries.X ^ (A + B)) * F (A + 1))
    (hG : ∀ A, 0 < A → (1 - PowerSeries.X ^ A) * G A =
      (1 - PowerSeries.X ^ (A + B)) * G (A + 1))
    (htail : ∀ A d, d < A → PowerSeries.coeff d (F A) = PowerSeries.coeff d (G A))
    (A : ℕ) (hA : 0 < A) : F A = G A := by
  apply PowerSeries.ext
  intro d
  have step : ∀ n A, d + 1 ≤ A + n → 0 < A →
      ∀ j, j ≤ d → PowerSeries.coeff j (F A) = PowerSeries.coeff j (G A) := by
    intro n
    induction n with
    | zero =>
        intro A hbound hpos j hj
        exact htail A j (by omega)
    | succ n ih =>
        intro A hbound hpos j hj
        let U : PowerSeries R := PowerSeries.invOfUnit (1 - PowerSeries.X ^ A) 1
        have hunit : (1 - PowerSeries.X ^ A) * U = 1 := by
          apply PowerSeries.mul_invOfUnit
          simp [hpos.ne']
        have hsolF : F A = (U * (1 - PowerSeries.X ^ (A + B))) * F (A + 1) := by
          calc
            _ = U * ((1 - PowerSeries.X ^ A) * F A) := by
              rw [← mul_assoc, mul_comm U, hunit, one_mul]
            _ = _ := by rw [hF A hpos]; ring
        have hsolG : G A = (U * (1 - PowerSeries.X ^ (A + B))) * G (A + 1) := by
          calc
            _ = U * ((1 - PowerSeries.X ^ A) * G A) := by
              rw [← mul_assoc, mul_comm U, hunit, one_mul]
            _ = _ := by rw [hG A hpos]; ring
        rw [hsolF, hsolG, mul_comm _ (F (A + 1)), mul_comm _ (G (A + 1))]
        apply coeff_mul_congr_left_upto
        intro i hi
        exact ih (A + 1) (by omega) (by omega) i (hi.trans hj)
  exact step (d + 1) A (by omega) hA d le_rfl

/-- The infinite q-binomial theorem at the two positive powers used in Section 5.4. -/
theorem qBinomialSum_eq (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (qBinomialSum A B : PowerSeries R) =
      qFactorial PowerSeries.X (A - 1) * reciprocalQFactorial (A + B - 1) := by
  exact positive_sequence_unique B (fun A => qBinomialSum A B) (fun A => qBinomialProduct A B)
    (fun A h => qBinomialSum_recurrence A B h)
    (fun A h => qBinomialProduct_recurrence A B h)
    (fun A d hd => by
      rw [coeff_qBinomialSum_of_lt A B d hd, coeff_qBinomialProduct_of_lt A B d hB hd]) A hA

end
end VOA.QSeries
