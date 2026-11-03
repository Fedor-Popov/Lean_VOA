import VOA.DeligneAudit.SL4TRadicalGrassmannianPowerSums
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Newton coefficient series and differences of alphabets over complex algebras. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The signed elementary series reconstructed from positive power sums. -/
def newtonCoefficientSeries (p : ℕ → R) : PowerSeries R := PowerSeries.mk (newtonCoeff p)

/-- The logarithmic derivative series of the positive power sums. -/
def positivePowerSumSeries (p : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (fun n => p (n + 1))

/-- The constant power sum has no effect on the reconstructed coefficients. -/
theorem newtonCoeff_congr_positive (p q : ℕ → R)
    (h : ∀ s, 0 < s → p s = q s) (n : ℕ) : newtonCoeff p n = newtonCoeff q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [newtonCoeff]
    | succ n =>
      simp only [newtonCoeff]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [h _ (by omega), ih _ i.isLt]

/-- Newton recursion is the differential equation for the signed elementary series. -/
theorem newtonCoefficientSeries_derivative (p : ℕ → R) :
    PowerSeries.derivative R (newtonCoefficientSeries p) =
      -(positivePowerSumSeries p * newtonCoefficientSeries p) := by
  ext n : 1
  rw [mul_comm (positivePowerSumSeries p), PowerSeries.coeff_derivative,
    map_neg, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [newtonCoefficientSeries, positivePowerSumSeries, PowerSeries.coeff_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  convert newtonCoeff_rec p n using 1
  · simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm]
    congr 2 <;> omega

/-- A normalized solution of the Newton differential equation is unique. -/
theorem newtonCoefficientSeries_unique (p : ℕ → R) (S : PowerSeries R)
    (hzero : PowerSeries.coeff 0 S = 1)
    (hderiv : PowerSeries.derivative R S = -(positivePowerSumSeries p * S)) :
    newtonCoefficientSeries p = S := by
  ext n : 1
  simp only [newtonCoefficientSeries, PowerSeries.coeff_mk]
  apply newtonCoeff_unique p (fun k => PowerSeries.coeff k S) hzero
  intro k
  have he := congrArg (PowerSeries.coeff k) hderiv
  rw [mul_comm (positivePowerSumSeries p), PowerSeries.coeff_derivative,
    map_neg, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  simp only [positivePowerSumSeries, PowerSeries.coeff_mk] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  convert he using 1
  · simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm]
    congr 2 <;> omega

/-- Addition of power sums becomes multiplication of elementary series. -/
theorem newtonCoefficientSeries_add (p q : ℕ → R) :
    newtonCoefficientSeries (fun s => p s + q s) =
      newtonCoefficientSeries p * newtonCoefficientSeries q := by
  apply newtonCoefficientSeries_unique
  · simp [newtonCoefficientSeries, PowerSeries.coeff_mul, newtonCoeff]
  · rw [Derivation.leibniz, newtonCoefficientSeries_derivative, newtonCoefficientSeries_derivative]
    have he : positivePowerSumSeries (fun s => p s + q s) =
        positivePowerSumSeries p + positivePowerSumSeries q := by
      ext n : 1
      simp [positivePowerSumSeries]
    rw [he]
    simp only [smul_eq_mul]
    ring

/-- The zero power-sum sequence has the constant elementary series. -/
theorem newtonCoefficientSeries_zero : newtonCoefficientSeries (fun _ => (0 : R)) = 1 := by
  apply newtonCoefficientSeries_unique
  · simp
  · have he : positivePowerSumSeries (fun _ => (0 : R)) = 0 := by
      ext n : 1
      simp [positivePowerSumSeries]
    simp [he]

/-- Subtraction of alphabets becomes division of their elementary series. -/
theorem newtonCoefficientSeries_sub_mul (p q : ℕ → R) :
    newtonCoefficientSeries (fun s => p s - q s) * newtonCoefficientSeries q =
      newtonCoefficientSeries p := by
  rw [← newtonCoefficientSeries_add]
  simp only [sub_add_cancel]

/-- Any inverse of an elementary series reconstructs the negative power sums. -/
theorem newtonCoefficientSeries_neg_of_inverse (p : ℕ → R) (S : PowerSeries R)
    (h : newtonCoefficientSeries p * S = 1) : newtonCoefficientSeries (fun s => -p s) = S := by
  have he : newtonCoefficientSeries (fun s => -p s) * newtonCoefficientSeries p = 1 := by
    rw [← newtonCoefficientSeries_add]
    simpa only [neg_add_cancel] using (newtonCoefficientSeries_zero (R := R))
  calc
    newtonCoefficientSeries (fun s => -p s) = newtonCoefficientSeries (fun s => -p s) *
        (newtonCoefficientSeries p * S) := by rw [h, mul_one]
    _ = S := by rw [← mul_assoc, he, one_mul]

/-- Elementary and complete series remain inverse after any algebra specialization. -/
theorem specializedElementary_complete_inverse (f : SymPoly →ₐ[ℂ] R) :
    PowerSeries.mk (fun n => (-1) ^ n * f (elementary n)) *
      PowerSeries.mk (fun n => f (complete n)) = 1 := by
  ext n : 1
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simp
  · have he := congrArg f (complete_relation n (by omega))
    simpa only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero,
      PowerSeries.coeff_one, if_neg hn] using he

/-- Inverse Newton reconstruction recovers a specialized elementary series. -/
theorem newtonCoefficientSeries_elementary (f : SymPoly →ₐ[ℂ] R) (d : ℕ) :
    newtonCoefficientSeries
        (powerSumOfCoeff d (fun n => (-1) ^ n * f (elementary n))) =
      PowerSeries.mk (fun n => (-1) ^ n * f (elementary n)) := by
  ext n : 1
  simp only [newtonCoefficientSeries, PowerSeries.coeff_mk]
  exact newtonCoeff_powerSumOfCoeff d _ (by simp) n

/-- The coefficients of a difference alphabet are elementary-complete convolutions. -/
theorem newtonCoeff_difference_alphabets (f g : SymPoly →ₐ[ℂ] R) (d e n : ℕ) :
    newtonCoeff (fun s =>
        powerSumOfCoeff d (fun k => (-1) ^ k * f (elementary k)) s -
        powerSumOfCoeff e (fun k => (-1) ^ k * g (elementary k)) s) n =
      ∑ i ∈ Finset.range (n + 1), (-1) ^ i * f (elementary i) * g (complete (n - i)) := by
  have he : newtonCoefficientSeries (fun s =>
        powerSumOfCoeff d (fun k => (-1) ^ k * f (elementary k)) s -
        powerSumOfCoeff e (fun k => (-1) ^ k * g (elementary k)) s) =
      PowerSeries.mk (fun k => (-1) ^ k * f (elementary k)) *
        PowerSeries.mk (fun k => g (complete k)) := by
    simp only [sub_eq_add_neg]
    rw [newtonCoefficientSeries_add, newtonCoefficientSeries_elementary]
    congr 1
    apply newtonCoefficientSeries_neg_of_inverse
    rw [newtonCoefficientSeries_elementary]
    exact specializedElementary_complete_inverse g
  have hc := congrArg (PowerSeries.coeff n) he
  simpa only [newtonCoefficientSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using hc

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_congr_positive
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_derivative
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_unique
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_add
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_zero
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_sub_mul
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_neg_of_inverse
#print axioms VOA.DeligneAudit.SL4T.specializedElementary_complete_inverse
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_elementary
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_difference_alphabets
