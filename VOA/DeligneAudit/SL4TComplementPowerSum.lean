import VOA.DeligneAudit.SL4TNewtonSeries

/-! Power sums at the last mode of a complementary characteristic factorization. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The inverse of a normalized coefficient polynomial computes its logarithmic derivative. -/
theorem powerSumSeries_eq_derivative_complement (f g : R[X]) (d : ℕ)
    (hf : f.coeff 0 = 1) (hfg : f * g = 1) :
    positivePowerSumSeries (powerSumOfCoeff d f.coeff) =
      -((f.derivative * g : R[X]) : PowerSeries R) := by
  have hs : newtonCoefficientSeries (powerSumOfCoeff d f.coeff) =
      (f : PowerSeries R) := by
    ext n : 1
    simpa only [newtonCoefficientSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
      using newtonCoeff_powerSumOfCoeff d f.coeff hf n
  have hd := newtonCoefficientSeries_derivative (powerSumOfCoeff d f.coeff)
  rw [hs, PowerSeries.derivative_coe] at hd
  have he := congrArg (fun u : PowerSeries R => u * (g : PowerSeries R)) hd
  dsimp only at he
  rw [neg_mul, mul_assoc, ← Polynomial.coe_mul, ← Polynomial.coe_mul,
    hfg, Polynomial.coe_one, mul_one] at he
  rw [he, neg_neg]

/-- Every positive power sum is a coefficient of the polynomial logarithmic derivative. -/
theorem powerSumOfCoeff_eq_derivative_complement (f g : R[X]) (d n : ℕ)
    (hf : f.coeff 0 = 1) (hfg : f * g = 1) :
    powerSumOfCoeff d f.coeff (n + 1) = -(f.derivative * g).coeff n := by
  have h := congrArg (PowerSeries.coeff n)
    (powerSumSeries_eq_derivative_complement f g d hf hfg)
  simpa only [positivePowerSumSeries, PowerSeries.coeff_mk, map_neg,
    Polynomial.coeff_coe] using h

/-- The reversed derivative has one less coefficient degree than the original polynomial. -/
theorem coefficientEuler_degree (f : R[X]) (d : ℕ) (hd : f.natDegree ≤ d) (hpos : 0 < d) :
    (Polynomial.C (d : R) * f - X * f.derivative).natDegree ≤ d - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hnpos : 0 < n := by omega
  have hx : (X * f.derivative).coeff n = f.derivative.coeff (n - 1) := by
    simpa only [Nat.sub_add_cancel hnpos] using coeff_X_mul f.derivative (n - 1)
  rw [coeff_sub, coeff_C_mul, hx, coeff_derivative,
    Nat.sub_add_cancel (by omega)]
  by_cases he : n = d
  · subst n
    have hc : ((d - 1 : ℕ) : R) + 1 = (d : R) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : R)) (Nat.sub_add_cancel hpos)
    rw [hc]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    ring

/-- The top coefficient of the reversed derivative is the next-to-top original coefficient. -/
theorem coefficientEuler_top (f : R[X]) (d : ℕ) (hpos : 0 < d) :
    (Polynomial.C (d : R) * f - X * f.derivative).coeff (d - 1) = f.coeff (d - 1) := by
  by_cases hd : d = 1
  · subst d
    simp
  · have hx : (X * f.derivative).coeff (d - 1) = f.derivative.coeff (d - 2) := by
      convert coeff_X_mul f.derivative (d - 2) using 1 <;> congr 1 <;> omega
    rw [coeff_sub, coeff_C_mul, hx, coeff_derivative,
      show d - 2 + 1 = d - 1 by omega]
    have hc : (d : R) = ((d - 2 : ℕ) : R) + 2 := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : R)) (show d = d - 2 + 2 by omega)
    rw [hc]
    ring

/-- The last positive power sum is the constant coefficient of the differentiated
characteristic factor times its complement. -/
theorem powerSumOfCoeff_last_mode (f g : R[X]) (d e : ℕ)
    (hf : f.coeff 0 = 1) (hfg : f * g = 1)
    (hd : f.natDegree ≤ d) (he : g.natDegree ≤ e) (hsize : 2 ≤ d + e) :
    powerSumOfCoeff d f.coeff (d + e - 1) =
      (f.reflect d).coeff 1 * (g.reflect e).coeff 0 := by
  by_cases hzero : d = 0
  · subst d
    have hf' : f = 1 := by
      rw [eq_C_of_natDegree_le_zero hd, hf, C_1]
    rw [hf']
    have hp := powerSumOfCoeff_eq_derivative_complement 1 g 0 (e - 2) (by simp)
      (by simpa only [hf'] using hfg)
    have hn : e - 2 + 1 = e - 1 := by omega
    simpa [hn, coeff_one] using hp
  · have hpos : 0 < d := by omega
    let u := Polynomial.C (d : R) * f - X * f.derivative
    have ht : (u * g).coeff (d - 1 + e) = f.coeff (d - 1) * g.coeff e := by
      rw [coeff_mul_add_eq_of_natDegree_le (coefficientEuler_degree f d hd hpos) he,
        coefficientEuler_top f d hpos]
    have hu : u * g = Polynomial.C (d : R) - X * (f.derivative * g) := by
      dsimp only [u]
      rw [sub_mul, mul_assoc, hfg, mul_one, mul_assoc]
    have hn : d - 1 + e = d + e - 1 := by omega
    rw [hn, hu, coeff_sub, coeff_C, if_neg (by omega), zero_sub] at ht
    have hx : (X * (f.derivative * g)).coeff (d + e - 1) =
        (f.derivative * g).coeff (d + e - 2) := by
      convert coeff_X_mul (f.derivative * g) (d + e - 2) using 1 <;> congr 1 <;> omega
    rw [hx] at ht
    have hp := powerSumOfCoeff_eq_derivative_complement f g d (d + e - 2) hf hfg
    have hn' : d + e - 2 + 1 = d + e - 1 := by omega
    rw [hn'] at hp
    rw [hp, coeff_reflect, revAt_le hpos, coeff_reflect, revAt_zero]
    exact ht

/-- The highest allowed coefficient of a product is the product of the allowed top coefficients. -/
theorem coefficient_prod_sum_degrees {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (d : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
        coeff_mul_add_eq_of_natDegree_le (h i (by simp))
          ((natDegree_prod_le _ _).trans (Finset.sum_le_sum
            (fun j hj => h j (Finset.mem_insert_of_mem hj)))),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.powerSumSeries_eq_derivative_complement
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_eq_derivative_complement
#print axioms VOA.DeligneAudit.SL4T.coefficientEuler_degree
#print axioms VOA.DeligneAudit.SL4T.coefficientEuler_top
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_last_mode
#print axioms VOA.DeligneAudit.SL4T.coefficient_prod_sum_degrees
