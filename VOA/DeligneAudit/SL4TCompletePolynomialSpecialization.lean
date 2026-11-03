import VOA.DeligneAudit.SL4TGrassmannian
import VOA.DeligneAudit.D4LeviKSHsymmSeries

/-! Specialization of the abstract complete polynomials to a finite alphabet. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- Substitute the elementary symmetric functions of a finite alphabet. -/
def elementarySpecialization (n : ℕ) : SymPoly →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval fun i => esymm (Fin n) ℂ (i + 1)

theorem elementarySpecialization_elementary (n j : ℕ) :
    elementarySpecialization n (elementary j) = esymm (Fin n) ℂ j := by
  cases j <;> simp [elementarySpecialization, elementary]

/-- The elementary product has the signed elementary functions as its coefficients. -/
theorem elementaryProduct_coeff (n j : ℕ) :
    (D4Levi.ksEPoly (List.ofFn fun i : Fin n => (X i : MvPolynomial (Fin n) ℂ))).coeff j =
      (-1) ^ j * esymm (Fin n) ℂ j := by
  classical
  have he (S : Finset (Fin n)) :
      (∏ i ∈ S, (-Polynomial.C (X i : MvPolynomial (Fin n) ℂ) * Polynomial.X) :
        Polynomial (MvPolynomial (Fin n) ℂ)) =
      Polynomial.C ((-1) ^ S.card * ∏ i ∈ S, X i) * Polynomial.X ^ S.card := by
    simp only [Finset.prod_mul_distrib, Finset.prod_neg, ← map_prod,
      Finset.prod_const, map_mul, map_pow, map_neg, map_one]
  simp only [D4Levi.ksEPoly, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  simp_rw [sub_eq_add_neg, ← neg_mul, Finset.prod_one_add, he,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [esymm, Finset.mul_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext S
    simp [Finset.mem_powersetCard, eq_comm]
  · intro S hS
    have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    rw [hcard]

/-- Complete homogeneous functions are inverse to the signed elementary product. -/
theorem finiteAlphabet_complete_relation (n k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range (k + 1),
      (-1) ^ i * esymm (Fin n) ℂ i * hsymm (Fin n) ℂ (k - i) = 0 := by
  have hprod := D4Levi.ksHSeries_mul_EPoly
    (List.ofFn fun i : Fin n => (X i : MvPolynomial (Fin n) ℂ))
  rw [mul_comm] at hprod
  have hc := congrArg (PowerSeries.coeff k) hprod
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simpa only [Polynomial.coeff_coe, elementaryProduct_coeff,
    D4Levi.ksHSeries_coeff_hsymm, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hk)] using hc

/-- The abstract inverse-series recursion gives the usual complete homogeneous polynomial. -/
theorem elementarySpecialization_complete (n j : ℕ) :
    elementarySpecialization n (complete j) = hsymm (Fin n) ℂ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp
    | succ k =>
      have hr := finiteAlphabet_complete_relation n (k + 1) (by omega)
      rw [Finset.sum_range_succ'] at hr
      simp only [Nat.add_sub_add_right, pow_zero, esymm_zero, one_mul, Nat.sub_zero] at hr
      rw [complete_succ, map_neg, map_sum]
      simp only [map_mul, map_pow, map_neg, map_one, elementarySpecialization_elementary]
      have he : (∑ i ∈ Finset.range (k + 1), (-1) ^ (i + 1) *
          esymm (Fin n) ℂ (i + 1) * elementarySpecialization n (complete (k - i))) =
          ∑ i ∈ Finset.range (k + 1), (-1) ^ (i + 1) *
            esymm (Fin n) ℂ (i + 1) * hsymm (Fin n) ℂ (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih _ (by omega)]
      rw [he]
      exact (eq_neg_of_add_eq_zero_right hr).symm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.elementarySpecialization_elementary
#print axioms VOA.DeligneAudit.SL4T.elementaryProduct_coeff
#print axioms VOA.DeligneAudit.SL4T.finiteAlphabet_complete_relation
#print axioms VOA.DeligneAudit.SL4T.elementarySpecialization_complete
