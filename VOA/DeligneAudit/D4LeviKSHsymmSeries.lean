import VOA.DeligneAudit.D4LeviKSBlockBox
import VOA.DeligneAudit.D4LeviKSMixedCoeffAlloc

/-! Complete homogeneous generating series and removal of a complementary alphabet. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.LeviConversion

variable {A : Type*} [CommRing A]

noncomputable def ksGeometricSeries (a : A) : PowerSeries A :=
  PowerSeries.mk fun r => a ^ r

noncomputable def ksHSeries (vs : List A) : PowerSeries A :=
  (vs.map ksGeometricSeries).prod

/-- The signed elementary polynomial of an alphabet. -/
noncomputable def ksEPoly (vs : List A) : Polynomial A :=
  (vs.map fun a => 1 - Polynomial.C a * Polynomial.X).prod

theorem ksGeometricSeries_mul_linear (a : A) :
    ksGeometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  apply PowerSeries.ext
  intro n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp [ksGeometricSeries]
  | succ n =>
      rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
      simp [ksGeometricSeries, pow_succ]

theorem ksHSeries_append (vs ws : List A) :
    ksHSeries (vs ++ ws) = ksHSeries vs * ksHSeries ws := by
  simp [ksHSeries]

theorem ksHSeries_mul_EPoly (vs : List A) :
    ksHSeries vs * (ksEPoly vs : PowerSeries A) = 1 := by
  induction vs with
  | nil => simp [ksHSeries, ksEPoly]
  | cons a vs ih =>
      simp only [ksHSeries, ksEPoly, List.map_cons, List.prod_cons] at *
      rw [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, mul_mul_mul_comm]
      rw [ksGeometricSeries_mul_linear, ih, one_mul]

/-- Removing an alphabet multiplies its complete series by the signed
    elementary polynomial of the removed letters. -/
theorem ksHSeries_remove (vs ws : List A) :
    ksHSeries vs = ksHSeries (vs ++ ws) * (ksEPoly ws : PowerSeries A) := by
  rw [ksHSeries_append, mul_assoc, ksHSeries_mul_EPoly, mul_one]

theorem ksEPoly_natDegree_le (vs : List A) : (ksEPoly vs).natDegree ≤ vs.length := by
  induction vs with
  | nil => simp [ksEPoly]
  | cons a vs ih =>
      have hlin : (1 - Polynomial.C a * Polynomial.X : Polynomial A).natDegree ≤ 1 := by
        apply (Polynomial.natDegree_sub_le _ _).trans
        exact max_le (by simp)
          ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
      exact (Polynomial.natDegree_mul_le).trans (by
        change (1 - Polynomial.C a * Polynomial.X : Polynomial A).natDegree +
          (ksEPoly vs).natDegree ≤ vs.length + 1
        omega)

theorem ksEPoly_coeff_eq_zero (vs : List A) (j : ℕ) (hj : vs.length < j) :
    (ksEPoly vs).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((ksEPoly_natDegree_le vs).trans_lt hj)

theorem ksHSeries_coeff_vectors (n s : ℕ) (v : Fin n → A) :
    PowerSeries.coeff s (ksHSeries (List.ofFn v)) =
      ∑ e : {e : Fin n → ℕ // ∑ i, e i = s}, ∏ i, v i ^ e.1 i := by
  classical
  have hseries : ksHSeries (List.ofFn v) =
      ((List.ofFn fun i : Fin n => (fun r : ℕ => v i ^ r)).map fCurrent).prod := by
    simp [ksHSeries, List.map_ofFn, Function.comp_def, ksGeometricSeries, fCurrent]
  rw [hseries, mixed_current_coeff_allocations]
  simp only [List.length_ofFn]
  rw [rz_zero_alloc_sum_eq_vector_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [List.ofFn_eq_map, List.zip_map', List.map_map, Function.comp_def]
  rw [← List.ofFn_eq_map, List.prod_ofFn]

theorem ksHSeries_coeff_aeval [Algebra ℂ A] (n s : ℕ) (v : Fin n → A) :
    PowerSeries.coeff s (ksHSeries (List.ofFn v)) =
      aeval v (hsymm (Fin n) ℂ s) := by
  rw [ksHSeries_coeff_vectors, rz_hsymm_eq_sum_vectors]
  simp only [map_sum, map_prod, map_pow, aeval_X]

theorem ksHSeries_coeff_hsymm (n s : ℕ) :
    PowerSeries.coeff s
        (ksHSeries (List.ofFn fun i : Fin n => (X i : MvPolynomial (Fin n) ℂ))) =
      hsymm (Fin n) ℂ s := by
  rw [ksHSeries_coeff_vectors, rz_hsymm_eq_sum_vectors]

/-- The convolution needed for relative box reduction. Its elementary factor
    has no coefficients above the size of the complementary alphabet. -/
theorem ksHSeries_remove_coeff (vs ws : List A) (s : ℕ) :
    PowerSeries.coeff s (ksHSeries vs) =
      ∑ p ∈ Finset.antidiagonal s,
        PowerSeries.coeff p.1 (ksHSeries (vs ++ ws)) * (ksEPoly ws).coeff p.2 := by
  rw [ksHSeries_remove vs ws, PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksGeometricSeries_mul_linear
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_append
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_mul_EPoly
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_remove
#print axioms VOA.DeligneAudit.D4Levi.ksEPoly_natDegree_le
#print axioms VOA.DeligneAudit.D4Levi.ksEPoly_coeff_eq_zero
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_vectors
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_aeval
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_hsymm
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_remove_coeff
