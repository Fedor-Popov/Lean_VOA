import VOA.DeligneAudit.D4CharCauchyRecurrence

/-!
The two-variable Cauchy shift and C(2,N), for every N at least two.
There is no bound on either series degree or on the highest weights in the GT sum.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- Expand the finite Euler denominator in elementary degrees. -/
theorem gtCauchyDenominator_expansion (u : ℕ → Rˣ) (N : ℕ) :
    (∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i : R) * X)) =
      ∑ S : Finset (Fin N),
        PowerSeries.C ((-1 : R) ^ S.card * ∏ i ∈ S, (u i : R)) * X ^ S.card := by
  classical
  rw [← Fin.prod_univ_eq_prod_range]
  have he (i : Fin N) :
      (1 - PowerSeries.C (u i : R) * X) = 1 + (-PowerSeries.C (u i : R) * X) := by
    ring
  simp only [he]
  rw [Finset.prod_one_add]
  have hu : (Finset.univ : Finset (Fin N)).powerset = Finset.univ := by ext; simp
  rw [hu]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_neg]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod]

theorem gtCauchyDenominator_coeff (u : ℕ → Rˣ) (N j : ℕ) :
    coeff j (∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i : R) * X)) =
      (-1 : R) ^ j * pieriElementary u N j := by
  classical
  rw [gtCauchyDenominator_expansion, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [pieriElementary, Finset.mul_sum, Finset.powersetCard_eq_filter,
    Finset.sum_filter]
  have hu : (Finset.univ : Finset (Fin N)).powerset = Finset.univ := by ext; simp
  rw [hu]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hj : S.card = j
  · simp [hj]
  · simp [hj, Ne.symm hj]

/-- The two-variable Cauchy shift, discharged by X, B and e-Pieri in all degrees. -/
theorem gtCauchyTwo_shift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    GTCauchyTwoShift q h u N := by
  intro r
  ext s
  rw [coeff_rescale]
  rw [mul_comm (gtCauchyTwoSeries q h u N r), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [gtCauchyTwoSeries, coeff_mk, gtCauchyDenominator_coeff]
  exact gtCauchyTwoCoeff_recurrence q h u N r s

/-- Ordinary Cauchy C(2,N+2), unconditionally over every admissible coefficient ring. -/
theorem gtCauchy_two (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    GTCauchyTwo q h u N :=
  gtCauchy_two_of_shift q h u N (gtCauchyTwo_shift q h u N)

/-- The three C(2,N) instances used by gP and the D4 mixed-Cauchy argument. -/
theorem gtCauchy_two_needed (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    GTCauchyTwo q h u 0 ∧ GTCauchyTwo q h u 1 ∧ GTCauchyTwo q h u 3 :=
  ⟨gtCauchy_two q h u 0, gtCauchy_two q h u 1, gtCauchy_two q h u 3⟩

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchyDenominator_expansion
#print axioms VOA.DeligneAudit.D4Char.gtCauchyDenominator_coeff
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwo_shift
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two_needed
