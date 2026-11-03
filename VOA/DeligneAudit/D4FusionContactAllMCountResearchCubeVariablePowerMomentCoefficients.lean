import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeVariablePowerMomentCoefficientsBase
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticMomentCoefficients
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeVariablePolarIdeal

/-! Actual filtered moments for the variable-power budget (2m+1)-2n.
No generic-n polynomial identity or ideal membership is assumed here. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Exact filtered finite moment of every original normalized current. -/
theorem coeff_X_pow_jet_actualCurrent_mul_eq_filtered_sum (m M j : ℕ) (c : Fin 8)
    (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff M (PowerSeries.X ^ j * (jetDerivative j (actualCurrent m c) * Q)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).filter (fun k => k.val ≤ M),
        k.val.descFactorial j •
          (actualMode m k.val c * PowerSeries.coeff (M - k.val) Q) := by
  simpa only [actualCurrent_coeff] using
    coeff_X_pow_jet_truncated_mul_eq_filtered_sum (actualCurrent m c) Q m M j
      (fun k hk => actualCurrent_coeff_high m k c hk)

/-- No relation between m,n,j is required for the filtered variable-power formula. -/
theorem coeff_variablePower_actualCurrent_filtered (m n j : ℕ) (c : Fin 8)
    (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff (variablePowerBudget m n)
        (PowerSeries.X ^ j * (jetDerivative j (actualCurrent m c) * Q)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).filter
          (fun k => k.val ≤ variablePowerBudget m n),
        k.val.descFactorial j •
          (actualMode m k.val c * PowerSeries.coeff (variablePowerBudget m n - k.val) Q) :=
  coeff_X_pow_jet_actualCurrent_mul_eq_filtered_sum m (variablePowerBudget m n) j c Q

theorem variablePower_mode_bound_of_large_m (m n : ℕ) (hm : 2 * n - 2 ≤ m) :
    m ≤ variablePowerBudget m n + 1 := by
  unfold variablePowerBudget
  omega

/-- The unfiltered specialization explicitly retains its correct mode bound. -/
theorem coeff_variablePower_actualCurrent_unfiltered_of_mode_bound
    (m n j : ℕ) (hm : m ≤ variablePowerBudget m n + 1) (c : Fin 8)
    (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff (variablePowerBudget m n)
        (PowerSeries.X ^ j * (jetDerivative j (actualCurrent m c) * Q)) =
      ∑ k : Fin m, k.val.descFactorial j •
        (actualMode m k.val c * PowerSeries.coeff (variablePowerBudget m n - k.val) Q) := by
  simpa only [actualCurrent_coeff] using
    coeff_X_pow_jet_truncated_mul_eq_sum_of_mode_bound (actualCurrent m c) Q m
      (variablePowerBudget m n) j (fun k hk => actualCurrent_coeff_high m k c hk) hm

theorem coeff_variablePower_actualCurrent_unfiltered_of_large_m
    (m n j : ℕ) (hm : 2 * n - 2 ≤ m) (c : Fin 8)
    (Q : PowerSeries (MvPolynomial (Vars m) ℂ)) :
    PowerSeries.coeff (variablePowerBudget m n)
        (PowerSeries.X ^ j * (jetDerivative j (actualCurrent m c) * Q)) =
      ∑ k : Fin m, k.val.descFactorial j •
        (actualMode m k.val c * PowerSeries.coeff (variablePowerBudget m n - k.val) Q) :=
  coeff_variablePower_actualCurrent_unfiltered_of_mode_bound m n j
    (variablePower_mode_bound_of_large_m m n hm) c Q

/-- The old quartic budget is the n=2 instance, including small Nat cutoffs. -/
theorem variablePowerBudget_two (m : ℕ) :
    variablePowerBudget m 2 = 2 * m - 3 := by
  unfold variablePowerBudget
  omega

end
#print axioms coeff_X_pow_jet_actualCurrent_mul_eq_filtered_sum
#print axioms coeff_variablePower_actualCurrent_filtered
#print axioms coeff_variablePower_actualCurrent_unfiltered_of_mode_bound
#print axioms coeff_variablePower_actualCurrent_unfiltered_of_large_m
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
