import VOA.DeligneAudit.D4CharMixedFiveKernel

/-!
Stable mixed Cauchy at (m,n,N) = (2,2,5), for all four formal-variable degrees.
The kernel is the product of the two negative-only inverse Euler products and
one mixed Euler step for each positive variable. The outermost variable is x_2,
then x_1, y_2 and y_1. No shift or coefficient-comparison hypothesis remains.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The actual four-variable mixed Euler product, in iterated power series. -/
def gtMixedFiveKernel (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    PowerSeries (PowerSeries (GTBiSeries R)) :=
  PowerSeries.C (PowerSeries.C (gtMixedFiveYBase q h u) * gtMixedFiveStep q h u) *
    (gtMixedFiveStep q h u).map PowerSeries.C

theorem gtMixedFiveKernel_coeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    gtBiCoeff t v (coeff r (coeff s (gtMixedFiveKernel q h u))) =
      gtMixedFiveKernelCoeff q h u r s t v := by
  simp only [gtMixedFiveKernel, coeff_C_mul, coeff_map, coeff_mul_C,
    gtMixedFiveKernelCoeff]

/-- Theorem MC_(2,2,5), as equality of the complete four-degree coefficient arrays. -/
theorem gtMixed_five (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    gtMixedFiveCoeff q h u = gtMixedFiveKernelCoeff q h u :=
  gtMixedFiveCoeff_eq q h u (gtMixedFiveKernelCoeff q h u)
    (gtMixedFiveKernelCoeff_recurrence q h u) (gtMixedFiveKernelCoeff_swap_x q h u)
    (gtMixedFiveKernelCoeff_zero_x q h u)

/-- The finite GT expansion of each coefficient of the actual mixed Euler product. -/
theorem gtMixed_five_coeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    gtBiCoeff t v (coeff r (coeff s (gtMixedFiveKernel q h u))) =
      ∑ b ∈ Finset.range (min r s + 1), ∑ d ∈ Finset.range (min t v + 1),
        gtTwoQCoefficient q h r s b * gtTwoQCoefficient q h t v d *
          gtEval q u 5 (gtMixedFiveRow (r + s - b : ℕ) b (t + v - d : ℕ) d) := by
  rw [gtMixedFiveKernel_coeff, ← gtMixed_five]
  rfl

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernel_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five_coeff
