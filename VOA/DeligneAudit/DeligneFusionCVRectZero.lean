import VOA.DeligneAudit.DeligneFusionCVRectShift

/-!
# Zero-capacity site removal at the actual coefficient ideal

After the highest retained modes of a zero-capacity site are set to
zero, each affected reversed current has one factor of the outer
variable. The coefficient-ideal equality below removes those factors
and exactly the corresponding site load from the order function.
Finite polynomial variable elimination is a separate map construction.
-/

namespace VOA.DeligneAudit.A2.CVRectZero

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal

noncomputable section

/-- The two-color family order for two-color and one-color site capacities. -/
def familyOrder (two one : List ℕ) (a b : ℕ) : ℕ :=
  excess two (a + b) + excess one b

theorem familyOrder_active_zero (two one : List ℕ) (a b : ℕ) :
    familyOrder (0 :: two) one a b = familyOrder two one a b + a + b := by
  simp only [familyOrder, excess, List.map_cons, List.sum_cons, Nat.sub_zero]
  omega

theorem familyOrder_inactive_zero (two one : List ℕ) (a b : ℕ) :
    familyOrder two (0 :: one) a b = familyOrder two one a b + b := by
  simp only [familyOrder, excess, List.map_cons, List.sum_cons, Nat.sub_zero]
  omega

section Coefficients

variable {R : Type*} [CommRing R]

theorem factored_current_product (S T : PowerSeries R) (u v a b : ℕ) :
    (PowerSeries.X ^ u * S) ^ a * (PowerSeries.X ^ v * T) ^ b =
      PowerSeries.X ^ (u * a + v * b) * (S ^ a * T ^ b) := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
  ring

/-- Removing known outer-variable factors gives equality of the actual
defining coefficient ideals, with their order functions reduced exactly. -/
theorem coefficientIdeal_factor (S T : PowerSeries R) (μ : ℕ → ℕ → ℕ) (u v : ℕ) :
    coefficientIdeal (PowerSeries.X ^ u * S) (PowerSeries.X ^ v * T)
      (fun a b => μ a b + u * a + v * b) = coefficientIdeal S T μ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨a, b, j, hj, rfl⟩
    change j < μ a b + u * a + v * b at hj
    rw [factored_current_product, PowerSeries.coeff_X_pow_mul']
    split_ifs with hshift
    · exact Ideal.subset_span ⟨a, b, j - (u * a + v * b), by omega, rfl⟩
    · exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro P ⟨a, b, j, hj, rfl⟩
    have hm : PowerSeries.coeff (j + (u * a + v * b))
        ((PowerSeries.X ^ u * S) ^ a * (PowerSeries.X ^ v * T) ^ b) ∈
          coefficientIdeal (PowerSeries.X ^ u * S) (PowerSeries.X ^ v * T)
            (fun a b => μ a b + u * a + v * b) :=
      Ideal.subset_span ⟨a, b, j + (u * a + v * b), by dsimp; omega, rfl⟩
    rw [factored_current_product, PowerSeries.coeff_X_pow_mul] at hm
    exact hm

/-- A zero-capacity two-color site is removed after both reversed
currents acquire their actual outer-variable factors. -/
theorem coefficientIdeal_active_zero (S T : PowerSeries R) (two one : List ℕ) :
    coefficientIdeal (PowerSeries.X * S) (PowerSeries.X * T)
      (familyOrder (0 :: two) one) = coefficientIdeal S T (familyOrder two one) := by
  have hμ : familyOrder (0 :: two) one =
      fun a b => familyOrder two one a b + 1 * a + 1 * b := by
    funext a b
    simpa only [one_mul] using familyOrder_active_zero two one a b
  rw [hμ]
  simpa only [pow_one] using coefficientIdeal_factor S T (familyOrder two one) 1 1

/-- A zero-capacity one-color site changes only that color's reversed current. -/
theorem coefficientIdeal_inactive_zero (S T : PowerSeries R) (two one : List ℕ) :
    coefficientIdeal S (PowerSeries.X * T)
      (familyOrder two (0 :: one)) = coefficientIdeal S T (familyOrder two one) := by
  have hμ : familyOrder two (0 :: one) =
      fun a b => familyOrder two one a b + 0 * a + 1 * b := by
    funext a b
    simpa only [zero_mul, one_mul, Nat.add_zero] using familyOrder_inactive_zero two one a b
  rw [hμ]
  simpa only [pow_zero, one_mul, pow_one] using
    coefficientIdeal_factor S T (familyOrder two one) 0 1

end Coefficients

end

end VOA.DeligneAudit.A2.CVRectZero

#print axioms VOA.DeligneAudit.A2.CVRectZero.coefficientIdeal_factor
#print axioms VOA.DeligneAudit.A2.CVRectZero.coefficientIdeal_active_zero
#print axioms VOA.DeligneAudit.A2.CVRectZero.coefficientIdeal_inactive_zero
