import VOA.DeligneAudit.DeligneFusionCVRectStarIdeal

/-! # Exact outer-variable factoring of the star coefficient ideal -/

namespace VOA.DeligneAudit.A2.CVRectStarFactor

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectStarIdeal

theorem starOrder_zero_left (left right center : List ℕ) (p q r : ℕ) :
    starOrder (0 :: left) right center p q r = starOrder left right center p q r + p + q := by
  simp only [starOrder, excess, List.map_cons, List.sum_cons, Nat.sub_zero]
  omega

variable {R : Type*} [CommRing R]

theorem factored_current_product (X Y Z : PowerSeries R) (u v w p q r : ℕ) :
    (PowerSeries.X ^ u * X) ^ p * (PowerSeries.X ^ v * Y) ^ q *
        (PowerSeries.X ^ w * Z) ^ r =
      PowerSeries.X ^ (u * p + v * q + w * r) * (X ^ p * Y ^ q * Z ^ r) := by
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_add]
  ring

theorem coefficientIdeal3_factor (X Y Z : PowerSeries R)
    (μ : ℕ → ℕ → ℕ → ℕ) (u v w : ℕ) :
    coefficientIdeal3 (PowerSeries.X ^ u * X) (PowerSeries.X ^ v * Y) (PowerSeries.X ^ w * Z)
      (fun p q r => μ p q r + u * p + v * q + w * r) = coefficientIdeal3 X Y Z μ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨p, q, r, j, hj, rfl⟩
    change j < μ p q r + u * p + v * q + w * r at hj
    rw [factored_current_product, PowerSeries.coeff_X_pow_mul']
    split_ifs with hshift
    · exact Ideal.subset_span ⟨p, q, r, j - (u * p + v * q + w * r), by omega, rfl⟩
    · exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro P ⟨p, q, r, j, hj, rfl⟩
    have hm : PowerSeries.coeff (j + (u * p + v * q + w * r))
        ((PowerSeries.X ^ u * X) ^ p * (PowerSeries.X ^ v * Y) ^ q *
          (PowerSeries.X ^ w * Z) ^ r) ∈
        coefficientIdeal3 (PowerSeries.X ^ u * X) (PowerSeries.X ^ v * Y)
          (PowerSeries.X ^ w * Z) (fun p q r => μ p q r + u * p + v * q + w * r) :=
      Ideal.subset_span ⟨p, q, r, j + (u * p + v * q + w * r), by dsimp; omega, rfl⟩
    rw [factored_current_product, PowerSeries.coeff_X_pow_mul] at hm
    exact hm

/-- A zero xy-site affects exactly the x and y reversed currents. -/
theorem coefficientIdeal3_zero_left (X Y Z : PowerSeries R) (left right center : List ℕ) :
    coefficientIdeal3 (PowerSeries.X * X) (PowerSeries.X * Y) Z
      (starOrder (0 :: left) right center) =
      coefficientIdeal3 X Y Z (starOrder left right center) := by
  have hμ : starOrder (0 :: left) right center =
      fun p q r => starOrder left right center p q r + 1 * p + 1 * q + 0 * r := by
    funext p q r
    simpa only [one_mul, zero_mul, Nat.add_zero] using starOrder_zero_left left right center p q r
  rw [hμ]
  simpa only [pow_one, pow_zero, one_mul] using
    coefficientIdeal3_factor X Y Z (starOrder left right center) 1 1 0

end VOA.DeligneAudit.A2.CVRectStarFactor

#print axioms VOA.DeligneAudit.A2.CVRectStarFactor.coefficientIdeal3_factor
#print axioms VOA.DeligneAudit.A2.CVRectStarFactor.coefficientIdeal3_zero_left
