import VOA.DeligneAudit.DeligneFusionCVRectPBWBoundary

/-!
# The coefficient row identity with two proved finite bounds

A left current supported through S and a right series supported through T
force their degree S+T coefficient through one row of the middle current.
This is a finite convolution identity, independent of any module presentation.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

open VOA.DeligneAudit.A2.CVRectPolynomial
open VOA.DeligneAudit.A2.CVRectPBWBoundary

noncomputable section

variable {A : Type*} [Semiring A]

theorem prefix_product_coefficient_zero (G : ℕ → A) (H : PowerSeries A) (j T : ℕ)
    (hH : ∀ k, T < k → PowerSeries.coeff k H = 0) :
    PowerSeries.coeff (j + T) ((finiteCurrent j G : PowerSeries A) * H) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, k⟩ hik
  have hik' : i + k = j + T := Finset.mem_antidiagonal.mp hik
  rw [Polynomial.coeff_coe]
  by_cases hi : i < j
  · rw [finiteCurrent_coeff_lt j G i hi, hH k (by omega), mul_zero]
  · rw [finiteCurrent_coeff_ge j G i (by omega), zero_mul]

theorem coefficient_shift_of_high_right (G : ℕ → A) (H : PowerSeries A) (j T : ℕ)
    (hH : ∀ k, T < k → PowerSeries.coeff k H = 0) :
    PowerSeries.coeff (j + T) (PowerSeries.mk G * H) =
      PowerSeries.coeff T (PowerSeries.mk (fun k => G (j + k)) * H) := by
  rw [series_prefix_tail G j, add_mul, mul_assoc, map_add,
    prefix_product_coefficient_zero G H j T hH, zero_add,
    PowerSeries.coeff_X_pow_mul']
  simp only [show j ≤ j + T by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-- One exact row computes the target coefficient under its two support bounds. -/
theorem coefficient_leading_row (F G : ℕ → A) (H : PowerSeries A) (S T : ℕ)
    (hF : ∀ i, S < i → F i = 0)
    (hH : ∀ k, T < k → PowerSeries.coeff k H = 0) :
    PowerSeries.coeff (S + T) (PowerSeries.mk F * PowerSeries.mk G * H) =
      ∑ ij ∈ Finset.antidiagonal S,
        F ij.1 * PowerSeries.coeff T (PowerSeries.mk (fun k => G (ij.2 + k)) * H) := by
  rw [mul_assoc, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have htrim : (∑ i ∈ Finset.range (S + T + 1),
      F i * PowerSeries.coeff (S + T - i) (PowerSeries.mk G * H)) =
      ∑ i ∈ Finset.range (S + 1),
        F i * PowerSeries.coeff (S + T - i) (PowerSeries.mk G * H) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : S + 1 ≤ S + T + 1))
    intro i hi hnot
    have hiS : S < i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    rw [hF i hiS, zero_mul]
  rw [htrim, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hiS : i ≤ S := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  rw [show S + T - i = (S - i) + T by omega,
    coefficient_shift_of_high_right G H (S - i) T hH]

end
end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.coefficient_leading_row
