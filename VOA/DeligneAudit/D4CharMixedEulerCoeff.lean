import VOA.DeligneAudit.D4CharMixedFiveShift

/-! Coefficient extraction for the two-factor mixed Euler equation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtPochhammerUnits_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : R) (h : PochhammerUnits q) : PochhammerUnits (φ q) := by
  intro n
  convert (h n).map φ using 1
  simp [CarrierChain.qpochGen, map_prod]

/-- Multiply a series by two linear Euler factors and extract any degree. -/
theorem gtCoeff_two_linear (F : PowerSeries R) (a b : R) (s : ℕ) :
    coeff s (F * ((1 - PowerSeries.C a * X) * (1 - PowerSeries.C b * X))) =
      coeff s F - (if 0 < s then a * coeff (s - 1) F else 0) -
        (if 0 < s then b * coeff (s - 1) F else 0) +
          (if 1 < s then a * b * coeff (s - 2) F else 0) := by
  have he : F * ((1 - PowerSeries.C a * X) * (1 - PowerSeries.C b * X)) =
      F - PowerSeries.C a * (F * X ^ 1) - PowerSeries.C b * (F * X ^ 1) +
        PowerSeries.C (a * b) * (F * X ^ 2) := by
    rw [map_mul]
    ring
  rw [he]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow']
  have h₁ : 1 ≤ s ↔ 0 < s := by omega
  have h₂ : 2 ≤ s ↔ 1 < s := by omega
  simp only [h₁, h₂, mul_ite, mul_zero]

/-- The kernel recurrence before extraction of the two y degrees. -/
theorem gtMixedEulerStep_coeff_two (q : R) (h : PochhammerUnits q)
    (u : ℕ → Rˣ) (y : ℕ → R) (N s : ℕ) :
    q ^ s * coeff s (gtMixedEulerStep q h (fun i => (u i : R)) y N 2) -
      (if 0 < s then y 0 * (q ^ (s - 1) *
        coeff (s - 1) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)) else 0) -
      (if 0 < s then y 1 * (q ^ (s - 1) *
        coeff (s - 1) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)) else 0) +
      (if 1 < s then y 0 * y 1 * (q ^ (s - 2) *
        coeff (s - 2) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)) else 0) =
      ∑ j ∈ Finset.range (s + 1), (-1 : R) ^ j * pieriElementary u N j *
        coeff (s - j) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2) := by
  have hh := congrArg (coeff s)
    (gtMixedEulerStep_shift q h (fun i => (u i : R)) y N 2)
  have hy : (∏ j ∈ Finset.range 2, (1 - PowerSeries.C (y j) * X)) =
      (1 - PowerSeries.C (y 0) * X) * (1 - PowerSeries.C (y 1) * X) := by
    simp [Finset.prod_range_succ]
  rw [hy, gtCoeff_two_linear] at hh
  simp only [coeff_rescale] at hh
  rw [mul_comm (gtMixedEulerStep q h (fun i => (u i : R)) y N 2), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  simpa only [gtCauchyDenominator_coeff] using hh

/-- The same recurrence after multiplying by any factor independent of the new x degree. -/
theorem gtMixedEulerStep_coeff_mul (q : R) (h : PochhammerUnits q)
    (u : ℕ → Rˣ) (y : ℕ → R) (N s : ℕ) (B : R) :
    q ^ s * (B * coeff s (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)) -
      (if 0 < s then q ^ (s - 1) *
        (y 0 * (B * coeff (s - 1) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)))
        else 0) -
      (if 0 < s then q ^ (s - 1) *
        (y 1 * (B * coeff (s - 1) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)))
        else 0) +
      (if 1 < s then q ^ (s - 2) *
        (y 0 * y 1 * (B * coeff (s - 2)
          (gtMixedEulerStep q h (fun i => (u i : R)) y N 2))) else 0) =
      ∑ j ∈ Finset.range (s + 1), (-1 : R) ^ j * pieriElementary u N j *
        (B * coeff (s - j) (gtMixedEulerStep q h (fun i => (u i : R)) y N 2)) := by
  have hh := congrArg (fun z : R => B * z) (gtMixedEulerStep_coeff_two q h u y N s)
  simp only [mul_add, mul_sub, mul_ite, mul_zero, Finset.mul_sum] at hh
  convert hh using 1
  · split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPochhammerUnits_map
#print axioms VOA.DeligneAudit.D4Char.gtCoeff_two_linear
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_coeff_two
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_coeff_mul
