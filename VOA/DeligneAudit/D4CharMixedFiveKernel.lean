import VOA.DeligneAudit.D4CharMixedBiSeries

/-! The stable mixed-Cauchy Euler kernel and its complete four-degree recurrence. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The two negative-only inverse Euler products, in independent y variables. -/
def gtMixedFiveYBase (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) : GTBiSeries R :=
  let A := ∏ i ∈ Finset.range 5, gtEulerInv q h ((u i)⁻¹ : Rˣ)
  PowerSeries.C A * A.map PowerSeries.C

/-- One positive-variable factor of the actual mixed Euler product. -/
def gtMixedFiveStep (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    PowerSeries (GTBiSeries R) :=
  gtMixedEulerStep (R := GTBiSeries R) (gtBiC (R := R) q)
    (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h)
    (fun i => gtBiC (R := R) (u i : R)) gtBiY 5 2

/-- Four-degree coefficient of the mixed Euler product at (2,2,5). -/
def gtMixedFiveKernelCoeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) : R :=
  gtBiCoeff t v (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
    coeff s (gtMixedFiveStep q h u))

theorem gtMixedFiveKernelCoeff_swap_x (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    gtMixedFiveKernelCoeff q h u r s t v = gtMixedFiveKernelCoeff q h u s r t v := by
  unfold gtMixedFiveKernelCoeff
  congr 1
  ring

theorem gtMixedFiveKernelCoeff_zero_x (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (t v : ℕ) :
    gtMixedFiveKernelCoeff q h u 0 0 t v =
      gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 t *
        gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 v := by
  simp only [gtMixedFiveKernelCoeff, gtMixedFiveStep, coeff_zero_eq_constantCoeff,
    constantCoeff_gtMixedEulerStep, mul_one, gtMixedFiveYBase]
  rw [gtBiCoeff_separate, gtEulerInv_product_coeff, gtEulerInv_product_coeff]

/-- The Euler product satisfies exactly the GT four-degree recurrence. -/
theorem gtMixedFiveKernelCoeff_recurrence (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    GTMixedFiveRecurrence q u (gtMixedFiveKernelCoeff q h u) := by
  intro r s t v
  have hh := gtMixedEulerStep_coeff_mul (R := GTBiSeries R) (gtBiC (R := R) q)
    (gtPochhammerUnits_map (S := GTBiSeries R) gtBiC q h)
    (fun i => Units.map (gtBiC (R := R)) (u i)) gtBiY 5 s
    (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u))
  have hp (k : ℕ) : (gtBiC (R := R) q) ^ k = gtBiC (q ^ k) :=
    (map_pow gtBiC q k).symm
  have he (j : ℕ) : (-1 : GTBiSeries R) ^ j *
      pieriElementary (fun i => Units.map (gtBiC (R := R)) (u i)) 5 j =
        gtBiC ((-1 : R) ^ j * pieriElementary u 5 j) := by
    rw [map_mul, map_pow, map_neg, map_one, pieriElementary_map]
  simp only [hp, he] at hh
  change gtBiC (q ^ s) *
      (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
        coeff s (gtMixedFiveStep q h u)) -
      (if 0 < s then gtBiC (q ^ (s - 1)) *
        (gtBiY 0 * (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
          coeff (s - 1) (gtMixedFiveStep q h u))) else 0) -
      (if 0 < s then gtBiC (q ^ (s - 1)) *
        (gtBiY 1 * (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
          coeff (s - 1) (gtMixedFiveStep q h u))) else 0) +
      (if 1 < s then gtBiC (q ^ (s - 2)) *
        (gtBiY 0 * gtBiY 1 * (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
          coeff (s - 2) (gtMixedFiveStep q h u))) else 0) =
      ∑ j ∈ Finset.range (s + 1), gtBiC ((-1 : R) ^ j * pieriElementary u 5 j) *
        (gtMixedFiveYBase q h u * coeff r (gtMixedFiveStep q h u) *
          coeff (s - j) (gtMixedFiveStep q h u)) at hh
  have hk := congrArg (gtBiCoeff (R := R) t v) hh
  have hit (p : Prop) [Decidable p] (F G : GTBiSeries R) :
      gtBiCoeff t v (if p then F else G) =
        if p then gtBiCoeff t v F else gtBiCoeff t v G := by split_ifs <;> rfl
  simp only [map_add, map_sub, map_sum, hit, map_zero, gtBiCoeff_C_mul,
    gtBiCoeff_yZero, gtBiCoeff_yOne, gtBiCoeff_yZeroOne, mul_ite, mul_zero] at hk
  simpa only [gtMixedFiveKernelCoeff, ← ite_and] using hk

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernelCoeff_swap_x
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernelCoeff_zero_x
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernelCoeff_recurrence
