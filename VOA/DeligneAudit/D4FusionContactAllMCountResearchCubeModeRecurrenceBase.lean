import VOA.DeligneAudit.D4FusionContactAllMCountResearchSeries

/-! Whole-series tail convolution and coefficient-power mode recurrences.
The boundary terms are retained before any ideal or quotient is considered. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

section Tail
variable {A : Type*} [CommRing A]

def tailSeries (ell : ℕ) (B : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun t => PowerSeries.coeff (t + ell) B)

@[simp] theorem tailSeries_coeff (ell t : ℕ) (B : PowerSeries A) :
    PowerSeries.coeff t (tailSeries ell B) = PowerSeries.coeff (t + ell) B :=
  PowerSeries.coeff_mk _ _

@[simp] theorem tailSeries_zero (B : PowerSeries A) : tailSeries 0 B = B := by
  apply PowerSeries.ext
  intro t
  simp only [tailSeries_coeff,Nat.add_zero]

/-- Split the complete coefficient convolution at the tail boundary ell. -/
theorem coeff_tailSeries_mul_split (B Q : PowerSeries A) (s ell : ℕ) :
    PowerSeries.coeff (s + ell) (B * Q) =
      (∑ a ∈ Finset.range ell, PowerSeries.coeff a B *
        PowerSeries.coeff (s + ell - a) Q) +
      PowerSeries.coeff s (tailSeries ell B * Q) := by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsize : (s + ell).succ = ell + (s + 1) := by omega
  rw [hsize,Finset.sum_range_add]
  congr 1
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro a _
  rw [tailSeries_coeff]
  have hindex : s + ell - (ell + a) = s - a := by omega
  have hcomm : ell + a = a + ell := by omega
  rw [hindex,hcomm]

/-- The tail coefficient is the static coefficient minus the ENTIRE prefix. -/
theorem coeff_tailSeries_mul (B Q : PowerSeries A) (s ell : ℕ) :
    PowerSeries.coeff s (tailSeries ell B * Q) =
      PowerSeries.coeff (s + ell) (B * Q) -
        ∑ a ∈ Finset.range ell, PowerSeries.coeff a B *
          PowerSeries.coeff (s + ell - a) Q := by
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact (coeff_tailSeries_mul_split B Q s ell).symm
end Tail

section Derivations
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Coefficientwise derivations obey the ordinary positive-power rule. -/
theorem derivation_power_coeff (D : Derivation K A A) (U B : PowerSeries A)
    (r s : ℕ) (hD : seriesDerivation D U = B) :
    D (PowerSeries.coeff s (U ^ (r + 1))) =
      (r + 1) • PowerSeries.coeff s (B * U ^ r) := by
  rw [← seriesDerivation_coeff,(seriesDerivation D).leibniz_pow,hD]
  simp only [Nat.add_sub_cancel,smul_eq_mul,map_nsmul]
  rw [mul_comm (U ^ r) B]

/-- An exact current-mode recurrence from the two proved whole-series actions.
No ideal-stability or coefficient-separation premise is present. -/
theorem coefficient_power_mode_recurrence
    (Dl D0 : Derivation K A A) (U B : PowerSeries A) (r s ell : ℕ)
    (hl : seriesDerivation Dl U = tailSeries ell B)
    (h0 : seriesDerivation D0 U = B) :
    Dl (PowerSeries.coeff s (U ^ (r + 1))) =
      D0 (PowerSeries.coeff (s + ell) (U ^ (r + 1))) -
        (r + 1) • ∑ a ∈ Finset.range ell, PowerSeries.coeff a B *
          PowerSeries.coeff (s + ell - a) (U ^ r) := by
  rw [derivation_power_coeff Dl U (tailSeries ell B) r s hl,
    derivation_power_coeff D0 U B r (s + ell) h0,coeff_tailSeries_mul]
  exact nsmul_sub _ _ _
end Derivations

end
#print axioms coeff_tailSeries_mul
#print axioms coefficient_power_mode_recurrence
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
