import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeHighest
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeRecurrenceBase

/-! Exact shift recurrences on the plain highest-color polynomial ring.
No identification with a Cartan operator on other colors is used. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

@[simp] theorem topCurrent_coeff (m s : ℕ) :
    PowerSeries.coeff s (topCurrent m) = topModeX m s :=
  PowerSeries.coeff_mk _ _

/-- The plain top shift acts on every truncated generator, including its zero tail. -/
theorem topShift_modeX (m ell s : ℕ) :
    topShift m ell (topModeX m s) = topModeX m (ell + s) := by
  by_cases hs : s < m
  · simp only [topModeX,dif_pos hs,topShift,MvPolynomial.mkDerivation_X]
  · have hsum : ¬ell + s < m := by omega
    simp only [topModeX,dif_neg hs,dif_neg hsum,map_zero]

/-- Shifting the WHOLE highest current gives its exact coefficient tail. -/
theorem topShift_current_tail (m ell : ℕ) :
    seriesDerivation (topShift m ell) (topCurrent m) =
      tailSeries ell (topCurrent m) := by
  apply PowerSeries.ext
  intro s
  rw [seriesDerivation_coeff,tailSeries_coeff,topCurrent_coeff,topCurrent_coeff,
    topShift_modeX,Nat.add_comm ell s]

/-- The plain mode-zero shift is Euler on the whole highest current. -/
theorem topShift_zero_current (m : ℕ) :
    seriesDerivation (topShift m 0) (topCurrent m) = topCurrent m := by
  simpa only [tailSeries_zero] using topShift_current_tail m 0

/-- Euler's scalar on each whole positive-power coefficient is its source power. -/
theorem topShift_zero_power_coeff (m r s : ℕ) :
    topShift m 0 (PowerSeries.coeff s (topCurrent m ^ (r + 1))) =
      (r + 1) • PowerSeries.coeff s (topCurrent m ^ (r + 1)) := by
  rw [derivation_power_coeff (topShift m 0) (topCurrent m) (topCurrent m)
    r s (topShift_zero_current m),← pow_succ']

/-- Exact plain-shift recurrence with every finite-boundary term retained. -/
theorem topShift_highest_coeff_recurrence (m r s ell : ℕ) :
    topShift m ell (PowerSeries.coeff s (topCurrent m ^ (r + 1))) =
      (r + 1) • PowerSeries.coeff (s + ell) (topCurrent m ^ (r + 1)) -
        (r + 1) • ∑ a ∈ Finset.range ell, topModeX m a *
          PowerSeries.coeff (s + ell - a) (topCurrent m ^ r) := by
  rw [coefficient_power_mode_recurrence (topShift m ell) (topShift m 0)
    (topCurrent m) (topCurrent m) r s ell (topShift_current_tail m ell)
    (topShift_zero_current m),topShift_zero_power_coeff]
  simp only [topCurrent_coeff]

/-- The source of power one has precisely the original finite-mode cutoff. -/
theorem topLinear_coeff_high (m t : ℕ) (ht : m ≤ t) :
    PowerSeries.coeff t (topCurrent m ^ 1) = 0 := by
  have hnot : ¬t < m := by omega
  simp only [pow_one,topCurrent_coeff,topModeX,dif_neg hnot]

end
#print axioms topShift_current_tail
#print axioms topShift_zero_power_coeff
#print axioms topShift_highest_coeff_recurrence
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
