import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeRecurrenceBase
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrentModes

/-! Exact original negative-current recurrence on whole highest-color powers.
No closure of a lower ideal and no C-source reduction is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def singleBitColor : Fin 3 → Fin 8 := ![1,2,4]

theorem cubeNext_highest (d : Fin 3) : cubeNext d 0 = some (singleBitColor d) := by
  fin_cases d <;> rfl

/-- Every original current mode sends the highest whole series to the exact tail. -/
theorem actual_lower_highest_current_tail (m : ℕ) (d : Fin 3) (ell : ℕ) :
    seriesDerivation (g0Deriv m (cubeDirection d) ell) (actualCurrent m 0) =
      tailSeries ell (actualCurrent m (singleBitColor d)) := by
  apply PowerSeries.ext
  intro t
  rw [seriesDerivation_coeff,actualCurrent_coeff,actualMode_lower_mode,cubeNext_highest,
    tailSeries_coeff,actualCurrent_coeff]
  rw [Nat.add_comm ell t]

/-- The normalized highest color is exactly the original highest source current. -/
theorem modeRecurrence_highest_current (m : ℕ) : actualCurrent m 0 = AllM.current m 0 := by
  change ((1 : ℤ) : ℂ) • AllM.current m 0 = AllM.current m 0
  rw [Int.cast_one,one_smul]

/-- Whole actual highest-color mode recurrence, with all finite-boundary terms. -/
theorem actual_lower_highest_coeff_recurrence (m r s ell : ℕ) (d : Fin 3) :
    g0Deriv m (cubeDirection d) ell
        (PowerSeries.coeff s (AllM.current m 0 ^ (r + 1))) =
      g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff (s + ell) (AllM.current m 0 ^ (r + 1))) -
      (r + 1) • ∑ a ∈ Finset.range ell, actualMode m a (singleBitColor d) *
        PowerSeries.coeff (s + ell - a) (AllM.current m 0 ^ r) := by
  have h0 : seriesDerivation (g0Deriv m (cubeDirection d) 0) (actualCurrent m 0) =
      actualCurrent m (singleBitColor d) := by
    simpa only [tailSeries_zero] using actual_lower_highest_current_tail m d 0
  have h := coefficient_power_mode_recurrence
    (g0Deriv m (cubeDirection d) ell) (g0Deriv m (cubeDirection d) 0)
    (actualCurrent m 0) (actualCurrent m (singleBitColor d)) r s ell
    (actual_lower_highest_current_tail m d ell) h0
  simpa only [modeRecurrence_highest_current,actualCurrent_coeff] using h

end
#print axioms actual_lower_highest_current_tail
#print axioms actual_lower_highest_coeff_recurrence
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
