import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticFormula
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticSource

/-! Whole twelve-term quartic current formula in the original actual D4
colors, including every normalization sign and every coefficient tail. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def quarticPolarWholeSeries (m : ℕ) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  (48:ℂ) • (AllM.current m 0^2 * AllM.current m 7^2) +
  (48:ℂ) • (AllM.current m 1^2 * AllM.current m 6^2) +
  (48:ℂ) • (AllM.current m 2^2 * AllM.current m 5^2) +
  (48:ℂ) • (AllM.current m 4^2 * AllM.current m 3^2) -
  (192:ℂ) • (AllM.current m 0 * AllM.current m 1 * AllM.current m 6 * AllM.current m 7) -
  (192:ℂ) • (AllM.current m 0 * AllM.current m 2 * AllM.current m 5 * AllM.current m 7) -
  (192:ℂ) • (AllM.current m 0 * AllM.current m 4 * AllM.current m 3 * AllM.current m 7) -
  (192:ℂ) • (AllM.current m 0 * AllM.current m 4 * AllM.current m 5 * AllM.current m 6) +
  (192:ℂ) • (AllM.current m 1 * AllM.current m 2 * AllM.current m 3 * AllM.current m 7) +
  (192:ℂ) • (AllM.current m 1 * AllM.current m 2 * AllM.current m 5 * AllM.current m 6) +
  (192:ℂ) • (AllM.current m 1 * AllM.current m 4 * AllM.current m 3 * AllM.current m 6) +
  (192:ℂ) • (AllM.current m 2 * AllM.current m 4 * AllM.current m 3 * AllM.current m 5)

theorem currentMap_quarticPolarFormula (m : ℕ) :
    currentMap m (quarticPolarFormula ℂ) = quarticPolarWholeSeries m := by
  simp only [quarticPolarFormula,map_add,map_mul,map_pow,map_ofNat,currentMap_X]
  simp [actualCurrent,cubeSign,cubeColor,Algebra.smul_def,quarticPolarWholeSeries,map_ofNat]
  ring

/-- The WHOLE actual six-fold lowering of the original fourth-power coefficient. -/
theorem quarticPolar_whole_coeff (m s : ℕ) :
    g0Deriv m 9 0 (g0Deriv m 9 0 (g0Deriv m 8 0 (g0Deriv m 8 0
      (g0Deriv m 7 0 (g0Deriv m 7 0 (PowerSeries.coeff s (AllM.current m 0^4))))))) =
      PowerSeries.coeff s (quarticPolarWholeSeries m) := by
  rw [← currentMap_quarticPolarFormula,← quartic_polar_formula,currentMap_orbit,
    coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
  rfl

theorem quarticPolar_whole_coeff_mem (m s : ℕ) (hs : m < 4 + s) :
    PowerSeries.coeff s (quarticPolarWholeSeries m) ∈ AllM.candidateIdeal m := by
  rw [← currentMap_quarticPolarFormula,← quartic_polar_formula]
  exact current_orbit_coeff_mem m 4 2 2 2 s (by decide) hs

/-- The whole selected quintic source, with its quartic factor explicit. -/
theorem quarticWitness_whole_coeff (m : ℕ) :
    quarticWitness m = actualMode m (m-1) 0 *
      PowerSeries.coeff (m-2) (quarticPolarWholeSeries m) := by
  rw [quarticWitness,quartic_polar_formula,currentMap_quarticPolarFormula]

end
#print axioms currentMap_quarticPolarFormula
#print axioms quarticPolar_whole_coeff
#print axioms quarticPolar_whole_coeff_mem
#print axioms quarticWitness_whole_coeff
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
