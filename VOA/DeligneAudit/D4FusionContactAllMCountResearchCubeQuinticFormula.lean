import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuinticLeading
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCubicFormula

/-! Whole exact current formula for the actual quintic source. Its lower
color tails are explicit; reducing those tails by earlier relations remains
a separate completion problem. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def cubicPolarWholeSeries (m : ℕ) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  (12:ℂ) • (AllM.current m 0 * AllM.current m 3 * AllM.current m 7) +
  (12:ℂ) • (AllM.current m 0 * AllM.current m 5 * AllM.current m 6) -
  (12:ℂ) • (AllM.current m 3 * AllM.current m 6 * AllM.current m 1) -
  (12:ℂ) • (AllM.current m 3 * AllM.current m 2 * AllM.current m 5) -
  (6:ℂ) • (AllM.current m 3^2 * AllM.current m 4)

theorem currentMap_cubicPolarFormula (m : ℕ) :
    currentMap m (cubicPolarFormula ℂ) = cubicPolarWholeSeries m := by
  simp only [cubicPolarFormula,map_add,map_mul,map_pow,map_ofNat,currentMap_X]
  simp [actualCurrent,cubeSign,cubeColor,Algebra.smul_def,cubicPolarWholeSeries,map_ofNat]
  ring

theorem cubicPolar_whole_coeff (m s : ℕ) :
    g0Deriv m 9 0 (g0Deriv m 9 0 (g0Deriv m 8 0
      (g0Deriv m 7 0 (AllMNormal.cubic m s)))) =
      PowerSeries.coeff s (cubicPolarWholeSeries m) := by
  rw [← cubic_polar_current_coeff,cubic_polar_formula,currentMap_cubicPolarFormula]

theorem lowCubicPolar_whole_coeff (m : ℕ) :
    AllMNormal.lowCubicPolar m = PowerSeries.coeff (m-2) (cubicPolarWholeSeries m) := by
  exact cubicPolar_whole_coeff m (m-2)

/-- All five whole color terms of the selected quintic row, at every m. -/
theorem quinticLowRow_whole_coeff (m : ℕ) :
    AllMNormal.quinticLowRow m = modeX m 1 0 * modeX m 2 (m-1) *
      PowerSeries.coeff (m-2) (cubicPolarWholeSeries m) := by
  rw [AllMNormal.quinticLowRow,lowCubicPolar_whole_coeff]

end
#print axioms cubicPolar_whole_coeff
#print axioms quinticLowRow_whole_coeff
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
