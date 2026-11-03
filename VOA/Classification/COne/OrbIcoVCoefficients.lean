import VOA.Classification.COne.OrbIcoVProbeNonzero
import VOA.Classification.COne.OrbIcoSCriteria

/-! Canonical actual coefficients of every two-tower icosahedral mode remainder.
Only the final numerical compatibility with Xu's constants remains separate. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbIco OrbIcoS OrbXu OrbC2c

def vacuumCoefficient (r : ℕ) : ℂ :=
  (2 : ℂ) ^ r * vacuumProbe (Wi.smul Xico (71 - 2 * r) Xico)

def sixthCoefficient (r : ℕ) : ℂ :=
  (2 : ℂ) ^ (r - 18) * sixthProbe (Wi.smul Xico (71 - 2 * r) Xico) /
    OrbIcoS.neutralProbe Xico

private theorem two_half_pow (n : ℕ) : (2 : ℂ) ^ n * (1 / 2 : ℂ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

/-- No existential choice of remainder coefficients remains. -/
theorem canonical_mode_remainder (r : ℕ) (hr : 18 ≤ r) (hmax : r < 50) :
    modeSymbol Wi Xico (71 - 2 * r) r (r - 18)
      (vacuumCoefficient r) (sixthCoefficient r) ∈
        virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  apply mode_remainder_of_measurements r hr hmax
    (vacuumCoefficient r) (sixthCoefficient r) vacuumProbe sixthProbe
    vacuumProbe_errors sixthProbe_errors (measurement_determinant_ne_zero r (r - 18))
  · rw [vacuumProbe_L_pow, vacuumProbe_L_pow, vacuumProbe_vacuum, vacuumProbe_Xico]
    simp only [mul_zero, mul_one, add_zero, vacuumCoefficient]
    calc
      _ = ((2 : ℂ) ^ r * (1 / 2 : ℂ) ^ r) *
          vacuumProbe (Wi.smul Xico (71 - 2 * r) Xico) := by rw [two_half_pow]; simp
      _ = _ := by ring
  · rw [sixthProbe_L_pow, sixthProbe_L_pow, sixthProbe_vacuum, sixthProbe_Xico]
    simp only [mul_zero, zero_add, sixthCoefficient]
    field_simp [neutralProbe_Xico_ne_zero]
    calc
      _ = ((2 : ℂ) ^ (r - 18) * (1 / 2 : ℂ) ^ (r - 18)) *
          sixthProbe (Wi.smul Xico (71 - 2 * r) Xico) := by
        rw [two_half_pow]; ring
      _ = _ := by ring

theorem canonical_weight74_remainder :
    modeSymbol Wi Xico (-3) 37 19 (vacuumCoefficient 37) (sixthCoefficient 37) ∈
      virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  simpa using canonical_mode_remainder 37 (by omega) (by omega)

theorem canonical_weight76_remainder :
    modeSymbol Wi Xico (-5) 38 20 (vacuumCoefficient 38) (sixthCoefficient 38) ∈
      virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  simpa using canonical_mode_remainder 38 (by omega) (by omega)

/-- The sole numerical gate, stated in terms of actual, fixed scalar functionals. -/
def ActualCoefficientCompatibility : Prop :=
  vacuumCoefficient 37 * sixthCoefficient 37 ≠ 0 ∧
  vacuumCoefficient 37 * (xuU38 : ℂ) = vacuumCoefficient 38 * (xuU37 : ℂ) ∧
  sixthCoefficient 37 * (xuV20 : ℂ) = sixthCoefficient 38 * (xuV19 : ℂ)

/-- Actual coefficient compatibility closes the unchanged original B4 target. -/
theorem icoSymbolRelations_of_actual_coefficients (hc : ActualCoefficientCompatibility) :
    IcoSymbolRelations :=
  icoSymbolRelations_of_remainders _ _ _ _ hc.1 hc.2.1 hc.2.2
    canonical_weight74_remainder canonical_weight76_remainder

end VOA.Classification.COne.OrbIcoV
