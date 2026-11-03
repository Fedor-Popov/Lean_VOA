import VOA.Huang.GenusTwoPointSepEnergyFlow
import VOA.Huang.GenusTwoPointSepEnergyConjugation

/-!
# Unconditional normalized Zhu coordinate conjugation

The formal Jacobian identity identifies the Witt exponential with
(1+x) log(1+x). Its coefficients are exactly those of the existing square
energy operator. Both energy residuals and the all-mode law follow.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators

/-- The exact logarithmic energy vector field, at every formal degree. -/
theorem energyExponential_log :
    energyExponential (iterativeLog (logarithmicCoordinate 1)) =
      (1 + PowerSeries.X) * PowerSeries.log ℂ := by
  have h := energyExponential_mul_derivative (iterativeLog (logarithmicCoordinate 1))
  rw [flowExponential_log, derivative_log_eq_geoAltSeries] at h
  calc
    _ = energyExponential (iterativeLog (logarithmicCoordinate 1)) *
        ((1 + PowerSeries.X) * geoAltSeries) := by
      rw [onePlusX_mul_geoAltSeries, mul_one]
    _ = (1 + PowerSeries.X) *
        (energyExponential (iterativeLog (logarithmicCoordinate 1)) * geoAltSeries) := by ring
    _ = _ := by rw [h]

/-- The scalar residual is proved, uniformly in the degree. -/
theorem logarithmicEnergyCoefficients_holds : LogarithmicEnergyCoefficients := by
  intro n
  have h := congrArg (PowerSeries.coeff (n + 1)) energyExponential_log
  rw [energyExponential, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    ← logOnePlusXSeries_eq_log, logOnePlusX_eq_X_mul_u,
    show (1 + PowerSeries.X) * (PowerSeries.X * uSeries) =
      PowerSeries.X * ((1 + PowerSeries.X) * uSeries) by ring,
    PowerSeries.coeff_succ_X_mul] at h
  have hc := sqBracketCoeffZ_two_eq_coeff_Pw 0 (n : ℤ)
  have he : sqBracketCoeffZ 2 1 ((n + 1 : ℕ) : ℤ) =
      PowerSeries.coeff n ((1 + PowerSeries.X) * uSeries) := by
    simpa [Pw, uUnit_coe] using hc
  exact h.trans he.symm

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Zhu's state energy conjugation for the actual finite exponential. -/
theorem normalizedStateZeroConjugation_holds : NormalizedStateZeroConjugation W :=
  normalizedStateZeroConjugation_of_energyCoefficients logarithmicEnergyCoefficients_holds

/-- Zhu's module energy conjugation for every lowest-weight module. -/
theorem normalizedModuleZeroConjugation_holds (P : LWModule W) :
    NormalizedModuleZeroConjugation P :=
  normalizedModuleZeroConjugation_of_energyCoefficients P logarithmicEnergyCoefficients_holds

/-- All integer vertex modes obey the unchanged normalized coordinate law. -/
theorem normalizedSquareConjugation_holds (P : LWModule W) :
    NormalizedSquareConjugation P :=
  normalizedSquareConjugation_of_energyCoefficients P logarithmicEnergyCoefficients_holds

/-- Huang's scaled vertex-mode conjugation, retaining the mode-dependent factor. -/
theorem huangU_conjugation (P : LWModule W) (a : V) (m : ℤ) (x : P.carrier) :
    huangU P 0 (mode (P.isMod.YM a) m ((huangU P 0).symm x)) = huangModeScale m •
      SquareModule.sqMode P.isMod m (huangStateU W a) x :=
  huangU_conjugation_of_squareConjugation P (normalizedSquareConjugation_holds P) a m x

/-- Identification of the actual Hadamard expansion with coordinate substitution
for vertex-operator modes (integer modes of the module intertwiner). -/
theorem normalizedVertex_commutator_expansion (P : LWModule W)
    (a : V) (m : ℤ) (x : P.carrier) :
    (∑ᶠ r, conjugationCoeff
      (-moduleCoordGen P (iterativeLog (logarithmicCoordinate 1)))
      (-moduleCoordGen P (iterativeLog (logarithmicCoordinate 1)))
      (mode (P.isMod.YM a) m) r x) =
      SquareModule.sqMode P.isMod m (normalizedStateChange W a) x := by
  have h := expFun_conjugation_eq_finsum
    (moduleCoordGen_isLocNilp P (iterativeLog (logarithmicCoordinate 1))).neg
    (moduleCoordGen_isLocNilp P (iterativeLog (logarithmicCoordinate 1))).neg
    (mode (P.isMod.YM a) m) x
  change normalizedCoordinateChange P
    (mode (P.isMod.YM a) m ((normalizedCoordinateChange P).symm x)) = _ at h
  rw [← h, normalizedSquareConjugation_holds P, LinearEquiv.apply_symm_apply]

end VOA.Huang.GenusTwoPoint.Separate
