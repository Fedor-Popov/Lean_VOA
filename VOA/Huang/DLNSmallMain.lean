import VOA.Huang.DLNSmallThreePower
import VOA.Huang.DLNSmallTwoPower
import VOA.Classification.COne.MainBeyl

/-!
# Consequences of `threePowerSchur`

With `DLNSchur.ThreePowerSchur` (`DLNSchur.threePowerSchur`) and
`DLNSchur.TwoPowerInflationFromTwo` (`DLNSchur.twoPowerInflationFromTwo_holds`) proved, the only
remaining Beyl residual is `LargePrimeGaussLowerRelations` (primes `p ≥ 5`).

Every theorem here is CONDITIONAL on the displayed hypotheses.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-- The odd prime-power Schur residual is exactly the large-prime residual. -/
theorem oddPrimePowerSchur_iff_largePrimeRootRelations :
    OddPrimePowerSchur ↔ LargePrimeRootRelations :=
  ⟨fun h => (oddPrimePowerSchur_iff_rootRelations_and_three.mp h).1,
    fun h => oddPrimePowerSchur_iff_rootRelations_and_three.mpr ⟨h, threePowerSchur⟩⟩

theorem oddPrimePowerSchur_iff_largePrimeGaussLowerRelations :
    OddPrimePowerSchur ↔ LargePrimeGaussLowerRelations :=
  oddPrimePowerSchur_iff_largePrimeRootRelations.trans
    largePrimeRootRelations_iff_gaussLowerRelations

/-- DLN matrix lifting from the two remaining residuals. -/
theorem matrixDLNLifting_of_large_and_two
    (hlarge : LargePrimeGaussLowerRelations) (htwo : TwoPowerInflationFromTwo) :
    VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_gaussLowerRelations hlarge threePowerSchur htwo

/-- DLN matrix lifting from the large-prime residual alone. -/
theorem matrixDLNLifting_of_large (hlarge : LargePrimeGaussLowerRelations) :
    VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_gaussLowerRelations hlarge threePowerSchur twoPowerInflationFromTwo_holds

/-- Beyl's inflation theorem for all moduli, from the odd prime-power Schur statement alone. -/
theorem beylInflationSL2_of_odd (hodd : OddPrimePowerSchur) : BeylInflationSL2 :=
  beylInflationSL2_of_local hodd twoPowerInflation_holds

/-- Beyl's inflation theorem for all moduli, from the large-prime residual alone. -/
theorem beylInflationSL2_of_large (hlarge : LargePrimeGaussLowerRelations) : BeylInflationSL2 :=
  beylInflationSL2_of_odd (oddPrimePowerSchur_iff_largePrimeGaussLowerRelations.mpr hlarge)

end VOA.Huang.DLNSchur

namespace VOA.Classification.COne

universe u

/-- **Forward Gannon–Rayhaun, conditional only on the large-prime and two-adic residuals.**
The prime-3 hypothesis of `gannonRayhaun_beyl_fine` is discharged by
`DLNSchur.threePowerSchur`. -/
theorem gannonRayhaun_beyl_large_two
    (hlarge : VOA.Huang.DLNSchur.LargePrimeGaussLowerRelations)
    (htwo : VOA.Huang.DLNSchur.TwoPowerInflationFromTwo) : GannonRayhaunStatement.{u} :=
  gannonRayhaun_beyl_fine hlarge VOA.Huang.DLNSchur.threePowerSchur htwo

/-- **Forward Gannon–Rayhaun, conditional only on the large-prime residual** (primes `p ≥ 5`).
Both the prime-3 and the two-adic hypotheses of `gannonRayhaun_beyl_fine` are discharged. -/
theorem gannonRayhaun_beyl_large
    (hlarge : VOA.Huang.DLNSchur.LargePrimeGaussLowerRelations) : GannonRayhaunStatement.{u} :=
  gannonRayhaun_beyl_fine hlarge VOA.Huang.DLNSchur.threePowerSchur
    VOA.Huang.DLNSchur.twoPowerInflationFromTwo_holds

end VOA.Classification.COne
