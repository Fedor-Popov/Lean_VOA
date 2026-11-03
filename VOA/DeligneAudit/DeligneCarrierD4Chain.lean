/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierD4
import VOA.DeligneAudit.DeligneCharacterD4

/-!
# The D₄ carrier side

The generic chain applied to `D4.D4data` and the `d4DemazureHilb`: B1 holds outright, and the
carrier is bounded by the D₄ Demazure sum given the sector fusion bound and U6.
-/

namespace VOA.DeligneAudit.DeligneCarrier.D4

open VOA.DeligneAudit.DeligneCharacter

/-- B1 for D₄. -/
theorem d4_casimirLayerBound : CasimirLayerBound D4data := casimirLayerBound D4data

/-- **D₄ carrier side**: `Σ_p dim Carrier p N ≤ D_N` for the D₄ Demazure sum. -/
theorem d4_carrierDim_le_demazureSum (F : ℕ → PowerSeries ℚ) (hF : SectorFusionBound D4data F)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb)) (N : ℕ) :
    carrierDim D4data N ≤ demazureSumCoeff d4DemazureHilb N :=
  carrierDim_le_demazureSum D4data d4DemazureHilb F hF hU6 N

end VOA.DeligneAudit.DeligneCarrier.D4

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier.D4
#print axioms d4_casimirLayerBound
#print axioms d4_carrierDim_le_demazureSum
end AxiomAudit
