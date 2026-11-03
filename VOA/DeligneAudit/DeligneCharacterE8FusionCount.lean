/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8FusionZ
import VOA.DeligneAudit.DeligneCharacterEFusionCount
import VOA.DeligneAudit.E8FusionKernelTheta

/-!
# `E₈`: U5 without the named count

The `E₈` analogue of the `DeligneCharacterEFusionCount` (for `E₆`, `E₇`).

The named count `E8K.E8FusionCount` is stated for the clamped series `hilbSeries e8DemazureHilb`.
The circle is broken through the unclamped series:

* `realizationG_hilbSeriesG` transfers the realizations from the clamped series to the unclamped one;
* the kernel route `fusionModuleBoundG_of_kernel`, with the `E8K.e8_ravinderKernelRel'` and the proved
  unclamped count `e8FusionFZ_count` (`248^m`), gives U5 for `e8FusionFZ`
  (`e8_fusionModuleBoundZ_of_totalBound`);
* U5 gives clamped = unclamped (`e8_hilbSeries_eq_Z`), hence:
  - **`e8_fusionModuleBound_of_totalBound'`**, the original U5 statement from `hF` and `hD` alone;
  - **`e8FusionCount_of_totalBound`**, the named count `E8K.E8FusionCount` itself, from the same inputs.
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneCharacter

open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector) in
/-- **U5 for `e8FusionFZ`** from `FusionTotalBoundG E8sector` and the realizations. -/
theorem e8_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector) (hilbSeries e8DemazureHilb) n) :
    FusionModuleBoundG E8sector e8FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero E8sector) (ravFam_step E8sector) (ravKw_deg E8sector)
    hF E8K.e8_ravinderKernelRel' (fun n => realizationG_hilbSeriesG _ _ _ (hD n))
    (fun m => by simpa using e8FusionFZ_count m)

open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector) in
/-- **U5 for `E₈`** (original clamped statement) from `hF` and `hD` alone — no count input. -/
theorem e8_fusionModuleBound_of_totalBound' (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector) (hilbSeries e8DemazureHilb) n) :
    FusionModuleBoundG E8sector (fusionOf (hilbSeries e8DemazureHilb)) := by
  have h := e8_fusionModuleBoundZ_of_totalBound hF hD
  rw [e8_hilbSeries_eq_Z h]
  exact h

open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector) in
/-- **The named count `E8K.E8FusionCount`** from `hF` and `hD`. -/
theorem e8FusionCount_of_totalBound (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector) (hilbSeries e8DemazureHilb) n) :
    E8K.E8FusionCount := by
  intro m
  rw [e8_hilbSeries_eq_Z (e8_fusionModuleBoundZ_of_totalBound hF hD)]
  simpa using e8FusionFZ_count m

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e8_fusionModuleBoundZ_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.e8_fusionModuleBound_of_totalBound'
#print axioms VOA.DeligneAudit.UnivG.e8FusionCount_of_totalBound
end AxiomAudit
