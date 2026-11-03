/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE6FusionZ
import VOA.DeligneAudit.DeligneCharacterE7FusionZ
import VOA.DeligneAudit.E6FusionKernelTheta
import VOA.DeligneAudit.E7FusionKernelTheta

/-!
# `E₆`, `E₇`: U5 without the named count

The named counts `E6K.E6FusionCount`, `E7FusionCount` are stated for the clamped series
`hilbSeries e{6,7}DemazureHilb`.  The clamped count needs coefficient positivity, which comes from U5.
The circle is broken through the unclamped series:

* `realizationG_hilbSeriesG`: a realization of the clamped series is one of the unclamped series
  (`hilbIntG ≤ (hilbIntG).toNat`), so the literature input `hD` transfers unchanged;
* the kernel route `fusionModuleBoundG_of_kernel` with the unclamped series and the proved count
  (`e{6,7}FusionFZ_count`) gives U5 for `e{6,7}FusionFZ` (`e6_fusionModuleBoundZ_of_totalBound`);
* U5 gives positivity, hence clamped = unclamped (`e{6,7}_hilbSeries_eq_Z`), hence
  **`e6_fusionModuleBound_of_totalBound'`**: the original U5 statement from `hF` and `hD` alone, and
  **`e6FusionCount_of_totalBound`**: the named count itself (same inputs).  Likewise for `E₇`.
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneCharacter

/-- **Realization transfer**: clamped ⇒ unclamped. -/
theorem realizationG_hilbSeriesG {S : DeligneSectorData} {spec : ℕ → ℕ → RelSpec S.n}
    (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ) {n : ℕ}
    (hD : DemazureRealizationG S spec (hilbSeries (levelOneDemazureHilb A θ word)) n) :
    DemazureRealizationG S spec (hilbSeriesG A θ word) n := by
  obtain ⟨V, i1, i2, ρ, w, hrel, hdim⟩ := hD
  refine ⟨V, i1, i2, ρ, w, hrel, fun N => le_trans ?_ (hdim N)⟩
  rw [hilbSeriesG, hilbSeries, coeff_mk, coeff_mk, DemCount.levelOneDemazureHilb_eq]
  exact_mod_cast Int.self_le_toNat _

open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector) in
/-- **U5 for `e6FusionFZ`** from `FusionTotalBoundG E6sector` and the realizations. -/
theorem e6_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector) (hilbSeries e6DemazureHilb) n) :
    FusionModuleBoundG E6sector e6FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero E6sector) (ravFam_step E6sector) (ravKw_deg E6sector)
    hF E6K.e6_ravinderKernelRel' (fun n => realizationG_hilbSeriesG _ _ _ (hD n))
    (fun m => by simpa using e6FusionFZ_count m)

open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector) in
/-- **U5 for `E₆`** (original clamped statement) from `hF` and `hD` alone — no count input. -/
theorem e6_fusionModuleBound_of_totalBound' (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector) (hilbSeries e6DemazureHilb) n) :
    FusionModuleBoundG E6sector (fusionOf (hilbSeries e6DemazureHilb)) := by
  have h := e6_fusionModuleBoundZ_of_totalBound hF hD
  rw [e6_hilbSeries_eq_Z h]
  exact h

open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector) in
/-- **The named count `E6FusionCount`** from `hF` and `hD`. -/
theorem e6FusionCount_of_totalBound (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector) (hilbSeries e6DemazureHilb) n) :
    E6K.E6FusionCount := by
  intro m
  rw [e6_hilbSeries_eq_Z (e6_fusionModuleBoundZ_of_totalBound hF hD)]
  simpa using e6FusionFZ_count m

open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector) in
/-- **U5 for `e7FusionFZ`** from `FusionTotalBoundG E7sector` and the realizations. -/
theorem e7_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector) (hilbSeries e7DemazureHilb) n) :
    FusionModuleBoundG E7sector e7FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero E7sector) (ravFam_step E7sector) (ravKw_deg E7sector)
    hF e7_ravinderKernelRel' (fun n => realizationG_hilbSeriesG _ _ _ (hD n))
    (fun m => by simpa using e7FusionFZ_count m)

open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector) in
/-- **U5 for `E₇`** (original clamped statement) from `hF` and `hD` alone — no count input. -/
theorem e7_fusionModuleBound_of_totalBound' (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector) (hilbSeries e7DemazureHilb) n) :
    FusionModuleBoundG E7sector (fusionOf (hilbSeries e7DemazureHilb)) := by
  have h := e7_fusionModuleBoundZ_of_totalBound hF hD
  rw [e7_hilbSeries_eq_Z h]
  exact h

open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector) in
/-- **The named count `E7FusionCount`** from `hF` and `hD`. -/
theorem e7FusionCount_of_totalBound (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector) (hilbSeries e7DemazureHilb) n) :
    E7FusionCount := by
  intro m
  rw [e7_hilbSeries_eq_Z (e7_fusionModuleBoundZ_of_totalBound hF hD)]
  simpa using e7FusionFZ_count m

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e6_fusionModuleBound_of_totalBound'
#print axioms VOA.DeligneAudit.UnivG.e6FusionCount_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.e7_fusionModuleBound_of_totalBound'
#print axioms VOA.DeligneAudit.UnivG.e7FusionCount_of_totalBound
end AxiomAudit
