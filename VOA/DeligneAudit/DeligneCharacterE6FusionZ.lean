/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterFusionZ
import VOA.DeligneAudit.DeligneCharacterE6Count
import VOA.DeligneAudit.DeligneCharacterE6Energy

/-!
# `E₆`: the unclamped fusion layer

`e6FusionFZ := fusionOf (∑_N hilbIntG … qᴺ)` for the `E₆` Demazure data.  With the energies
(`DemCount.e6DemazureEnergy`) and the total (`DemCount.e6_demazure_total`, `79^m`) proved,
**U5 for `e6FusionFZ` follows from the squeeze inputs and the universal bound alone**
(`e6_fusionModuleBoundZ_of_squeeze'`).  Coefficient positivity, and hence the agreement of the
clamped `e6DemazureHilb` series with the unclamped one, is a consequence of U5 (`e6_hilbSeries_eq_Z`).
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.DeligneSector SectorWeyl VOA.DeligneAudit.DeligneCharacter

/-- The `E₆` unclamped Demazure series. -/
noncomputable abbrev e6HilbSeriesZ : ℕ → PowerSeries ℚ := hilbSeriesG cartanE6 thetaE6 wordE6

/-- The `E₆` fusion series of the unclamped Demazure series. -/
noncomputable abbrev e6FusionFZ : ℕ → PowerSeries ℚ := fusionFZ cartanE6 thetaE6 wordE6

theorem e6_total_succ (m : ℕ) :
    ((demazureChar cartanE6 thetaE6 wordE6 m).map (·.2)).sum = ((78 : ℕ) + 1 : ℤ) ^ m := by
  rw [DemCount.e6_demazure_total]; norm_num

/-- `e6FusionFZ m (1) = 78^m`, unconditionally. -/
theorem e6FusionFZ_count (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (e6FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (e6FusionFZ m) = ((78 : ℕ) : ℚ) ^ m :=
  fusionFZ_count _ _ _ 78 DemCount.e6DemazureEnergy e6_total_succ m

/-- **U5 for `E₆`** (`FusionModuleBoundG S e6FusionFZ`, any sector with `dim g = 78`) from the
squeeze inputs and the universal bound alone. -/
theorem e6_fusionModuleBoundZ_of_squeeze' (S : DeligneSectorData) (hn : S.n = 78)
    {M : ℕ → ℕ → PowerSeries ℚ} (h : FusionSqueezeInputsG e6HilbSeriesZ 78 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S e6FusionFZ :=
  fusionModuleBoundZ_of_squeeze _ _ _ S 78 hn DemCount.e6DemazureEnergy e6_total_succ h huniv

/-- Under U5, the clamped `E₆` Demazure series equals the unclamped one. -/
theorem e6_hilbSeries_eq_Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S e6FusionFZ) :
    hilbSeries e6DemazureHilb = e6HilbSeriesZ :=
  hilbSeries_eq_G _ _ _ hU5

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.e6FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.e6_fusionModuleBoundZ_of_squeeze'
#print axioms VOA.DeligneAudit.DeligneCarrier.e6_hilbSeries_eq_Z
end AxiomAudit
