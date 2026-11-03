/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterFusionZ
import VOA.DeligneAudit.DeligneCharacterE7Count
import VOA.DeligneAudit.DeligneCharacterE7Energy

/-!
# `E₇`: the unclamped fusion layer

`e7FusionFZ := fusionOf (∑_N hilbIntG … qᴺ)` for the `E₇` Demazure data.  With the energies
(`DemCount.e7DemazureEnergy`) and the total (`DemCount.e7_demazure_total`, `134^m`) proved,
**U5 for `e7FusionFZ` follows from the squeeze inputs and the universal bound alone**
(`e7_fusionModuleBoundZ_of_squeeze'`).  Coefficient positivity, and hence the agreement of the
clamped `e7DemazureHilb` series with the unclamped one, is a consequence of U5 (`e7_hilbSeries_eq_Z`).
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.DeligneSector SectorWeyl VOA.DeligneAudit.DeligneCharacter

/-- The `E₇` unclamped Demazure series. -/
noncomputable abbrev e7HilbSeriesZ : ℕ → PowerSeries ℚ := hilbSeriesG cartanE7 thetaE7 wordE7

/-- The `E₇` fusion series of the unclamped Demazure series. -/
noncomputable abbrev e7FusionFZ : ℕ → PowerSeries ℚ := fusionFZ cartanE7 thetaE7 wordE7

theorem e7_total_succ (m : ℕ) :
    ((demazureChar cartanE7 thetaE7 wordE7 m).map (·.2)).sum = ((133 : ℕ) + 1 : ℤ) ^ m := by
  rw [DemCount.e7_demazure_total]; norm_num

/-- `e7FusionFZ m (1) = 133^m`, unconditionally. -/
theorem e7FusionFZ_count (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (e7FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (e7FusionFZ m) = ((133 : ℕ) : ℚ) ^ m :=
  fusionFZ_count _ _ _ 133 DemCount.e7DemazureEnergy e7_total_succ m

/-- **U5 for `E₇`** (`FusionModuleBoundG S e7FusionFZ`, any sector with `dim g = 133`) from the
squeeze inputs and the universal bound alone. -/
theorem e7_fusionModuleBoundZ_of_squeeze' (S : DeligneSectorData) (hn : S.n = 133)
    {M : ℕ → ℕ → PowerSeries ℚ} (h : FusionSqueezeInputsG e7HilbSeriesZ 133 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S e7FusionFZ :=
  fusionModuleBoundZ_of_squeeze _ _ _ S 133 hn DemCount.e7DemazureEnergy e7_total_succ h huniv

/-- Under U5, the clamped `E₇` Demazure series equals the unclamped one. -/
theorem e7_hilbSeries_eq_Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S e7FusionFZ) :
    hilbSeries e7DemazureHilb = e7HilbSeriesZ :=
  hilbSeries_eq_G _ _ _ hU5

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.e7FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.e7_fusionModuleBoundZ_of_squeeze'
#print axioms VOA.DeligneAudit.DeligneCarrier.e7_hilbSeries_eq_Z
end AxiomAudit
