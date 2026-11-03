/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterFusionZ
import VOA.DeligneAudit.DeligneCharacterE8Count
import VOA.DeligneAudit.DeligneCharacterE8Energy

/-!
# `E₈`: the unclamped fusion layer

`e8FusionFZ := fusionOf (∑_N hilbIntG … qᴺ)` for the `E₈` Demazure data.  With the energies
(`DemCount.e8DemazureEnergy`) and the total (`DemCount.e8_demazure_total`, `249^m`) proved,
**U5 for `e8FusionFZ` follows from the squeeze inputs and the universal bound alone**
(`e8_fusionModuleBoundZ_of_squeeze'`).  Coefficient positivity, and hence the agreement of the
clamped `e8DemazureHilb` series with the unclamped one, is a consequence of U5 (`e8_hilbSeries_eq_Z`).
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.DeligneSector SectorWeyl VOA.DeligneAudit.DeligneCharacter

/-- The `E₈` unclamped Demazure series. -/
noncomputable abbrev e8HilbSeriesZ : ℕ → PowerSeries ℚ := hilbSeriesG cartanE8 thetaE8 wordE8

/-- The `E₈` fusion series of the unclamped Demazure series. -/
noncomputable abbrev e8FusionFZ : ℕ → PowerSeries ℚ := fusionFZ cartanE8 thetaE8 wordE8

theorem e8_total_succ (m : ℕ) :
    ((demazureChar cartanE8 thetaE8 wordE8 m).map (·.2)).sum = ((248 : ℕ) + 1 : ℤ) ^ m := by
  rw [DemCount.e8_demazure_total]; norm_num

/-- `e8FusionFZ m (1) = 248^m`, unconditionally. -/
theorem e8FusionFZ_count (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (e8FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (e8FusionFZ m) = ((248 : ℕ) : ℚ) ^ m :=
  fusionFZ_count _ _ _ 248 DemCount.e8DemazureEnergy e8_total_succ m

/-- **U5 for `E₈`** (`FusionModuleBoundG S e8FusionFZ`, any sector with `dim g = 248`) from the
squeeze inputs and the universal bound alone. -/
theorem e8_fusionModuleBoundZ_of_squeeze' (S : DeligneSectorData) (hn : S.n = 248)
    {M : ℕ → ℕ → PowerSeries ℚ} (h : FusionSqueezeInputsG e8HilbSeriesZ 248 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S e8FusionFZ :=
  fusionModuleBoundZ_of_squeeze _ _ _ S 248 hn DemCount.e8DemazureEnergy e8_total_succ h huniv

/-- Under U5, the clamped `E₈` Demazure series equals the unclamped one. -/
theorem e8_hilbSeries_eq_Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S e8FusionFZ) :
    hilbSeries e8DemazureHilb = e8HilbSeriesZ :=
  hilbSeries_eq_G _ _ _ hU5

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.e8FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.e8_fusionModuleBoundZ_of_squeeze'
#print axioms VOA.DeligneAudit.DeligneCarrier.e8_hilbSeries_eq_Z
end AxiomAudit
