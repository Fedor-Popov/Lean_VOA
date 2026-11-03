/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.DeligneCharacterDemazureCountSmallChecks
import VOA.DeligneAudit.DeligneCharacterD4Positivity
import VOA.DeligneAudit.G2Fusion

/-!
# The `q = 1` Demazure counts for `D₄` and `G₂`

Instances of `DemCount.demazureChar_total` (`C_m(1) = C_1(1)^m`, proved from the algorithm by the
twisted Leibniz rule of the Demazure operators at `q = 1`):

* **`d4_demazure_total`**: `∑ coeff (demazureChar D₄ m) = 29^m`, unconditional;
* **`d4DemazureCountZ`**: `∑_N hilbInt m N = 29^m` (unclamped graded count), unconditional
  (energy nonnegativity is the `energy_holds`);
* `d4DemazureCount_of_coeff`: the clamped `D4DemazureCount` from coefficient nonnegativity
  `∀ m N, 0 ≤ hilbInt m N` (the `coeff` half of `D4DemazurePositivity`);
* **`g2_demazure_total`**: `∑ coeff (demazureChar G₂ m) = 15^m`, unconditional;
* `g2DemazureCount_of`: the `G2DemazureCount` from energy and coefficient nonnegativity for `G₂`.

The finite inputs (the invariance of `C_1(q = 1)` under the reflections of the word and under `s_θ`, and
`C_1(1) = 29`, resp. `15`) are `decide +kernel` checks on `demazureChar … 1`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter Finset

/-! ## `D₄` -/

theorem d4_inv : invCheck cartanD4 thetaD4 wordD4 (demazureChar cartanD4 thetaD4 wordD4 1) = true := by
  have hchar : demazureChar cartanD4 thetaD4 wordD4 1 = D4Small.charOne :=
    D4Small.charOne_eq
  rw [hchar]
  exact SmallChecks.d4_inv

theorem d4_total_one : ((demazureChar cartanD4 thetaD4 wordD4 1).map (·.2)).sum = 29 := by
  change ((demazureChar [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]] [1, 2, 1, 1] [1, 0, 2, 1, 3, 1, 2, 0, 1] 1).map (·.2)).sum = 29
  rw [D4Small.charOne_eq]
  exact SmallChecks.d4_total

/-- **`D₄`: the total multiplicity of `D(1, mθ)` is `29^m`.** -/
theorem d4_demazure_total (m : ℕ) :
    ((demazureChar cartanD4 thetaD4 wordD4 m).map (·.2)).sum = 29 ^ m := by
  rw [demazureChar_total (r := 4) cartanD4 thetaD4 rfl wordD4
    (alpha_ne_zero_of cartanD4 thetaD4 wordD4 (by decide) ⟨⟨1, by omega⟩, by decide⟩)
    (inv_of_invCheck cartanD4 thetaD4 rfl wordD4 _ (toR1_demazureChar cartanD4 thetaD4 rfl wordD4 1).2
      d4_inv) m, d4_total_one]

/-- **`D₄` graded count, unclamped**: `∑_N hilbInt m N = 29^m`. -/
theorem d4DemazureCountZ (m : ℕ) :
    ∃ B, (∀ N : ℕ, B ≤ N → D4K.hilbInt m N = 0) ∧ ∑ N ∈ range B, D4K.hilbInt m N = 29 ^ m := by
  obtain ⟨B, h0, hs⟩ := hilbIntG_count cartanD4 thetaD4 wordD4 m (D4Wp.energy_holds m)
  exact ⟨B, h0, hs.trans (d4_demazure_total m)⟩

/-- The `D4DemazureCount` from the coefficient half of Demazure positivity. -/
theorem d4DemazureCount_of_coeff (hpos : ∀ m N : ℕ, 0 ≤ D4K.hilbInt m N) :
    DeligneCarrier.D4DemazureCount := by
  intro m
  obtain ⟨B, h0, hs⟩ := levelOneDemazureHilb_count cartanD4 thetaD4 wordD4 m (D4Wp.energy_holds m)
    (hpos m) (29 ^ m) (by rw [d4_demazure_total]; push_cast; rfl)
  exact ⟨B, h0, hs⟩

/-! ## `G₂` -/

theorem g2_inv : invCheck cartanG2 thetaG2 wordG2 (demazureChar cartanG2 thetaG2 wordG2 1) = true := by
  rw [exceptional_g2_char_one]
  exact SmallChecks.g2_inv

theorem g2_total_one : ((demazureChar cartanG2 thetaG2 wordG2 1).map (·.2)).sum = 15 := by
  rw [exceptional_g2_char_one]
  exact SmallChecks.g2_total

/-- **`G₂`: the total multiplicity of `D(1, mθ)` is `15^m`.** -/
theorem g2_demazure_total (m : ℕ) :
    ((demazureChar cartanG2 thetaG2 wordG2 m).map (·.2)).sum = 15 ^ m := by
  rw [demazureChar_total (r := 2) cartanG2 thetaG2 rfl wordG2
    (alpha_ne_zero_of cartanG2 thetaG2 wordG2 (by decide) ⟨⟨0, by omega⟩, by decide⟩)
    (inv_of_invCheck cartanG2 thetaG2 rfl wordG2 _ (toR1_demazureChar cartanG2 thetaG2 rfl wordG2 1).2
      g2_inv) m, g2_total_one]

/-- The `G2DemazureCount` from energy and coefficient nonnegativity for `G₂`. -/
theorem g2DemazureCount_of
    (henergy : ∀ m : ℕ, ∀ t ∈ demazureChar cartanG2 thetaG2 wordG2 m, 0 ≤ t.1.2 + (m : ℤ) * m)
    (hpos : ∀ m N : ℕ, 0 ≤ hilbIntG cartanG2 thetaG2 wordG2 m N) :
    DeligneCarrier.G2DemazureCount := by
  intro m
  obtain ⟨B, h0, hs⟩ := levelOneDemazureHilb_count cartanG2 thetaG2 wordG2 m (henergy m)
    (hpos m) (15 ^ m) (by rw [g2_demazure_total]; push_cast; rfl)
  exact ⟨B, h0, hs⟩

end VOA.DeligneAudit.DeligneCharacter.DemCount

/-! ## `D₄`: U5 for `d4FusionFZ` without `D4DemazureCount` -/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.DeligneSector SectorWeyl VOA.DeligneAudit.DeligneCharacter

/-- `d4FusionFZ m (1) = 28^m`, unconditionally (from `d4DemazureCountZ`). -/
theorem d4FusionFZ_count (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (D4Wp.d4FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (D4Wp.d4FusionFZ m) = ((28 : ℕ) : ℚ) ^ m := by
  refine fusionOf_count _ 28 (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := DemCount.d4DemazureCountZ n
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [D4Wp.hilbSeriesZ, coeff_mk, hB N hN]; simp
  · simp only [D4Wp.hilbSeriesZ, coeff_mk]
    rw [← Int.cast_sum, hs]
    norm_num

/-- **U5 for `D₄` in the unclamped form** (`FusionModuleBoundG D4sector d4FusionFZ`, the input of
`D4Lie.classicallyFree_of_fusionBoundZ`) from the squeeze inputs and the universal bound alone:
the count is a theorem (`d4FusionFZ_count`). -/
theorem d4_fusionModuleBoundZ_of_squeeze {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG D4Wp.hilbSeriesZ 28 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.D4sector.f V) (w : V),
      LocalWeylRelG VOA.DeligneAudit.DeligneSector.D4.D4sector ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG VOA.DeligneAudit.DeligneSector.D4.D4sector D4Wp.d4FusionFZ :=
  fusionModuleBoundG_of_squeeze _ d4sector_n h d4FusionFZ_count huniv

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.d4_demazure_total
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.d4DemazureCountZ
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.d4DemazureCount_of_coeff
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.g2_demazure_total
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.g2DemazureCount_of
#print axioms VOA.DeligneAudit.DeligneCarrier.d4FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.d4_fusionModuleBoundZ_of_squeeze
end AxiomAudit
