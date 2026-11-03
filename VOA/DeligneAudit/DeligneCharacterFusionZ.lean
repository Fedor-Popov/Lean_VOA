/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.DeligneCharacterD4Positivity
import VOA.DeligneAudit.DeligneFusionSqueezeG

/-!
# The unclamped fusion layer, generic in the Demazure data

For Demazure data `(A, θ, word)` (the algorithm `demazureChar`):

* `hilbSeriesG`: the unclamped series `∑_N hilbIntG m N qᴺ`, and `fusionFZ := fusionOf hilbSeriesG`;
* `fusionFZ_count`: `fusionFZ m (1) = d^m` from nonnegative energies and the total `(d+1)^m`
  (both proved per type: `energy_of_orbit`, `demazureChar_total`);
* `fusionModuleBoundZ_of_squeeze`: **U5 for `fusionFZ`** from the squeeze inputs and the universal bound;
* `hilbIntG_nonneg_of_U5Z`: coefficient positivity is a consequence of U5.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.DeligneSector SectorWeyl VOA.DeligneAudit.DeligneCharacter
  VOA.DeligneAudit.DeligneCharacter.DemCount VOA.DeligneAudit.DeligneCharacter.D4Wp

noncomputable section

variable (A : List (List ℤ)) (θ : List ℤ) (word : List ℕ)

/-- The unclamped Demazure series. -/
def hilbSeriesG (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (hilbIntG A θ word n N : ℚ)

/-- The fusion series of the unclamped Demazure series. -/
def fusionFZ : ℕ → PowerSeries ℚ := fusionOf (hilbSeriesG A θ word)

theorem fusionFZ_count (d : ℕ)
    (henergy : ∀ m : ℕ, ∀ t ∈ demazureChar A θ word m, 0 ≤ t.1.2 + (m : ℤ) * m)
    (htot : ∀ m : ℕ, ((demazureChar A θ word m).map (·.2)).sum = ((d : ℤ) + 1) ^ m) (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (fusionFZ A θ word m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionFZ A θ word m) = (d : ℚ) ^ m := by
  refine fusionOf_count _ d (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := hilbIntG_count A θ word n (henergy n)
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [hilbSeriesG, coeff_mk, hB N hN]; simp
  · simp only [hilbSeriesG, coeff_mk]
    rw [← Int.cast_sum, hs, htot n]
    push_cast; ring

/-- **U5 for `fusionFZ`** from energies, the total, the squeeze inputs and the universal bound. -/
theorem fusionModuleBoundZ_of_squeeze (S : DeligneSectorData) (d : ℕ) (hn : S.n = d)
    {M : ℕ → ℕ → PowerSeries ℚ}
    (henergy : ∀ m : ℕ, ∀ t ∈ demazureChar A θ word m, 0 ≤ t.1.2 + (m : ℤ) * m)
    (htot : ∀ m : ℕ, ((demazureChar A θ word m).map (·.2)).sum = ((d : ℤ) + 1) ^ m)
    (h : FusionSqueezeInputsG (hilbSeriesG A θ word) d M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S (fusionFZ A θ word) :=
  fusionModuleBoundG_of_squeeze S hn h (fusionFZ_count A θ word d henergy htot) huniv

/-- **Coefficient positivity** from U5 for `fusionFZ`. -/
theorem hilbIntG_nonneg_of_U5Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S (fusionFZ A θ word))
    (m N : ℕ) : 0 ≤ hilbIntG A θ word m N := by
  have hF : ∀ k, NN (fusionFZ A θ word k) := fun k b => F_coeff_nonneg hU5 k b
  have h := congrArg (coeff N) ((mixedFusionRecursion_fusionOf (hilbSeriesG A θ word)).eq m)
  rw [hilbSeriesG, coeff_mk, VOA.DeligneGaussian.mixed_eq] at h
  have hnn : NN (∑ d ∈ Finset.range (m + 1), X ^ (d * (m + 0)) *
      VOA.DeligneGaussian.qbinom (X : PowerSeries ℚ) m d * fusionFZ A θ word (m + 0 - d)) :=
    NN_sum _ _ fun d _ => ((NN_X_pow _).mul (NN_qbinom _ _)).mul (hF _)
  have := hnn N
  rw [fusionFZ] at this
  rw [← h] at this
  exact_mod_cast this

/-- The clamped series agrees with the unclamped one once U5 holds. -/
theorem hilbSeries_eq_G {S : DeligneSectorData} (hU5 : FusionModuleBoundG S (fusionFZ A θ word)) :
    hilbSeries (levelOneDemazureHilb A θ word) = hilbSeriesG A θ word := by
  funext m
  ext N : 1
  rw [hilbSeries, hilbSeriesG, coeff_mk, coeff_mk, levelOneDemazureHilb_eq]
  have := hilbIntG_nonneg_of_U5Z A θ word hU5 m N
  rw [show ((hilbIntG A θ word m N).toNat : ℚ) = (((hilbIntG A θ word m N).toNat : ℤ) : ℚ) by
    push_cast; rfl, Int.toNat_of_nonneg this]

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.fusionModuleBoundZ_of_squeeze
#print axioms VOA.DeligneAudit.DeligneCarrier.hilbSeries_eq_G
end AxiomAudit
