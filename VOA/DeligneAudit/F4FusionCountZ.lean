/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4FusionCountInv
import VOA.DeligneAudit.F4FusionCountEnergy
import VOA.DeligneAudit.F4LieKernel
import VOA.DeligneAudit.DeligneCharacterG2FusionZ

/-!
# The unclamped `F₄` route: `F₄` without the count input

Mirrors the `G₂` unclamped route (`DeligneCharacterG2FusionZ`):

* `f4HilbInt`, `f4HilbSeriesZ`, `f4FusionFZ := fusionOf f4HilbSeriesZ`;
* `f4DemazureCountZ` (`∑_N f4HilbInt m N = 53^m`, from `f4_demazure_total` and
  `f4DemazureEnergy`) and `f4FusionFZ_count` (`52^m`), unconditional;
* `f4HilbInt_nonneg_of_U5Z`, `f4FusionF_eq_Z`: coefficient positivity from U5 for the unclamped
  series;
* `realizationZ_of_clamped`: a realization of the clamped Demazure series is one of the unclamped
  series (`hilbInt ≤ toNat hilbInt`);
* `f4_classicallyFree_of_totalBound'`: the `F₄` case from `FusionTotalBoundG F4sector`, the
  (clamped) `F₄` Demazure realizations and `F4StarBound`, with no count input.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector SectorWeyl
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneCharacter.DemCount
  VOA.DeligneAudit.DeligneCharacter.D4Wp VOA.DeligneAudit.UnivG

noncomputable section

local notation "F4S" => VOA.DeligneAudit.DeligneSector.F4.F4sector

/-- `[q^N] q^{m²} C_m|_{z=1}` for `F₄`, unclamped. -/
def f4HilbInt (m : ℕ) (N : ℤ) : ℤ := hilbIntG cartanF4 thetaF4 wordF4 m N

theorem f4DemazureHilb_eq_toNat (m N : ℕ) : f4DemazureHilb m N = (f4HilbInt m N).toNat := rfl

/-- The unclamped `F₄` Demazure series. -/
def f4HilbSeriesZ (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (f4HilbInt n N : ℚ)

/-- The `F₄` fusion series of the unclamped Demazure series. -/
def f4FusionFZ : ℕ → PowerSeries ℚ := fusionOf f4HilbSeriesZ

theorem f4DemazureCountZ (m : ℕ) :
    ∃ B, (∀ N : ℕ, B ≤ N → f4HilbInt m N = 0) ∧ ∑ N ∈ Finset.range B, f4HilbInt m N = 53 ^ m := by
  obtain ⟨B, h0, hs⟩ := hilbIntG_count cartanF4 thetaF4 wordF4 m (f4DemazureEnergy m)
  exact ⟨B, h0, hs.trans (f4_demazure_total m)⟩

/-- **`f4FusionFZ m (1) = 52^m`**, unconditionally. -/
theorem f4FusionFZ_count (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (f4FusionFZ m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (f4FusionFZ m) = ((52 : ℕ) : ℚ) ^ m := by
  refine fusionOf_count _ 52 (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := f4DemazureCountZ n
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [f4HilbSeriesZ, coeff_mk, hB N hN]; simp
  · simp only [f4HilbSeriesZ, coeff_mk]
    rw [← Int.cast_sum, hs]
    norm_num

/-- **Coefficient positivity** from U5 for `f4FusionFZ`. -/
theorem f4HilbInt_nonneg_of_U5Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S f4FusionFZ)
    (m N : ℕ) : 0 ≤ f4HilbInt m N := by
  have hF : ∀ k, NN (f4FusionFZ k) := fun k b => F_coeff_nonneg hU5 k b
  have h := congrArg (coeff N) ((mixedFusionRecursion_fusionOf f4HilbSeriesZ).eq m)
  rw [f4HilbSeriesZ, coeff_mk, VOA.DeligneGaussian.mixed_eq] at h
  have hnn : NN (∑ d ∈ Finset.range (m + 1), X ^ (d * (m + 0)) *
      VOA.DeligneGaussian.qbinom (X : PowerSeries ℚ) m d * f4FusionFZ (m + 0 - d)) :=
    NN_sum _ _ fun d _ => ((NN_X_pow _).mul (NN_qbinom _ _)).mul (hF _)
  have := hnn N
  rw [f4FusionFZ] at this
  rw [← h] at this
  exact_mod_cast this

theorem hilbSeries_f4_eq_Z (hc : ∀ m N : ℕ, 0 ≤ f4HilbInt m N) :
    hilbSeries f4DemazureHilb = f4HilbSeriesZ := by
  funext m
  ext N : 1
  rw [hilbSeries, f4HilbSeriesZ, coeff_mk, coeff_mk, f4DemazureHilb_eq_toNat]
  have := hc m N
  rw [show ((f4HilbInt m N).toNat : ℚ) = (((f4HilbInt m N).toNat : ℤ) : ℚ) by push_cast; rfl,
    Int.toNat_of_nonneg this]

/-- **`f4FusionF = f4FusionFZ`** given U5 for the unclamped series. -/
theorem f4FusionF_eq_Z {S : DeligneSectorData} (hU5 : FusionModuleBoundG S f4FusionFZ) :
    F4Lie.f4FusionF = f4FusionFZ := by
  rw [F4Lie.f4FusionF, hilbSeries_f4_eq_Z (f4HilbInt_nonneg_of_U5Z hU5), f4FusionFZ]

/-- **Realization transfer**: a realization of the clamped `F₄` Demazure series realizes the
unclamped one (`f4HilbInt ≤ toNat f4HilbInt`). -/
theorem realizationZ_of_clamped {S : DeligneSectorData} {spec : ℕ → ℕ → RelSpec S.n} {n : ℕ}
    (h : DemazureRealizationG S spec (hilbSeries f4DemazureHilb) n) :
    DemazureRealizationG S spec f4HilbSeriesZ n := by
  obtain ⟨V, i1, i2, ρ, w, hs, hd⟩ := h
  refine ⟨V, i1, i2, ρ, w, hs, fun N => le_trans ?_ (hd N)⟩
  rw [f4HilbSeriesZ, hilbSeries, coeff_mk, coeff_mk, f4DemazureHilb_eq_toNat]
  have := Int.self_le_toNat (f4HilbInt n N)
  exact_mod_cast this

/-- **U5 for `f4FusionFZ`** from `FusionTotalBoundG` and the `F₄` Demazure realizations. -/
theorem f4_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG F4S)
    (hD : ∀ n, DemazureRealizationG F4S (ravFam F4S) (hilbSeries f4DemazureHilb) n) :
    FusionModuleBoundG F4S f4FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero _) (ravFam_step _) (ravKw_deg _)
    hF F4K.f4_ravinderKernelRel (fun n => realizationZ_of_clamped (hD n)) f4FusionFZ_count

/-- **The `F₄` case from `FusionTotalBoundG`, the Demazure realizations and `F4StarBound`**
(no count input; divisor comparison: the `f4_divisorComparison`). -/
theorem f4_classicallyFree_of_totalBound' (hF : FusionTotalBoundG F4S)
    (hD : ∀ n, DemazureRealizationG F4S (ravFam F4S) (hilbSeries f4DemazureHilb) n)
    (hB : F4StarBound) :
    CaseClassicallyFree .F4 F4Lie.f4W F4Lie.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass F4Lie.f4W 1 ⟨F4Lie.explicitPresentation.gen i,
          F4Lie.explicitPresentation.gen_weight_one i⟩).toRingHom =
        F4Lie.explicitPresentation.ideal := by
  have hU5 := f4_fusionModuleBoundZ_of_totalBound hF hD
  exact F4Lie.f4_classicallyFree_concrete' ((f4FusionF_eq_Z hU5) ▸ hU5) hB

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.f4FusionFZ_count
#print axioms VOA.DeligneAudit.DeligneCarrier.f4FusionF_eq_Z
#print axioms VOA.DeligneAudit.DeligneCarrier.f4_fusionModuleBoundZ_of_totalBound
#print axioms VOA.DeligneAudit.DeligneCarrier.f4_classicallyFree_of_totalBound'
end AxiomAudit
