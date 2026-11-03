/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorB6
import VOA.DeligneAudit.A2SectorFusion
import VOA.DeligneAudit.DeligneCarrierChain

/-!
# The sector chain for any Deligne type

From the sector data `S`, the divisor comparison at `(Δ)` and U5 (with its total-dimension field):

* B8 (`W_m = M_m`): `carrierGenerationG` from B6 (`mFreeness`, proved from U5), the generic
  comparison (`genericComparisonG`, proved from coadjoint cyclicity) and the divisor comparison,
  by normality of `B_m`;
* the fibre bound: the Nakayama fibre of `W_m = M_m` is bounded through the fibre module of `M_m`
  by U5;
* graded Nakayama (`1/(q)_m`) and the auxiliary tensor split (`1/(q)_d`) then give
  `SectorFusionBound D F` for `D = S.toDeligneCarrierData`.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorNakayama
open VOA.QuadraticCurrentFunctionalCarrier VOA.HeightOneGlobalization
open VOA.DeligneAudit.A2 (discS discS_ne_zero partitionsLe partitionsLe_series partitionSeries)
open VOA.DeligneAudit.DeligneCarrier PowerSeries VOA.DeligneAudit.CarrierChain

noncomputable section

variable (S : DeligneSectorData)

/-- **Divisor comparison for the type** (B8 at `(Δ)`; the `PairComparison` route). -/
structure DivisorComparisonG : Prop where
  le : ∀ m, ∀ x ∈ currentCarrier S.fullMatrix m 0, ∀ p : HeightOnePrime (SymAlg (K := ℂ) m),
    discS m ∈ p.asIdeal → ∃ s : SymAlg (K := ℂ) m, s ∉ p.asIdeal ∧ s • x ∈ Mspace S.f m S.c₀

set_option synthInstance.maxHeartbeats 400000 in
/-- **B8 for the type**: `W_m ⊂ M_m`. -/
theorem carrierGenerationG (hF : MFreenessG S) (hD : DivisorComparisonG S) (m : ℕ) :
    currentCarrier S.fullMatrix m 0 ≤ Mspace S.f m S.c₀ := by
  intro x hx
  haveI := hF.free m
  haveI := hF.finite m
  let b := Module.Free.chooseBasis (SymAlg (K := ℂ) m) (MspaceR S m)
  have hn := genericComparisonG S m hx
  have hΔn : discS m ^ S.depth ≠ 0 := pow_ne_zero _ (discS_ne_zero m)
  change x ∈ MspaceR S m
  refine SectorGlobal.mem_of_local_witnesses (torsionFree S m) (MspaceR S m) b x
    ⟨_, hΔn, hn⟩ fun p => ?_
  by_cases hp : discS m ∈ p.asIdeal
  · exact hD.le m x hx p hp
  · exact ⟨discS m ^ S.depth, fun h => hp (p.isPrime.mem_of_pow_mem _ h), hn⟩

/-- Under B8 the carrier pieces are the pieces of `M_m`. -/
theorem carrierDeg_eq_Mdeg (hF : MFreenessG S) (hD : DivisorComparisonG S) (m b : ℕ) :
    carrierDeg S.fullMatrix m b = Mdeg S m b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨carrierGenerationG S hF hD m y.2, fun t => hy t⟩
  · rintro ⟨hxM, hxd⟩
    exact ⟨⟨x, Mspace_le S.f S.stable S.c₀ S.diag hxM⟩, fun t => hxd t, rfl⟩

/-- The Nakayama fibre dimension of `W_m`. -/
def currentFiberDimG (m b : ℕ) : ℕ :=
  fiberDim (symDeg (K := ℂ) m) (carrierDeg S.fullMatrix m) b

/-- **The fibre bound for the type**, from B8 and U5. -/
theorem currentFiberBoundG (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG S F)
    (hD : DivisorComparisonG S) (m b : ℕ) :
    (currentFiberDimG S m b : ℚ) ≤ coeff b (F m) := by
  have hF := mFreeness hU5
  have heq : currentFiberDimG S m b = fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b := by
    unfold currentFiberDimG
    have := funext (carrierDeg_eq_Mdeg S hF hD m)
    rw [this]
  rw [heq]
  calc (fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b : ℚ)
      ≤ (Module.finrank ℂ (cycDeg (fiberRepM S m) (wM S m) b) : ℚ) := by
        exact_mod_cast fiberDimM_le_cycDeg b
    _ ≤ _ := hU5.le m _ (fiberRepM S m) (wM S m) (localWeylRelM m) b

/-- **the `SectorFusionBound` for the type**, from U5 and the divisor comparison. -/
theorem sectorFusionBoundG (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG S F)
    (hD : DivisorComparisonG S) : SectorFusionBound S.toDeligneCarrierData F := by
  refine ⟨fun m d r => ?_⟩
  have hcur : ∀ a, (currentDim S.toDeligneCarrierData m 0 a : ℚ) ≤
      coeff a (F m * (qpoch m)⁻¹) := by
    intro a
    rw [partitionsLe_series m, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc (currentDim S.toDeligneCarrierData m 0 a : ℚ)
        ≤ ((∑ b ∈ Finset.range (a + 1), currentFiberDimG S m b * partitionsLe m (a - b) : ℕ) :
            ℚ) := by
          exact_mod_cast SectorFiber.finrank_current_le_fiber S.fullMatrix m a
      _ = ∑ b ∈ Finset.range (a + 1), (currentFiberDimG S m b : ℚ) *
            (partitionsLe m (a - b) : ℚ) := by push_cast; rfl
      _ ≤ _ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [partitionSeries, PowerSeries.coeff_mk]
          exact mul_le_mul_of_nonneg_right (currentFiberBoundG S F hU5 hD m b) (by positivity)
  rw [partitionsLe_series d, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc (currentDim S.toDeligneCarrierData m d r : ℚ)
      ≤ ((∑ a ∈ Finset.range (r + 1), currentDim S.toDeligneCarrierData m 0 a *
          partitionsLe d (r - a) : ℕ) : ℚ) := by
        exact_mod_cast SectorTensor.finrank_currentCarrier_le S.fullMatrix m d r
    _ = ∑ a ∈ Finset.range (r + 1), (currentDim S.toDeligneCarrierData m 0 a : ℚ) *
          (partitionsLe d (r - a) : ℚ) := by push_cast; rfl
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [partitionSeries, PowerSeries.coeff_mk]
        exact mul_le_mul_of_nonneg_right (hcur a) (by positivity)

end

end VOA.DeligneAudit.DeligneSector

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.genericComparisonG
#print axioms VOA.DeligneAudit.DeligneSector.mFreeness
#print axioms VOA.DeligneAudit.DeligneSector.carrierGenerationG
#print axioms VOA.DeligneAudit.DeligneSector.sectorFusionBoundG
end AxiomAudit
