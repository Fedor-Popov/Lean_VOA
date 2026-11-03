/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierDemazure
import VOA.DeligneAudit.A2CarrierChain

/-!
# A₂ as an instance of the type-generic carrier chain

`A2data` packages the A₂ data (`relationMatrix`, `casimirMatrix`, U3 from `A2CarrierCasimir`).
The generic carrier, carrier dimension, current dimension and sector bound coincide with the A₂
ones, and the generic theorems re-derive the A₂ carrier side.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- **The A₂ type data.** -/
def A2data : DeligneCarrierData where
  n := 8
  ρ := Fin 8
  rel := A2.relationMatrix
  cas := A2.casimirMatrix
  u3 a := by
    have h := A2.X_mul_casimir_mem_I2ns a
    rwa [A2.casimir_eq_quadraticRelation, A2.I2ns_eq_quadraticIdeal] at h

theorem A2data_I : A2data.I = A2.I2ns := A2.I2ns_eq_quadraticIdeal.symm

theorem A2data_Q : A2data.Q = A2.casimir := A2.casimir_eq_quadraticRelation.symm

theorem A2data_carrier (p N : ℕ) : A2data.Carrier p N = A2.Carrier p N := rfl

theorem A2data_carrierDim (N : ℕ) : carrierDim A2data N = A2.carrierDim N := rfl

theorem A2data_fullMatrix : A2data.fullMatrix = A2.fullMatrix := by
  funext o
  cases o <;> rfl

theorem A2data_currentDim : currentDim A2data = A2.currentDim := by
  funext m d r
  unfold currentDim A2.currentDim
  rw [A2data_fullMatrix]
  rfl

theorem sectorFusionBound_A2_iff (F : ℕ → PowerSeries ℚ) :
    SectorFusionBound A2data F ↔ A2.SectorFusionBound F := by
  constructor
  · intro h; exact ⟨fun m d r => by rw [← A2data_currentDim]; exact h.le m d r⟩
  · intro h; exact ⟨fun m d r => by rw [A2data_currentDim]; exact h.le m d r⟩

/-- B1 for A₂, re-derived from the generic theorem. -/
theorem A2_casimirLayerBound_generic : CasimirLayerBound A2data := casimirLayerBound A2data

/-- **The A₂ carrier side, re-derived generically**: `Σ_p dim A2.Carrier p N ≤ demazureCoeff N`
from the A₂ sector fusion bound and U6. -/
theorem A2_carrierDim_le_demazureCoeff (F : ℕ → PowerSeries ℚ) (hF : A2.SectorFusionBound F)
    (hU6 : MixedFusionRecursion F (hilbSeries A2.demazureHilb)) (N : ℕ) :
    A2.carrierDim N ≤ A2.demazureCoeff N := by
  rw [← A2data_carrierDim, A2_demazureCoeff_eq_generic]
  exact carrierDim_le_demazureSum A2data A2.demazureHilb F ((sectorFusionBound_A2_iff F).mpr hF)
    hU6 N

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier
#print axioms A2data
#print axioms sectorFusionBound_A2_iff
#print axioms A2_casimirLayerBound_generic
#print axioms A2_carrierDim_le_demazureCoeff
end AxiomAudit
