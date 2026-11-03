/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierData

/-!
# Type-generic version of `A2CarrierChain`

Mechanically generalized from the A₂ file `A2CarrierChain` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial PowerSeries
open VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAuxiliaryCollision
open VOA.DeligneAudit.CarrierChain
open VOA.DeligneAudit.CarrierEmbedding
open VOA.DeligneHigherRankConditionalCapstone
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D
/-! ### Sector dimensions -/

/-- Dimension of the `(m,d)` auxiliary sector carrier in derivative degree `p`
(conformal weight `m + 2d + p`). -/
def auxDim (m d p : ℕ) : ℕ :=
  Module.finrank ℂ (degreePiece (auxiliaryCarrier D.fullMatrix m d) p)

/-- Dimension of the current carrier with `d` auxiliary spectators in degree `r`. -/
def currentDim (m d r : ℕ) : ℕ :=
  Module.finrank ℂ (degreePiece (currentCarrier D.fullMatrix m d) r)

theorem auxDim_conductor_add (m d r : ℕ) :
    (auxDim D) m d (conductorDegree m d + r) = (currentDim D) m d r :=
  finrank_auxiliary_eq_current D.fullMatrix m d r

theorem auxDim_eq_zero_of_lt (m d p : ℕ) (hp : p < conductorDegree m d) : (auxDim D) m d p = 0 := by
  haveI : Subsingleton (degreePiece (auxiliaryCarrier D.fullMatrix m d) p) :=
    ⟨fun x y => by
      rw [auxiliary_degreePiece_eq_zero_of_lt D.fullMatrix m d p hp x,
        auxiliary_degreePiece_eq_zero_of_lt D.fullMatrix m d p hp y]⟩
  exact Module.finrank_zero_of_subsingleton

/-- The carrier side, `Σ_p dim A2.Carrier p N = dim Jet(R̃)_N`. -/
def carrierDim (N : ℕ) : ℕ := ∑ p ∈ Finset.range (N + 1), Module.finrank ℂ ((Carrier D) p N)

/-- The weight-`N` contribution of sector `(m,d)`. -/
def sectorDim (N m d : ℕ) : ℕ := if m + 2 * d ≤ N then (auxDim D) m d (N - m - 2 * d) else 0

/-! ### Named hypotheses -/

/-- **B1 (Casimir/auxiliary filtration).**  The Casimir-adic filtration of `Jet(Sym sl₃/I₂ⁿˢ)` has
associated sectors that are quotients of the auxiliary sectors, so in every conformal weight the jet
algebra is bounded by the sum of the auxiliary sector carriers.  Not a literature input.
**Proved** for every `D`: `DeligneCarrier.casimirAuxiliaryBound` (`DeligneCarrierLayerBound.lean`;
U3 is `D.u3`, `D.Q_sq_mem`, `mixed_jetRelation_mem`, `casimirSq_jetRelation_mem`). -/
structure CasimirAuxiliaryBound : Prop where
  le : ∀ N, (carrierDim D) N ≤
    ∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n, (sectorDim D) N md.1 md.2

/-- **Sector fusion bound (B2–B8 with U4, U5).**  The current carrier of the full `I₂` with `m`
currents and `d` auxiliary spectators has Hilbert series bounded by `F_m / ((q)_m (q)_d)`.  The
`1/(q)_d` factor is the proved tensor split with `ℂ[v]^{S_d}` (`QuadraticCurrentAuxiliaryTensor`);
`Hilb W_m ≤ F_m/(q)_m` is B4–B8; in the paper with U4 (Chari–Fourier–Khandai) and U5
(Ravinder/Feigin), `F_m` the graded character of the fusion fiber `W_loc(mθ)/⟨(f_α⊗t^m)w⟩`.
The Lean chain uses U5 only: `X_sectorFusionBound_of_U5` (`G2Divisor.lean`, …, `E8Divisor.lean`)
and `A2_sectorFusionBound_generic` (`DeligneSectorA2.lean`). -/
structure SectorFusionBound (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ m d r, ((currentDim D) m d r : ℚ) ≤ coeff r (F m * (qpoch m)⁻¹ * (qpoch d)⁻¹)

/-- **U6 (mixed fusion recursion, Ravinder Cor. 1).**  `Dem n = Hilb Dz(1,nθ)` is `M_{n,0}` for the
recursion `M_{a+1,b} = M_{a,b+1} + q^{2a+b+1} M_{a,b}` with `M_{0,b} = F b`. -/
structure MixedFusionRecursion (F Dem : ℕ → PowerSeries ℚ) : Prop where
  eq : ∀ n, Dem n = VOA.DeligneGaussian.mixed (X : PowerSeries ℚ) F n 0

/-! ### Assembly -/

theorem sector_exponent (m d : ℕ) :
    m + d + d * (m + d) = m + 2 * d + conductorDegree m d := by
  rw [conductorDegree_eq]
  cases d with
  | zero => simp
  | succ d => simp only [Nat.add_sub_cancel]; ring

theorem sectorDim_le_coeff (F : ℕ → PowerSeries ℚ) (hF : (SectorFusionBound D) F) (N m d : ℕ) :
    ((sectorDim D) N m d : ℚ) ≤ coeff N (sectorTerm F m d) := by
  rw [sectorTerm, coeff_X_pow_mul', (sector_exponent D)]
  unfold sectorDim
  split_ifs with h1 h2 h2
  · -- the sector is present and the conductor fits
    obtain ⟨r, hr⟩ : ∃ r, N - m - 2 * d = conductorDegree m d + r :=
      ⟨N - m - 2 * d - conductorDegree m d, by omega⟩
    rw [hr, (auxDim_conductor_add D), show N - (m + 2 * d + conductorDegree m d) = r by omega]
    exact hF.le m d r
  · rw [(auxDim_eq_zero_of_lt D) m d _ (by omega)]
    simp
  · omega
  · simp

/-- **(Carrier D) side of the A₂ inequality**, against the Demazure-side coefficients built from
`Dem`. -/
theorem carrierDim_le_demazureCoeffOf (F Dem : ℕ → PowerSeries ℚ)
    (hB1 : (CasimirAuxiliaryBound D)) (hF : (SectorFusionBound D) F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : ((carrierDim D) N : ℚ) ≤ demazureCoeffOf Dem N := by
  rw [← sectorCoeff_eq_of_mixed F Dem hU6.eq, sectorCoeff]
  calc ((carrierDim D) N : ℚ)
      ≤ ((∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n,
          (sectorDim D) N md.1 md.2 : ℕ) : ℚ) := by exact_mod_cast hB1.le N
    _ = ∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n,
          ((sectorDim D) N md.1 md.2 : ℚ) := by push_cast; rfl
    _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun md _ =>
          (sectorDim_le_coeff D) F hF N md.1 md.2

/-- **Interface with the character side.**  For any `Dz : ℕ → ℕ` whose values are the Demazure coefficients
`[q^N] Σ_n q^n Dem_n/(q)_n`, the carrier is bounded by `Dz`. -/
theorem carrierDim_le_demazure (F Dem : ℕ → PowerSeries ℚ) (Dz : ℕ → ℕ)
    (hD : ∀ N, (Dz N : ℚ) = demazureCoeffOf Dem N)
    (hB1 : (CasimirAuxiliaryBound D)) (hF : (SectorFusionBound D) F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : (carrierDim D) N ≤ Dz N := by
  have h := (carrierDim_le_demazureCoeffOf D) F Dem hB1 hF hU6 N
  rw [← hD] at h
  exact_mod_cast h

/-- **Closing the A₂ inequality.**  Together with the character side `D_N ≤ dim V_N`, the carrier
upper bound `QuadraticCarrierUpperBound D.rel W` holds. -/
theorem quadraticCarrierUpperBound_of_chain {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (F Dem : ℕ → PowerSeries ℚ) (Dz : ℕ → ℕ)
    (hD : ∀ N, (Dz N : ℚ) = demazureCoeffOf Dem N)
    (hB1 : (CasimirAuxiliaryBound D)) (hF : (SectorFusionBound D) F) (hU6 : MixedFusionRecursion F Dem)
    (hchar : ∀ N, Dz N ≤ Module.finrank ℂ (W.grading N)) :
    QuadraticCarrierUpperBound D.rel W :=
  ⟨fun N => ((carrierDim_le_demazure D) F Dem Dz hD hB1 hF hU6 N).trans (hchar N)⟩

end

end VOA.DeligneAudit.DeligneCarrier
