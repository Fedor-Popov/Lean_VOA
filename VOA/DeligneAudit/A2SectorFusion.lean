/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorAssembly
import VOA.DeligneAudit.A2SectorTensor
import VOA.DeligneAudit.A2SectorFiber

/-!
# Reducing `SectorFusionBound` to the current-only sector (the `1/(q)_d` split)

the `SectorFusionBound F` bounds the current carrier with `m` currents and `d` auxiliary
spectators by `F_m/((q)_m (q)_d)`.  The `1/(q)_d` factor is the auxiliary symmetric-polynomial
tensor factor.  This file splits the bound into

* `AuxiliaryTensorGrading` (**proved**: `auxiliaryTensorGrading`, from
  `SectorTensor.finrank_currentCarrier_le`) — the graded form of the tensor split
  `currentCarrier m d ≅ currentCarrier m 0 ⊗ ℂ[z₁,…,z_d]^{S_d}`:
  `dim (m,d)_r ≤ Σ_{a ≤ r} dim (m,0)_a · p_{≤d}(r-a)`.  Commutative algebra, no literature input
  (the ungraded equivalence is `QuadraticCurrentAuxiliaryTensor.currentAuxiliaryTensorEquiv`).
* `CurrentFusionBound F` — the current-only sector: `dim (m,0)_a ≤ [q^a] F_m/(q)_m`.  This is
  B4–B8 with U4 (global Weyl modules are free over the symmetric algebra with local Weyl fibre,
  Chari–Fourier–Khandai) and U5 (fusion upper bound, Ravinder/Feigin).

`sectorFusionBound_of_split` proves `SectorFusionBound F` from the two, using the proved
`1/(q)_d = Σ_N p_{≤d}(N) q^N` (`partitionsLe_series`).
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.DeligneAudit.CarrierChain

noncomputable section

/-- **Graded auxiliary tensor split** (formalization target): the `(m,d)` current carrier in
degree `r` is bounded by the current-only carrier tensored with the symmetric polynomials in `d`
variables, whose Hilbert series is `1/(q)_d`. -/
structure AuxiliaryTensorGrading : Prop where
  le : ∀ m d r, currentDim m d r ≤
    ∑ a ∈ Finset.range (r + 1), currentDim m 0 a * partitionsLe d (r - a)

/-- **Current-only fusion bound** (B4–B8 with U4, U5): `Hilb (m,0) ≤ F_m/(q)_m`. -/
structure CurrentFusionBound (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ m a, (currentDim m 0 a : ℚ) ≤ coeff a (F m * (qpoch m)⁻¹)

/-- **`SectorFusionBound` from the graded tensor split and the current-only bound.** -/
theorem sectorFusionBound_of_split (F : ℕ → PowerSeries ℚ) (hT : AuxiliaryTensorGrading)
    (hC : CurrentFusionBound F) : SectorFusionBound F := by
  refine ⟨fun m d r => ?_⟩
  rw [partitionsLe_series d, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc (currentDim m d r : ℚ)
      ≤ ((∑ a ∈ Finset.range (r + 1), currentDim m 0 a * partitionsLe d (r - a) : ℕ) : ℚ) := by
        exact_mod_cast hT.le m d r
    _ = ∑ a ∈ Finset.range (r + 1), (currentDim m 0 a : ℚ) * (partitionsLe d (r - a) : ℚ) := by
        push_cast; rfl
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [partitionSeries, coeff_mk]
        exact mul_le_mul_of_nonneg_right (hC.le m a) (by positivity)

/-- **The graded auxiliary tensor split holds** (no hypothesis). -/
theorem auxiliaryTensorGrading : AuxiliaryTensorGrading :=
  ⟨fun m d r => SectorTensor.finrank_currentCarrier_le fullMatrix m d r⟩

/-- `SectorFusionBound F` from the current-only bound alone. -/
theorem sectorFusionBound_of_current (F : ℕ → PowerSeries ℚ) (hC : CurrentFusionBound F) :
    SectorFusionBound F :=
  sectorFusionBound_of_split F auxiliaryTensorGrading hC

open VOA.DeligneHigherRankConditionalCapstone in
/-- **A₂ Deligne classical freeness from five named inputs, with the auxiliary factor proved**:
`CasimirLayerBound` (B1), `CurrentFusionBound F` (B4–B8 with U4, U5),
`MixedFusionRecursion F demazureHilbSeries` (U6), `StarIdentity`, `KacWakimotoLowerBound`. -/
theorem classicallyFree_of_currentInputs (F : ℕ → PowerSeries ℚ)
    (hL : CasimirLayerBound) (hC : CurrentFusionBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_sectorInputs F hL (sectorFusionBound_of_current F hC) hU6 hstar hkw

/-! ## The fibre reduction of `CurrentFusionBound` -/

/-- Dimension of the degree-`b` fibre `W_m / B_{m,+} W_m` of the current-only carrier over the
symmetric polynomials in the `m` current roots. -/
def currentFiberDim (m b : ℕ) : ℕ :=
  SectorNakayama.fiberDim (SectorFiber.symDeg (K := ℂ) m) (SectorFiber.carrierDeg fullMatrix m) b

/-- **Fibre bound (B5–B8 with U4, U5)**: the fibre of `W_m` at the origin has graded dimension at
most `[q^b] F_m`.  In the paper `W_m = M_m` is free over `B_m` with fibre of character exactly
`F_m` (B6, B8), a quotient of `W_loc(mθ)/⟨(f_α ⊗ t^m) w⟩` (U4, CFK) whose dimension is bounded by
U5 (Ravinder/Feigin). -/
structure CurrentFiberBound (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ m b, (currentFiberDim m b : ℚ) ≤ coeff b (F m)

/-- `CurrentFusionBound` from the fibre bound (graded Nakayama, proved). -/
theorem currentFusionBound_of_fiber (F : ℕ → PowerSeries ℚ) (hF : CurrentFiberBound F) :
    CurrentFusionBound F := by
  refine ⟨fun m a => ?_⟩
  rw [partitionsLe_series m, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc (currentDim m 0 a : ℚ)
      ≤ ((∑ b ∈ Finset.range (a + 1), currentFiberDim m b * partitionsLe m (a - b) : ℕ) : ℚ) := by
        exact_mod_cast SectorFiber.finrank_current_le_fiber fullMatrix m a
    _ = ∑ b ∈ Finset.range (a + 1), (currentFiberDim m b : ℚ) * (partitionsLe m (a - b) : ℚ) := by
        push_cast; rfl
    _ ≤ _ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [partitionSeries, coeff_mk]
        exact mul_le_mul_of_nonneg_right (hF.le m b) (by positivity)

open VOA.DeligneHigherRankConditionalCapstone in
/-- **A₂ Deligne classical freeness from five named inputs, with the auxiliary factor and the
`1/(q)_m` factor proved**: `CasimirLayerBound` (B1), `CurrentFiberBound F` (B5–B8 with U4, U5),
`MixedFusionRecursion F demazureHilbSeries` (U6), `StarIdentity`, `KacWakimotoLowerBound`. -/
theorem classicallyFree_of_fiberInputs (F : ℕ → PowerSeries ℚ)
    (hL : CasimirLayerBound) (hF : CurrentFiberBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_currentInputs F hL (currentFusionBound_of_fiber F hF) hU6 hstar hkw

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.currentFusionBound_of_fiber
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_fiberInputs
#print axioms VOA.DeligneAudit.A2.auxiliaryTensorGrading
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_currentInputs
#print axioms VOA.DeligneAudit.A2.sectorFusionBound_of_split
end AxiomAudit
