/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Carrier
import VOA.DeligneAudit.A2CarrierCasimir
import VOA.DeligneAudit.A2CarrierResummation
import VOA.Commutative.QuadraticCurrentGradedCarrier
import VOA.Commutative.DeligneAuxiliaryDegree

/-!
# The carrier side of the A₂ inequality: `Σ_p dim A2.Carrier p N ≤ D_N`

`D_N = [q^N] Σ_n q^n Hilb D(1,nθ)/(q)_n` is the Demazure sum.  The paper's chain is

  `dim Jet(R̃)_N ≤ Σ_{m,d} dim U_{m,d,N}`                      (B1, Casimir filtration; U3)
  `Σ_r dim U_{m,d}(cond + r) q^r ≤ F_m / ((q)_m (q)_d)`         (B2–B8; U4, U5)
  `Σ_{m,d} q^{m+d+d(m+d)} F_m/((q)_m(q)_d) = Σ_n q^n d_n/(q)_n`  (D3, proved here: resummation)
  `d_n = Hilb D(1,nθ)`                                          (U6, mixed fusion recursion)

Here `U_{m,d}` is the dual of the `(m,d)` sector of the auxiliary algebra, i.e. the literal carrier
`degreePiece (auxiliaryCarrier fullMatrix m d) p` with `m` currents and `d` Casimir particles in
conformal weight `m + 2d + p`, and `fullMatrix` encodes the full `I₂ = I₂ⁿˢ ⊕ ℂ·Q`.

This file proves the assembly `carrier_le_demazureCoeff` from three explicitly named hypothesis
structures (never axioms):

* `CasimirAuxiliaryBound` — step B1.  **Not a literature input**: it is commutative algebra
  (its input U3 is proved in `A2CarrierCasimir`) and is the next formalization target.
* `SectorFusionBound F` — B2–B8 together with U4 (global Weyl modules, Chari–Fourier–Khandai) and U5
  (Ravinder/Feigin fusion upper bound), with `F m` the graded character of the fusion fiber.
* `MixedFusionRecursion F Dem` — U6 (Ravinder Cor. 1: `Hilb D(1,nθ) = M_{n,0}` for the mixed fusion
  recursion with `M_{0,m} = F m`).

The resummation D3 and the conductor shift are proved (`sectorCoeff_eq_of_mixed`,
`finrank_auxiliary_eq_current`, `auxiliary_degreePiece_eq_zero_of_lt`).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial PowerSeries
open VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAuxiliaryCollision
open VOA.DeligneAudit.CarrierChain
open VOA.DeligneAudit.CarrierEmbedding
open VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-! ### The full quadratic ideal `I₂ = I₂ⁿˢ ⊕ ℂ Q` -/

/-- The Casimir as a coefficient matrix. -/
def casimirMatrix : Fin 8 × Fin 8 → ℂ :=
  entryMatrix [(6, 6, 2), (6, 7, 2), (7, 7, 2), (0, 3, 6), (1, 4, 6), (2, 5, 6)]

theorem casimir_eq_quadraticRelation : casimir = quadraticRelation casimirMatrix := by
  rw [casimirMatrix, quadraticRelation_entryMatrix]
  simp [casimir, q, MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

/-- The coefficient matrices of the full `I₂`: the Casimir (`none`) and the adjoint relations. -/
def fullMatrix : Option (Fin 8) → Fin 8 × Fin 8 → ℂ
  | none => casimirMatrix
  | some a => relationMatrix a

theorem quadraticRelation_fullMatrix_none : quadraticRelation (fullMatrix none) = casimir :=
  casimir_eq_quadraticRelation.symm

theorem quadraticRelation_fullMatrix_some (a : Fin 8) :
    quadraticRelation (fullMatrix (some a)) = relationPoly a :=
  (relationPoly_eq_quadraticRelation a).symm

/-! ### Sector dimensions -/

/-- Dimension of the `(m,d)` auxiliary sector carrier in derivative degree `p`
(conformal weight `m + 2d + p`). -/
def auxDim (m d p : ℕ) : ℕ :=
  Module.finrank ℂ (degreePiece (auxiliaryCarrier fullMatrix m d) p)

/-- Dimension of the current carrier with `d` auxiliary spectators in degree `r`. -/
def currentDim (m d r : ℕ) : ℕ :=
  Module.finrank ℂ (degreePiece (currentCarrier fullMatrix m d) r)

theorem auxDim_conductor_add (m d r : ℕ) :
    auxDim m d (conductorDegree m d + r) = currentDim m d r :=
  finrank_auxiliary_eq_current fullMatrix m d r

theorem auxDim_eq_zero_of_lt (m d p : ℕ) (hp : p < conductorDegree m d) : auxDim m d p = 0 := by
  haveI : Subsingleton (degreePiece (auxiliaryCarrier fullMatrix m d) p) :=
    ⟨fun x y => by
      rw [auxiliary_degreePiece_eq_zero_of_lt fullMatrix m d p hp x,
        auxiliary_degreePiece_eq_zero_of_lt fullMatrix m d p hp y]⟩
  exact Module.finrank_zero_of_subsingleton

/-- The carrier side, `Σ_p dim A2.Carrier p N = dim Jet(R̃)_N`. -/
def carrierDim (N : ℕ) : ℕ := ∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)

/-- The weight-`N` contribution of sector `(m,d)`. -/
def sectorDim (N m d : ℕ) : ℕ := if m + 2 * d ≤ N then auxDim m d (N - m - 2 * d) else 0

/-! ### Named hypotheses -/

/-- **B1 (Casimir/auxiliary filtration).**  The Casimir-adic filtration of `Jet(Sym sl₃/I₂ⁿˢ)` has
associated sectors that are quotients of the auxiliary sectors, so in every conformal weight the jet
algebra is bounded by the sum of the auxiliary sector carriers.  Not a literature input: a
formalization target (U3 is proved: `X_mul_casimir_mem_I2ns`, `casimir_sq_mem_I2ns`,
`mixed_jetRelation_mem`, `casimirSq_jetRelation_mem`). -/
structure CasimirAuxiliaryBound : Prop where
  le : ∀ N, carrierDim N ≤
    ∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n, sectorDim N md.1 md.2

/-- **Sector fusion bound (B2–B8 with U4, U5).**  The current carrier of the full `I₂` with `m`
currents and `d` auxiliary spectators has Hilbert series bounded by `F_m / ((q)_m (q)_d)`.  The
`1/(q)_d` factor is the proved tensor split with `ℂ[v]^{S_d}` (`QuadraticCurrentAuxiliaryTensor`);
`Hilb W_m ≤ F_m/(q)_m` is B4–B8 with U4 (Chari–Fourier–Khandai) and U5 (Ravinder/Feigin), `F_m`
the graded character of the fusion fiber `W_loc(mθ)/⟨(f_α⊗t^m)w⟩`. -/
structure SectorFusionBound (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ m d r, (currentDim m d r : ℚ) ≤ coeff r (F m * (qpoch m)⁻¹ * (qpoch d)⁻¹)

/-- **U6 (mixed fusion recursion, Ravinder Cor. 1).**  `Dem n = Hilb D(1,nθ)` is `M_{n,0}` for the
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

theorem sectorDim_le_coeff (F : ℕ → PowerSeries ℚ) (hF : SectorFusionBound F) (N m d : ℕ) :
    (sectorDim N m d : ℚ) ≤ coeff N (sectorTerm F m d) := by
  rw [sectorTerm, coeff_X_pow_mul', sector_exponent]
  unfold sectorDim
  split_ifs with h1 h2 h2
  · -- the sector is present and the conductor fits
    obtain ⟨r, hr⟩ : ∃ r, N - m - 2 * d = conductorDegree m d + r :=
      ⟨N - m - 2 * d - conductorDegree m d, by omega⟩
    rw [hr, auxDim_conductor_add, show N - (m + 2 * d + conductorDegree m d) = r by omega]
    exact hF.le m d r
  · rw [auxDim_eq_zero_of_lt m d _ (by omega)]
    simp
  · omega
  · simp

/-- **Carrier side of the A₂ inequality**, against the Demazure-side coefficients built from
`Dem`. -/
theorem carrierDim_le_demazureCoeffOf (F Dem : ℕ → PowerSeries ℚ)
    (hB1 : CasimirAuxiliaryBound) (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : (carrierDim N : ℚ) ≤ demazureCoeffOf Dem N := by
  rw [← sectorCoeff_eq_of_mixed F Dem hU6.eq, sectorCoeff]
  calc (carrierDim N : ℚ)
      ≤ ((∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n,
          sectorDim N md.1 md.2 : ℕ) : ℚ) := by exact_mod_cast hB1.le N
    _ = ∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n,
          (sectorDim N md.1 md.2 : ℚ) := by push_cast; rfl
    _ ≤ _ := Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun md _ =>
          sectorDim_le_coeff F hF N md.1 md.2

/-- **Interface with the character side.**  For any `D : ℕ → ℕ` whose values are the Demazure coefficients
`[q^N] Σ_n q^n Dem_n/(q)_n`, the carrier is bounded by `D`. -/
theorem carrierDim_le_demazure (F Dem : ℕ → PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ N, (D N : ℚ) = demazureCoeffOf Dem N)
    (hB1 : CasimirAuxiliaryBound) (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F Dem)
    (N : ℕ) : carrierDim N ≤ D N := by
  have h := carrierDim_le_demazureCoeffOf F Dem hB1 hF hU6 N
  rw [← hD] at h
  exact_mod_cast h

/-- **Closing the A₂ inequality.**  Together with the character side `D_N ≤ dim V_N`, the carrier
upper bound `QuadraticCarrierUpperBound relationMatrix W` holds. -/
theorem quadraticCarrierUpperBound_of_chain {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (F Dem : ℕ → PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ N, (D N : ℚ) = demazureCoeffOf Dem N)
    (hB1 : CasimirAuxiliaryBound) (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F Dem)
    (hchar : ∀ N, D N ≤ Module.finrank ℂ (W.grading N)) :
    QuadraticCarrierUpperBound relationMatrix W :=
  ⟨fun N => (carrierDim_le_demazure F Dem D hD hB1 hF hU6 N).trans (hchar N)⟩

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms casimir_eq_quadraticRelation
#print axioms auxDim_conductor_add
#print axioms auxDim_eq_zero_of_lt
#print axioms sector_exponent
#print axioms sectorDim_le_coeff
#print axioms carrierDim_le_demazureCoeffOf
#print axioms carrierDim_le_demazure
#print axioms quadraticCarrierUpperBound_of_chain
end AxiomAudit
