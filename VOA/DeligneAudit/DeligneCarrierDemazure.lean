/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierLayerBound
import VOA.DeligneAudit.DeligneCharacter
import VOA.DeligneAudit.A2SectorAssembly

/-!
# The type-generic carrier chain to the Demazure sum

For type data `D` and any table `hilb` of Demazure Hilbert series (with sum
`DeligneCharacter.demazureSumCoeff hilb`):

* `demazureSumCoeff_eq_demazureCoeffOf`: the Demazure sum is the coefficient of the series
  `Σ_n q^n Hilb_n/(q)_n` used by the resummation (D3) of the chain;
* **`carrierDim_le_demazureSum`**: `Σ_p dim Carrier p N ≤ D_N`, from B1 (proved, `casimirLayerBound`),
  D3 (proved), and the named inputs `SectorFusionBound D F` (B2–B8, U4, U5) and
  `MixedFusionRecursion F (hilbSeries hilb)` (U6);
* **`carrierCharacterLowerBound_of_sector`**: the capstone's `CarrierCharacterLowerBound` for the
  literal carrier, given in addition the `DemazureBoundFor W hilb`.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneAudit.CarrierChain VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- The Demazure Hilbert series of a table, as power series over `ℚ`. -/
def hilbSeries (hilb : ℕ → ℕ → ℕ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (hilb n N : ℚ)

/-- **the Demazure sum equals the chain's resummed coefficient.** -/
theorem demazureSumCoeff_eq_demazureCoeffOf (hilb : ℕ → ℕ → ℕ) (N : ℕ) :
    (demazureSumCoeff hilb N : ℚ) = demazureCoeffOf (hilbSeries hilb) N := by
  rw [demazureSumCoeff, demazureCoeffOf]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [mul_assoc, coeff_X_pow_mul', if_pos hnN, A2.partitionsLe_series, hilbSeries,
    A2.partitionSeries, A2.coeff_mk_mul_mk]

/-- **Carrier side of the Deligne inequality, any type.** -/
theorem carrierDim_le_demazureSum (D : DeligneCarrierData) (hilb : ℕ → ℕ → ℕ)
    (F : ℕ → PowerSeries ℚ) (hF : SectorFusionBound D F)
    (hU6 : MixedFusionRecursion F (hilbSeries hilb)) (N : ℕ) :
    carrierDim D N ≤ demazureSumCoeff hilb N :=
  carrierDim_le_demazure_of_sector D F (hilbSeries hilb) (demazureSumCoeff hilb)
    (demazureSumCoeff_eq_demazureCoeffOf hilb) hF hU6 N

/-- **The capstone's carrier-character input, any type**, from the sector inputs and the
character side. -/
theorem carrierCharacterLowerBound_of_sector {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (D : DeligneCarrierData) (hilb : ℕ → ℕ → ℕ)
    (F : ℕ → PowerSeries ℚ) (hF : SectorFusionBound D F)
    (hU6 : MixedFusionRecursion F (hilbSeries hilb)) (hchr : DemazureBoundFor W hilb) :
    CarrierCharacterLowerBound W D.Carrier :=
  carrierCharacterLowerBound_of_demazureSum D.Carrier
    (carrierDim_le_demazureSum D hilb F hF hU6) hchr

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier
#print axioms casimirLayerBound
#print axioms casimirAuxiliaryBound
#print axioms demazureSumCoeff_eq_demazureCoeffOf
#print axioms carrierDim_le_demazureSum
#print axioms carrierCharacterLowerBound_of_sector
end AxiomAudit
