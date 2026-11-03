/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Assembly
import VOA.DeligneAudit.A2CarrierFiltration

/-!
# Gluing the carrier chain to the Demazure interface, and the refined A₂ headline

the chain bounds the carrier by `demazureCoeffOf Dem N = Σ_n [q^N] q^n Dem_n/(q)_n` for an
abstract family of power series `Dem`; the interface defines the concrete natural numbers
`demazureCoeff N = Σ_n [q^{N-n}] (demazureHilb n) · (partitions into parts ≤ n)`.

* `partitionsLe_series`: `Σ_N partitionsLe n N q^N = 1/(q)_n` (proved from the defining sum by the
  recurrence `p_{≤n+1}(N) = p_{≤n}(N) + p_{≤n+1}(N-n-1)`).
* `demazureCoeff_eq_demazureCoeffOf`: the tie `hD` for `Dem := demazureHilbSeries`, the power series
  with coefficients `demazureHilb n`.  The two definitions agree exactly; no discrepancy.
* `classicallyFree_of_sectorInputs`: **A₂ classical freeness from exactly** `CasimirLayerBound`,
  `SectorFusionBound F`, `MixedFusionRecursion F demazureHilbSeries`, `StarIdentity`,
  `KacWakimotoLowerBound`.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.DeligneAudit.CarrierChain VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-! ## `1/(q)_n` is the partition generating function -/

theorem partitionsLe_succ_of_lt (n N : ℕ) (h : N < n + 1) :
    partitionsLe (n + 1) N = partitionsLe n N := by
  rw [partitionsLe, Nat.div_eq_of_lt h]
  simp

theorem partitionsLe_succ_of_le (n N : ℕ) (h : n + 1 ≤ N) :
    partitionsLe (n + 1) N = partitionsLe n N + partitionsLe (n + 1) (N - (n + 1)) := by
  have hdiv : N / (n + 1) = (N - (n + 1)) / (n + 1) + 1 := by
    rw [← Nat.sub_add_cancel h, Nat.add_div_right _ (Nat.succ_pos n), Nat.add_sub_cancel]
  rw [partitionsLe, partitionsLe, hdiv, Finset.sum_range_succ']
  simp only [zero_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Nat.sub_sub, add_mul, one_mul, add_comm]

/-- The partition series `Σ_N p_{≤n}(N) q^N`. -/
def partitionSeries (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (partitionsLe n N : ℚ)

theorem partitionSeries_mul_qpoch (n : ℕ) : partitionSeries n * qpoch n = 1 := by
  induction n with
  | zero =>
      ext N
      simp only [qpoch, qpochGen_zero, mul_one, partitionSeries, coeff_mk, coeff_one]
      rcases N with _ | N <;> simp [partitionsLe]
  | succ n ih =>
      have hstep : partitionSeries (n + 1) * (1 - X ^ (n + 1)) = partitionSeries n := by
        ext N
        rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', partitionSeries, partitionSeries,
          coeff_mk, coeff_mk]
        split_ifs with h
        · rw [coeff_mk, partitionsLe_succ_of_le n N h]
          push_cast
          ring
        · rw [partitionsLe_succ_of_lt n N (by omega), sub_zero, coeff_mk]
      rw [qpoch, qpochGen_succ, ← mul_assoc, mul_comm (partitionSeries (n + 1)), mul_assoc,
        hstep]
      rw [mul_comm]
      exact ih

/-- **`1/(q)_n = Σ_N p_{≤n}(N) q^N`.** -/
theorem partitionsLe_series (n : ℕ) : (qpoch n)⁻¹ = partitionSeries n :=
  ((PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_qpoch]; exact one_ne_zero)).mpr
    (partitionSeries_mul_qpoch n)).symm

/-! ## The tie `hD` -/

/-- The `demazureHilb n` as a power series over `ℚ`. -/
def demazureHilbSeries (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (demazureHilb n N : ℚ)

theorem coeff_mk_mul_mk (f g : ℕ → ℕ) (M : ℕ) :
    coeff M (PowerSeries.mk (fun N => (f N : ℚ)) * PowerSeries.mk fun N => (g N : ℚ)) =
      (conv f g M : ℚ) := by
  rw [coeff_mul, conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  simp

/-- **The carrier–character tie.**  The concrete Demazure sum is the `demazureCoeffOf` for the series of
`demazureHilb`. -/
theorem demazureCoeff_eq_demazureCoeffOf (N : ℕ) :
    (demazureCoeff N : ℚ) = demazureCoeffOf demazureHilbSeries N := by
  rw [demazureCoeff, demazureCoeffOf]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [mul_assoc, coeff_X_pow_mul', if_pos hnN, partitionsLe_series, demazureHilbSeries,
    partitionSeries, coeff_mk_mul_mk]

/-! ## Refined headline -/

/-- The carrier bound by the `demazureCoeff`, from the sector inputs. -/
theorem carrier_le_demazureCoeff (F : ℕ → PowerSeries ℚ) (hL : CasimirLayerBound)
    (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F demazureHilbSeries) (N : ℕ) :
    (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤ demazureCoeff N :=
  carrierDim_le_demazure_of_layerBound F demazureHilbSeries demazureCoeff
    demazureCoeff_eq_demazureCoeffOf hL hF hU6 N

/-- **A₂ Deligne classical freeness from exactly five named inputs**: the Casimir layer bound
(B1, formalization target), the sector fusion bound (B2–B8 with U4, U5), the mixed fusion
recursion for `demazureHilb` (U6), the star identity, and the lower half of Kac–Wakimoto.  The
conclusion also identifies `I₂ⁿˢ` with the full `C₂` kernel. -/
theorem classicallyFree_of_sectorInputs (F : ℕ → PowerSeries ℚ)
    (hL : CasimirLayerBound) (hF : SectorFusionBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_residualInputs (carrier_le_demazureCoeff F hL hF hU6) hstar hkw

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.partitionsLe_series
#print axioms VOA.DeligneAudit.A2.demazureCoeff_eq_demazureCoeffOf
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_sectorInputs
end AxiomAudit
