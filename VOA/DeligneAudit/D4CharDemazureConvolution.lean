import VOA.DeligneAudit.D4CharKernelIdentification
import VOA.DeligneAudit.D4CharThetaReindex
import VOA.DeligneAudit.D4FiniteStatementProof

/-! Comparing the normalized theta integral with the actual Demazure coefficients. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter PowerSeries

noncomputable section

/-- The complete three-index theta series, in t = s squared. -/
def rsTripleSeries : D4K.S :=
  PowerSeries.mk fun n => rsMoment (coeff (2 * n) rsMixedKernel)

theorem rsMixed_moment_expand :
    D4K.smap rsMoment rsMixedKernel = expand 2 two_ne_zero rsTripleSeries := by
  apply PowerSeries.ext
  intro n
  rw [D4K.coeff_smap]
  by_cases hn : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_expand_mul]
    simp only [rsTripleSeries, coeff_mk]
  · rw [coeff_expand_of_not_dvd _ _ _ hn]
    have he : n = 2 * (n / 2) + 1 := by omega
    rw [he, rsMixedKernel_moment_odd]

/-- A scalar series can be pulled through every coefficientwise linear functional. -/
theorem rsSmap_lift_mul (L : D4K.R →ₗ[D4K.Kq] D4K.R)
    (A : PowerSeries D4K.Kq) (F : D4K.S) :
    D4K.smap L (D4K.liftS A * F) = D4K.liftS A * D4K.smap L F := by
  apply PowerSeries.ext
  intro n
  simp only [D4K.coeff_smap, coeff_mul, map_sum, D4K.liftS, coeff_map]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]

theorem rsSmap_expand (L : D4K.R →ₗ[D4K.Kq] D4K.R) (F : D4K.S) :
    D4K.smap L (expand 2 two_ne_zero F) =
      expand 2 two_ne_zero (D4K.smap L F) := by
  apply PowerSeries.ext
  intro n
  simp only [D4K.coeff_smap, coeff_expand]
  split_ifs <;> simp only [D4K.coeff_smap, map_zero]

/-- Euler inversion turns the normalized kernel moment into a four-part convolution. -/
theorem rsKernel_moment_expand :
    D4K.smap rsMoment D4K.kernelM =
      expand 2 two_ne_zero (D4K.liftS D4K.eInv * rsTripleSeries) := by
  have he : D4K.EInv 1 0 2 two_ne_zero =
      D4K.liftS (expand 2 two_ne_zero D4K.eInv) := by
    rw [D4K.EInv, rsMon_zero, map_one, rescale_one, RingHom.id_apply]
    apply PowerSeries.ext
    intro n
    simp only [D4K.liftS, coeff_map, coeff_expand]
    split_ifs <;> simp only [map_zero] <;> rfl
  rw [rsKernelM_eq_inv_mul_mixed, he, rsSmap_lift_mul, rsMixed_moment_expand]
  rw [map_mul]
  congr 1
  exact he.symm.trans (by
    rw [D4K.EInv, rsMon_zero, map_one, rescale_one, RingHom.id_apply])

/-- The original Demazure coefficient theorem with the theta factor two normalized away. -/
theorem rsKernel_moment_demazure (n : ℕ) :
    rsMoment (coeff (2 * n) D4K.kernelM) = (D4K.qpoch n)⁻¹ • D4K.Cdem n := by
  have ht := D4K.Ikernel_coeff_even D4Finite.d4FiniteIdentity_holds n
  rw [D4K.Ikernel, D4K.coeff_smap] at ht
  change (2 : D4K.Kq)⁻¹ • D4K.ctTheta (coeff (2 * n) D4K.kernelM) = _
  rw [ht, smul_smul, ← mul_assoc]
  have h2 : (2 : D4K.Kq) ≠ 0 := HahnSeries.C_ne_zero two_ne_zero
  rw [inv_mul_cancel₀ h2, one_mul]

/-- All four multiplicity degrees occur: the last one is supplied by Euler inversion. -/
theorem rsCdem_convolution (n : ℕ) :
    (D4K.qpoch n)⁻¹ • D4K.Cdem n =
      ∑ c ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n - c + 1),
        ∑ b ∈ Finset.range (n - c - a + 1),
          ((D4K.qpoch c)⁻¹ * ((D4K.qpoch a)⁻¹ * (D4K.qpoch b)⁻¹ *
            (D4K.qpoch (n - c - a - b))⁻¹)) •
            gtEval rsNome rsZAlphabet 4
              (gtMixedFourRow ((a + b : ℕ) : ℤ) b
                ((a + (n - c - a - b) : ℕ) : ℤ) ((n - c - a - b : ℕ) : ℤ)) := by
  have hh := congrArg (coeff (2 * n)) rsKernel_moment_expand
  rw [D4K.coeff_smap, rsKernel_moment_demazure, coeff_expand_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro c _
  simp only [D4K.liftS, coeff_map, D4K.eInv, coeff_mk, rsTripleSeries]
  rw [← Algebra.smul_def, rsMixedKernel_moment_even]
  simp only [Finset.smul_sum, smul_smul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMixed_moment_expand
#print axioms VOA.DeligneAudit.D4Char.rsSmap_lift_mul
#print axioms VOA.DeligneAudit.D4Char.rsSmap_expand
#print axioms VOA.DeligneAudit.D4Char.rsKernel_moment_expand
#print axioms VOA.DeligneAudit.D4Char.rsKernel_moment_demazure
#print axioms VOA.DeligneAudit.D4Char.rsCdem_convolution
