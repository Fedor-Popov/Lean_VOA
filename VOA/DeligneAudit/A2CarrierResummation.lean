/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.GaussianTransform

/-!
# The auxiliary-carrier resummation (paper step D3)

With `(q)_n = ∏_{i=1}^{n} (1 - q^i)` and Gaussian binomials `[n,d]` (the q-Pascal recursion of
`GaussianTransform`), this file proves the product identity `[n,d] (q)_d (q)_{n-d} = (q)_n` and the
coefficientwise resummation

  `Σ_{m,d} q^{m+d+d(m+d)} F_m / ((q)_m (q)_d) = Σ_n q^n d_n / (q)_n`,
  `d_n = Σ_{d ≤ n} q^{n d} [n,d] F_{n-d}`,

for an arbitrary family of power series `F`.  The double series is truncated at `m + d ≤ N` in
conformal weight `N`; all other terms have zero `q^N` coefficient.  No Lie theory enters.
-/

namespace VOA.DeligneAudit.CarrierChain

open PowerSeries VOA.DeligneGaussian

noncomputable section

section Pochhammer

variable {R : Type*} [CommRing R] (q : R)

/-- The q-Pochhammer symbol `(q;q)_n = ∏_{i=1}^n (1 - q^i)`. -/
def qpochGen (n : ℕ) : R := ∏ i ∈ Finset.range n, (1 - q ^ (i + 1))

@[simp] theorem qpochGen_zero : qpochGen q 0 = 1 := by simp [qpochGen]

theorem qpochGen_succ (n : ℕ) : qpochGen q (n + 1) = qpochGen q n * (1 - q ^ (n + 1)) :=
  Finset.prod_range_succ _ _

/-- **Gaussian binomial product identity** `[n,d] (q)_d (q)_{n-d} = (q)_n`. -/
theorem qbinom_mul_qpochGen : ∀ n d : ℕ, d ≤ n →
    qbinom q n d * qpochGen q d * qpochGen q (n - d) = qpochGen q n
  | n, 0, _ => by simp
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
      have hk : k ≤ n := by omega
      rw [qbinom_succ_succ, qpochGen_succ q k, qpochGen_succ q n,
        show n + 1 - (k + 1) = n - k by omega]
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · have ih := qbinom_mul_qpochGen k k le_rfl
        rw [qbinom_eq_zero_of_lt q (Nat.lt_succ_self k), Nat.sub_self] at *
        simp only [pow_zero, one_mul, add_zero] at ih ⊢
        linear_combination (1 - q ^ (k + 1)) * ih
      · obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - (k + 1), by omega⟩
        have ih1 := qbinom_mul_qpochGen n k hk
        have ih2 := qbinom_mul_qpochGen n (k + 1) hlt
        rw [hm] at ih1 ⊢
        rw [show n - (k + 1) = m by omega, qpochGen_succ q k] at ih2
        rw [qpochGen_succ q m] at ih1 ⊢
        have he : q ^ (m + 1) * q ^ (k + 1) = q ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (q ^ (m + 1) * (1 - q ^ (k + 1))) * ih1 +
          (1 - q ^ (m + 1)) * ih2 - qpochGen q n * he

end Pochhammer

/-- `(q;q)_n` as a power series over `ℚ`. -/
abbrev qpoch (n : ℕ) : PowerSeries ℚ := qpochGen (X : PowerSeries ℚ) n

theorem constantCoeff_qpoch (n : ℕ) : constantCoeff (qpoch n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [qpoch, qpochGen_succ, ih]

theorem qpoch_mul_inv (n : ℕ) : qpoch n * (qpoch n)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_qpoch]; exact one_ne_zero)

/-- `[n,d] / (q)_n = 1 / ((q)_{n-d} (q)_d)`. -/
theorem qbinom_mul_inv_qpoch (n d : ℕ) (h : d ≤ n) :
    qbinom (X : PowerSeries ℚ) n d * (qpoch n)⁻¹ = (qpoch (n - d))⁻¹ * (qpoch d)⁻¹ := by
  have hb := qbinom_mul_qpochGen (X : PowerSeries ℚ) n d h
  have h1 := qpoch_mul_inv d
  have h2 := qpoch_mul_inv (n - d)
  have h3 := qpoch_mul_inv n
  set qb := qbinom (X : PowerSeries ℚ) n d
  set qd := qpoch d
  set qm := qpoch (n - d)
  set qn := qpoch n
  change qb * qd * qm = qn at hb
  linear_combination qn⁻¹ * qd⁻¹ * qm⁻¹ * hb - qb * qn⁻¹ * qm * qm⁻¹ * h1 - qb * qn⁻¹ * h2 +
    qd⁻¹ * qm⁻¹ * h3

/-- The Gaussian transform `d_n = Σ_{d ≤ n} q^{n d} [n,d] F_{n-d}` (the right side of
`demazure_eq_gaussian`). -/
def demazureSeries (F : ℕ → PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  ∑ d ∈ Finset.range (n + 1), X ^ (n * d) * qbinom (X : PowerSeries ℚ) n d * F (n - d)

/-- The `(m,d)` term of the auxiliary-carrier series `q^{m+d+d(m+d)} F_m / ((q)_m (q)_d)`. -/
def sectorTerm (F : ℕ → PowerSeries ℚ) (m d : ℕ) : PowerSeries ℚ :=
  X ^ (m + d + d * (m + d)) * (F m * (qpoch m)⁻¹ * (qpoch d)⁻¹)

theorem demazure_term_eq (F : ℕ → PowerSeries ℚ) (n : ℕ) :
    X ^ n * demazureSeries F n * (qpoch n)⁻¹ =
      ∑ d ∈ Finset.range (n + 1), sectorTerm F (n - d) d := by
  rw [demazureSeries, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have hinv := qbinom_mul_inv_qpoch n d hdn
  rw [sectorTerm, show n - d + d + d * (n - d + d) = n + n * d by
    rw [Nat.sub_add_cancel hdn]; ring, pow_add]
  linear_combination (X ^ n * X ^ (n * d) * F (n - d)) * hinv

/-- Conformal-weight-`N` coefficient of the auxiliary-carrier series, truncated at `m + d ≤ N`. -/
def sectorCoeff (F : ℕ → PowerSeries ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1), ∑ md ∈ Finset.antidiagonal n, coeff N (sectorTerm F md.1 md.2)

/-- Conformal-weight-`N` coefficient of `Σ_n q^n Dem_n / (q)_n`, truncated at `n ≤ N`. -/
def demazureCoeffOf (Dem : ℕ → PowerSeries ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1), coeff N (X ^ n * Dem n * (qpoch n)⁻¹)

/-- **Resummation (D3).** -/
theorem sectorCoeff_eq_demazureCoeffOf (F : ℕ → PowerSeries ℚ) (N : ℕ) :
    sectorCoeff F N = demazureCoeffOf (demazureSeries F) N := by
  rw [sectorCoeff, demazureCoeffOf]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [demazure_term_eq, map_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m d => coeff N (sectorTerm F m d)) n]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn := Finset.mem_range.mp hd
  congr 2; omega

/-- With the mixed fusion recursion (`Dem n = mixed q F n 0`), the Demazure side is the sector
series. -/
theorem sectorCoeff_eq_of_mixed (F Dem : ℕ → PowerSeries ℚ)
    (hDem : ∀ n, Dem n = mixed (X : PowerSeries ℚ) F n 0) (N : ℕ) :
    sectorCoeff F N = demazureCoeffOf Dem N := by
  rw [sectorCoeff_eq_demazureCoeffOf]
  unfold demazureCoeffOf
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hDem, demazure_eq_gaussian, demazureSeries]

end

end VOA.DeligneAudit.CarrierChain

section AxiomAudit
open VOA.DeligneAudit.CarrierChain
#print axioms qbinom_mul_qpochGen
#print axioms qbinom_mul_inv_qpoch
#print axioms demazure_term_eq
#print axioms sectorCoeff_eq_demazureCoeffOf
#print axioms sectorCoeff_eq_of_mixed
end AxiomAudit
