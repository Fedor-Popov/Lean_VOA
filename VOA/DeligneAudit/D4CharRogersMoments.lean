import VOA.DeligneAudit.D4CharThetaBinomial

/-! Rogers--Szego Laurent polynomials and their zero moments for the actual D4 theta map. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian DeligneCharacter

noncomputable section

/-- H_n(x) in the kernel's Laurent ring, with its original x coordinate. -/
def rsH (n : ℕ) : D4K.R :=
  ∑ j ∈ Finset.range (n + 1),
    D4K.mon (((n : ℤ) - 2 * j) • D4K.xv) (qbinom D4K.qq n j)

/-- The normalized theta functional; values retain the four spectator coordinates. -/
def rsMoment : D4K.R →ₗ[D4K.Kq] D4K.R := (2 : D4K.Kq)⁻¹ • D4K.ctTheta

theorem rsMon_zero (c : D4K.Kq) : D4K.mon 0 c = algebraMap D4K.Kq D4K.R c := rfl

theorem rsKillX (a : ℤ) : D4K.killX (a • D4K.xv) = 0 := by
  have h := D4K.killX_add_xv 0 a
  simpa [D4K.killX] using h

/-- The actual theta map on H_n is the finite Gaussian theta convolution. -/
theorem ctTheta_rsH_sum (n : ℕ) :
    D4K.ctTheta (rsH n) = algebraMap D4K.Kq D4K.R
      (∑ j ∈ Finset.range (n + 1),
        qbinom D4K.qq n j * D4K.thK (-((n : ℤ) - 2 * j))) := by
  rw [rsH, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [D4K.ctFun_mon, rsKillX, rsMon_zero]
  simp [D4K.xv]

/-- Parity kills every odd Rogers--Szego moment. -/
theorem ctTheta_rsH_odd (k : ℕ) : D4K.ctTheta (rsH (2 * k + 1)) = 0 := by
  rw [ctTheta_rsH_sum]
  have hz : (∑ j ∈ Finset.range (2 * k + 1 + 1),
      qbinom D4K.qq (2 * k + 1) j *
        D4K.thK (-(((2 * k + 1 : ℕ) : ℤ) - 2 * j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [D4K.thK_odd, mul_zero]
    rw [Int.not_even_iff_odd]
    refine ⟨(j : ℤ) - k - 1, ?_⟩
    push_cast
    ring
  rw [hz, map_zero]

/-- The two finite q-binomial zeros kill every positive even moment. -/
theorem ctTheta_rsH_even (k : ℕ) (hk : 0 < k) :
    D4K.ctTheta (rsH (2 * k)) = 0 := by
  rw [ctTheta_rsH_sum]
  have he : ∀ j : ℕ,
      D4K.thK (-(((2 * k : ℕ) : ℤ) - 2 * j)) =
        rsThetaSeed ((k : ℤ) - j) - rsThetaSeed ((k : ℤ) + 1 - j) := by
    intro j
    rw [show -(((2 * k : ℕ) : ℤ) - 2 * j) = 2 * -((k : ℤ) - j) by
      push_cast; ring, rsTheta_even_neg, rsThetaSeed_difference]
    congr 2
    ring
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib]
  change algebraMap D4K.Kq D4K.R
    (rsThetaSum (2 * k) k - rsThetaSum (2 * k) ((k + 1 : ℕ) : ℤ)) = 0
  rw [rsThetaSum_zero (2 * k) k hk (by omega),
    rsThetaSum_zero (2 * k) (k + 1) (by omega) (by omega), sub_self, map_zero]

@[simp] theorem rsH_zero : rsH 0 = 1 := by
  simp [rsH, D4K.mon, AddMonoidAlgebra.one_def]

/-- Lemma O(i), before dividing the theta functional by two. -/
theorem ctTheta_rsH (n : ℕ) :
    D4K.ctTheta (rsH n) = if n = 0 then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    rw [ctTheta_rsH_sum]
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.cast_zero, sub_zero, mul_zero, neg_zero,
      qbinom_zero_right, D4K.thK_zero, one_mul, map_ofNat, ite_true]
  · rw [if_neg hn]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have he : n = 2 * k := by omega
      rw [he]
      exact ctTheta_rsH_even k (by omega)
    · have he : n = 2 * k + 1 := by omega
      rw [he]
      exact ctTheta_rsH_odd k

/-- Lemma O(i), with the normalization used in the kernel identity. -/
theorem rsMoment_rsH (n : ℕ) : rsMoment (rsH n) = if n = 0 then 1 else 0 := by
  simp only [rsMoment, LinearMap.smul_apply, ctTheta_rsH]
  split_ifs
  · rw [show (2 : D4K.R) = (2 : D4K.Kq) • (1 : D4K.R) by
      rw [Algebra.smul_def, mul_one, map_ofNat]]
    have h2 : (2 : D4K.Kq) ≠ 0 := by
      rw [show (2 : D4K.Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm]
      exact HahnSeries.C_ne_zero two_ne_zero
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  · exact smul_zero _

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMon_zero
#print axioms VOA.DeligneAudit.D4Char.rsKillX
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH_sum
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH_odd
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH_even
#print axioms VOA.DeligneAudit.D4Char.rsH_zero
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH
#print axioms VOA.DeligneAudit.D4Char.rsMoment_rsH
