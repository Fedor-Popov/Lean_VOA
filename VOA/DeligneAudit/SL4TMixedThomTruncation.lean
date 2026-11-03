import VOA.DeligneAudit.SL4TMixedCharacteristicProduct

/-! # The no-root b-site and double-root a-site truncation identities -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The first no-root b-state loses one truncation site before taking a quotient. -/
theorem mixedBThom_first_truncation (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B) :
    Polynomial.C (mixedBThom q .s1) * X ^ (q.A + q.B - 1).toNat ∈
      mixedTruncationIdeal q := by
  have hv := hq
  simp only [MixedValid] at hv
  have hm : (q.A + q.B - 1).toNat + 1 = (q.A + q.B).toNat := by omega
  have hf : mixedSecondPolynomial q * mixedSecondAmbientComplement q =
      X ^ ((q.A + q.B - 1).toNat + 1) := by
    rw [hm]
    exact mixedSecond_ambient_factorization q hq
  have h := characteristic_constant_power_mem (mixedFirstPolynomial q)
    (mixedSecondPolynomial q) (mixedSecondAmbientComplement q)
    (mixedEvaluation q (mixedE 1 q.d2.toNat)) (q.A + q.B - 1).toNat ⊥ hf (by
      change _ = 0
      exact mixedSecondAmbientComplement_constant_annihilated q hq hB)
  simp only [Ideal.map_bot, sup_bot_eq, hm] at h
  rw [mixedFirstPolynomial_constant] at h
  change _ ∈ mixedTruncationIdeal q at h
  apply ((mixedTruncationIdeal q).smul_mem_iff_of_isUnit
    (isUnit_neg_one.pow q.e1.toNat)).mp
  change (-1 : (MixedRing q)[X]) ^ q.e1.toNat * _ ∈ _
  convert h using 1
  simp only [mixedBThom, map_mul, map_pow, map_neg, map_one]
  ring

/-- The second no-root b-state loses a truncation site modulo the second chain ideal. -/
theorem mixedBThom_second_truncation (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B) :
    Polynomial.C (mixedBThom q .s2) * X ^ (q.A + q.B - 1).toNat ∈
      mixedTruncationIdeal q ⊔ (mixedBChain q 2).map Polynomial.C := by
  have hv := hq
  simp only [MixedValid] at hv
  have hm : (q.A + q.B - 1).toNat + 1 = (q.A + q.B).toNat := by omega
  have hf : mixedFirstPolynomial q * mixedFirstAmbientComplement q =
      X ^ ((q.A + q.B - 1).toNat + 1) := by
    rw [hm]
    exact mixedFirst_ambient_factorization q hq
  have h := characteristic_constant_power_mem (mixedSecondPolynomial q)
    (mixedFirstPolynomial q) (mixedFirstAmbientComplement q) 1
    (q.A + q.B - 1).toNat (mixedBChain q 2) hf (by
      rw [one_mul]
      exact mixedFirstAmbientComplement_constant_mem q)
  rw [one_mul, mixedSecondPolynomial_constant] at h
  have hI : relationIdeal (mixedSecondPolynomial q) (mixedFirstPolynomial q)
      ((q.A + q.B - 1).toNat + 1) = mixedTruncationIdeal q := by
    rw [hm]
    unfold relationIdeal mixedTruncationIdeal
    rw [mixedCharacteristic_factors, mul_comm (mixedSecondPolynomial q)]
  rw [hI] at h
  let J := mixedTruncationIdeal q ⊔ (mixedBChain q 2).map Polynomial.C
  apply (J.smul_mem_iff_of_isUnit (isUnit_neg_one.pow (mixedQ q - q.e2).toNat)).mp
  change (-1 : (MixedRing q)[X]) ^ (mixedQ q - q.e2).toNat * _ ∈ _
  convert h using 1
  simp only [mixedBThom, map_mul, map_pow, map_neg, map_one]
  ring

/-- The double-root a-state costs one truncation level modulo the sixth chain ideal. -/
theorem mixedAThom_doubleRoot_truncation (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) :
    Polynomial.C (mixedAThom q (.chosen, .complement)) * X *
        (mixedFirstPolynomial q).divX * (mixedSecondPolynomial q).divX ∈
      mixedTruncationIdeal q ⊔ (mixedAChain q 6).map Polynomial.C := by
  have hm : (q.A - 1).toNat + 1 = (q.A + q.B).toNat := by omega
  have hf : mixedSecondPolynomial q * mixedSecondAmbientComplement q =
      X ^ ((q.A - 1).toNat + 1) := by
    rw [hm]
    exact mixedSecond_ambient_factorization q hq
  have hp : (mixedFirstPolynomial q).coeff 0 ∈ mixedAChain q 6 := by
    rw [mixedFirstPolynomial_constant]
    exact (mixedAChain q 6).mul_mem_left _
      (mem_principalIdealPrefix _ 6 (5 : Fin 9) (by decide))
  have h := polynomial_both_mem (mixedFirstPolynomial q) (mixedSecondPolynomial q)
    (mixedSecondAmbientComplement q) (q.A - 1).toNat (mixedAChain q 6) hf hp
  rw [mixedSecondAmbientComplement_constant_without_b q hq hB, hm] at h
  change _ ∈ mixedTruncationIdeal q ⊔ (mixedAChain q 6).map Polynomial.C at h
  let J := mixedTruncationIdeal q ⊔ (mixedAChain q 6).map Polynomial.C
  apply (J.smul_mem_iff_of_isUnit (isUnit_neg_one.pow (q.e2.toNat + q.d3.toNat))).mp
  change (-1 : (MixedRing q)[X]) ^ (q.e2.toNat + q.d3.toNat) * _ ∈ _
  convert h using 1
  simp only [mixedAThom, map_mul, map_pow, map_neg, map_one]
  ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedBThom_first_truncation
#print axioms VOA.DeligneAudit.SL4T.mixedBThom_second_truncation
#print axioms VOA.DeligneAudit.SL4T.mixedAThom_doubleRoot_truncation
