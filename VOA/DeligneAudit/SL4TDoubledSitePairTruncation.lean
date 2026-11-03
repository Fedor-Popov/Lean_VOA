import VOA.DeligneAudit.SL4TDoubledSitePairRelations
import VOA.DeligneAudit.SL4TMiddleFlagPeel

/-! The shortened characteristic and power relations for all surviving pair types. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- The ten surviving characteristic lifts satisfy their shortened cutoff relations. -/
theorem doubledPairPolynomial_relation (p : Fin 4 → R[X]) (I : Ideal R) (n : ℕ)
    (hprod : ∏ i : Fin 4, p i = X ^ (n + 2))
    (htail : ∀ i, (p i).coeff 1 * ∏ j ∈ Finset.univ.erase i, (p j).coeff 0 ∈ I)
    (k : Fin 10) :
    Polynomial.C (doubledPairTop (fun i => (p i).coeff 0) k) *
        X ^ doubledPairLevelShift k * doubledPairPolynomial p k ∈
      (doubledPairPrefix (fun i => (p i).coeff 0) I k.val).map Polynomial.C ⊔
        relationIdeal (p 2) (p 3) (n + 1) := by
  let a := fun i => (p i).coeff 0
  have hz : a 0 * a 1 * a 2 * a 3 = 0 := by
    have h := congrArg (fun f : R[X] => f.coeff 0) hprod
    simpa [Fin.prod_univ_succ, mul_assoc, a] using h
  have hb := doubledPairTop_boundaries a (fun i => (p i).coeff 1) I hz htail k
  have hf : (p 2 * p 3) * (p 0 * p 1) = X ^ ((n + 1) + 1) := by
    calc
      _ = ∏ i : Fin 4, p i := by simp [Fin.prod_univ_succ]; ring
      _ = _ := by simpa only [Nat.add_assoc] using hprod
  have hf' : (p 3 * p 2) * (p 0 * p 1) = X ^ ((n + 1) + 1) := by
    simpa only [mul_comm (p 3) (p 2)] using hf
  fin_cases k
  · have h := (relationIdeal (p 2) (p 3) (n + 1)).mul_mem_left
      (Polynomial.C (doubledPairTop a 0)) (relationIdeal_product (p 2) (p 3) (n + 1))
    apply (show relationIdeal (p 2) (p 3) (n + 1) ≤ _ from le_sup_right)
    simpa [doubledPairLevelShift, doubledPairPolynomial, a] using h
  · have h := (relationIdeal (p 2) (p 3) (n + 1)).mul_mem_left
      (Polynomial.C (doubledPairTop a 1)) (relationIdeal_product (p 2) (p 3) (n + 1))
    apply (show relationIdeal (p 2) (p 3) (n + 1) ≤ _ from le_sup_right)
    simpa [doubledPairLevelShift, doubledPairPolynomial, a] using h
  · have h := (relationIdeal (p 2) (p 3) (n + 1)).mul_mem_left
      (Polynomial.C (doubledPairTop a 2)) (relationIdeal_product (p 2) (p 3) (n + 1))
    apply (show relationIdeal (p 2) (p 3) (n + 1) ≤ _ from le_sup_right)
    simpa [doubledPairLevelShift, doubledPairPolynomial, a] using h
  · have h := polynomial_two_equal_removals_mem (p 2) (p 3) (p 0 * p 1)
      (n + 1) (doubledPairPrefix a I 3) ((p 3).coeff 0) hf
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.1)
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.2)
    simpa [a, doubledPairTop, doubledPairPolynomial, doubledPairLevelShift,
      mul_coeff_zero, relationIdeal, mul_comm, mul_left_comm, mul_assoc, sup_comm] using h
  · have h := polynomial_one_retained_removal_mem (p 2) (p 3) (n + 1)
      (doubledPairPrefix a I 4) (doubledPairTop a 4)
      (by simpa [a, doubledPairIndices] using hb.1)
    simpa [a, doubledPairTop, doubledPairPolynomial, doubledPairLevelShift,
      relationIdeal, mul_comm, mul_left_comm, mul_assoc, sup_comm] using h
  · have h := polynomial_one_retained_removal_mem (p 2) (p 3) (n + 1)
      (doubledPairPrefix a I 5) (doubledPairTop a 5)
      (by simpa [a, doubledPairIndices] using hb.1)
    change Polynomial.C (a 3) * X * (p 2).divX * p 3 ∈
      relationIdeal (p 2) (p 3) (n + 1) ⊔ (doubledPairPrefix a I 5).map Polynomial.C at h
    change Polynomial.C (a 3) * X ^ 1 * ((p 2).divX * p 3) ∈
      (doubledPairPrefix a I 5).map Polynomial.C ⊔ relationIdeal (p 2) (p 3) (n + 1)
    simpa only [pow_one, mul_assoc, sup_comm] using h
  · have h := polynomial_two_equal_removals_mem (p 3) (p 2) (p 0 * p 1)
      (n + 1) (doubledPairPrefix a I 6) ((p 2).coeff 0) hf'
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.1)
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.2)
    simpa [a, doubledPairTop, doubledPairPolynomial, doubledPairLevelShift,
      mul_coeff_zero, relationIdeal, mul_comm, mul_left_comm, mul_assoc, sup_comm] using h
  · have h := polynomial_two_distinct_removals_mem (p 2) (p 3) (p 0 * p 1)
      (n + 1) (doubledPairPrefix a I 7) hf
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.2)
      (by simpa [a, doubledPairTop, doubledPairIndices, mul_coeff_zero,
        mul_comm, mul_left_comm, mul_assoc] using hb.1)
    simpa [a, doubledPairTop, doubledPairPolynomial, doubledPairLevelShift,
      mul_coeff_zero, relationIdeal, mul_comm, mul_left_comm, mul_assoc, sup_comm] using h
  · have h := polynomial_one_retained_removal_mem (p 3) (p 2) (n + 1)
      (doubledPairPrefix a I 8) (doubledPairTop a 8)
      (by simpa [a, doubledPairIndices] using hb.1)
    change Polynomial.C (a 0) * X * (p 3).divX * p 2 ∈
      relationIdeal (p 3) (p 2) (n + 1) ⊔ (doubledPairPrefix a I 8).map Polynomial.C at h
    have hswap : relationIdeal (p 3) (p 2) (n + 1) =
        relationIdeal (p 2) (p 3) (n + 1) := by unfold relationIdeal; rw [mul_comm]
    rw [hswap, sup_comm] at h
    change Polynomial.C (a 0) * X ^ 1 * (p 2 * (p 3).divX) ∈
      (doubledPairPrefix a I 8).map Polynomial.C ⊔ relationIdeal (p 2) (p 3) (n + 1)
    convert h using 1 <;> ring
  · have h := polynomial_one_retained_removal_mem (p 3) (p 2) (n + 1)
      (doubledPairPrefix a I 9) (doubledPairTop a 9)
      (by simpa [a, doubledPairIndices] using hb.1)
    simpa [a, doubledPairTop, doubledPairPolynomial, doubledPairLevelShift,
      relationIdeal, mul_comm, mul_left_comm, mul_assoc, sup_comm] using h

/-- The inner power relation also descends at the shortened cutoff for every pair. -/
theorem doubledPairPower_relation (p : Fin 4 → R[X]) (I : Ideal R) (n : ℕ) (k : Fin 10) :
    Polynomial.C (doubledPairTop (fun i => (p i).coeff 0) k) *
        X ^ (n + doubledPairLevelShift k) ∈
      (doubledPairPrefix (fun i => (p i).coeff 0) I k.val).map Polynomial.C ⊔
        relationIdeal (p 2) (p 3) (n + 1) := by
  apply (show relationIdeal (p 2) (p 3) (n + 1) ≤ _ from le_sup_right)
  by_cases hk : k.val < 3
  · fin_cases k <;> norm_num at hk
    · simpa [doubledPairTop, doubledPairLevelShift, mul_coeff_zero, mul_assoc] using
        polynomial_no_retained_removal_mem (p 2) (p 3) n ((p 1).coeff 0)
    · simpa [doubledPairTop, doubledPairLevelShift, mul_coeff_zero, mul_assoc] using
        polynomial_no_retained_removal_mem (p 2) (p 3) n ((p 0).coeff 0)
    · simpa [doubledPairTop, doubledPairLevelShift, mul_coeff_zero] using
        polynomial_no_retained_removal_mem (p 2) (p 3) n 1
  · rw [doubledPairLevelShift, if_neg hk]
    exact (relationIdeal (p 2) (p 3) (n + 1)).mul_mem_left _
      (relationIdeal_power (p 2) (p 3) (n + 1))

/-- The four characteristic polynomials in the forward doubled-site order. -/
def doubledSiteFlagPolynomials (q : MixedParams) (i : Fin 4) : (MixedRing q)[X] :=
  middleFlagPolynomial q (doubledSiteFlagIndex i)

/-- All surviving pair relations hold in every actual middle-weight block. -/
theorem doubledSitePair_polynomialRelations (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10) :
    let p := doubledSiteFlagPolynomials q
    let a := fun i => (p i).coeff 0
    let J := doubledPairPrefix a (middleFlagTailIdeal q (q.B.toNat - 1)) k.val
    let A := relationIdeal (p 2) (p 3) (q.B.toNat - 1)
    Polynomial.C (doubledPairTop a k) * X ^ doubledPairLevelShift k *
        doubledPairPolynomial p k ∈ J.map Polynomial.C ⊔ A ∧
      Polynomial.C (doubledPairTop a k) * X ^ (q.B.toNat - 2 + doubledPairLevelShift k) ∈
        J.map Polynomial.C ⊔ A := by
  dsimp only
  have hn : 2 ≤ q.B.toNat := by omega
  have hp : (∏ i : Fin 4, doubledSiteFlagPolynomials q i) =
      X ^ (q.B.toNat - 2 + 2) := by
    rw [Nat.sub_add_cancel hn]
    have h := middleFlagPolynomial_product q hq hA
    convert h using 1
    simp [doubledSiteFlagPolynomials, doubledSiteFlagIndex, Fin.prod_univ_succ]
    ring
  have ht (i : Fin 4) : (doubledSiteFlagPolynomials q i).coeff 1 *
      ∏ j ∈ Finset.univ.erase i, (doubledSiteFlagPolynomials q j).coeff 0 ∈
        middleFlagTailIdeal q (q.B.toNat - 1) := by
    change doubledSiteSignedLinear q i *
      ∏ j ∈ Finset.univ.erase i, doubledSiteSignedTop q j ∈ _
    rw [doubledSiteSignedLinear_tail q hq hA hB]
    exact Ideal.subset_span ⟨doubledSiteFlagIndex i, rfl⟩
  have hcut : q.B.toNat - 2 + 1 = q.B.toNat - 1 := by omega
  constructor
  · simpa only [hcut] using doubledPairPolynomial_relation (doubledSiteFlagPolynomials q)
      (middleFlagTailIdeal q (q.B.toNat - 1)) (q.B.toNat - 2) hp ht k
  · simpa only [hcut] using doubledPairPower_relation (doubledSiteFlagPolynomials q)
      (middleFlagTailIdeal q (q.B.toNat - 1)) (q.B.toNat - 2) k

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doubledPairPolynomial_relation
#print axioms VOA.DeligneAudit.SL4T.doubledPairPower_relation
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_polynomialRelations
