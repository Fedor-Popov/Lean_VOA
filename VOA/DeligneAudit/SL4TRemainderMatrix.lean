import VOA.DeligneAudit.SL4TFullFlagCharacteristic
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Remainder coefficients from the inverse elementary series -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {A : Type*} [CommRing A]

/-- The coefficient of a power reduced modulo an alphabet characteristic. -/
def alphabetPowerRemainder (xs : List A) (m l : ℕ) : A :=
  (X ^ m %ₘ alphabetCharacteristic xs).coeff l

/-- The remainder matrix has columns given by consecutive powers starting at the cutoff. -/
def alphabetRemainderMatrix (xs : List A) (N : ℕ) : Fin xs.length → ℕ → A :=
  fun l c => alphabetPowerRemainder xs (N + c) l

/-- Truncating the inverse series does not change product coefficients below the cutoff. -/
theorem inverseSeries_trunc_product_coeff (E : A[X]) (H : PowerSeries A)
    (hEH : (E : PowerSeries A) * H = 1) (q n : ℕ) (hn : n ≤ q) :
    (E * PowerSeries.trunc (q + 1) H).coeff n = if n = 0 then 1 else 0 := by
  have he : (E * PowerSeries.trunc (q + 1) H).coeff n =
      PowerSeries.coeff n ((E : PowerSeries A) * H) := by
    rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega)]
  rw [he, hEH, PowerSeries.coeff_one]

/-- Reflecting a truncated complete series gives the polynomial quotient. -/
def alphabetPowerQuotient (xs : List A) (m : ℕ) : A[X] :=
  (PowerSeries.trunc (m - xs.length + 1) (D4Levi.ksHSeries xs)).reflect (m - xs.length)

theorem alphabetPowerQuotient_product (xs : List A) (m : ℕ) (hm : xs.length ≤ m) :
    alphabetCharacteristic xs * alphabetPowerQuotient xs m =
      (D4Levi.ksEPoly xs *
        PowerSeries.trunc (m - xs.length + 1) (D4Levi.ksHSeries xs)).reflect m := by
  rw [alphabetCharacteristic, alphabetPowerQuotient,
    ← reflect_mul _ _ (D4Levi.ksEPoly_natDegree_le xs)
      (Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ _)),
    Nat.add_sub_of_le hm]

theorem alphabetPowerQuotient_remainder_degree (xs : List A) (m : ℕ)
    (hm : xs.length ≤ m) :
    (X ^ m - alphabetCharacteristic xs * alphabetPowerQuotient xs m).degree <
      (xs.length : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_sub, alphabetPowerQuotient_product xs m hm, coeff_reflect]
  by_cases hnm : n ≤ m
  · rw [revAt_le hnm, inverseSeries_trunc_product_coeff _ _
      (by rw [mul_comm]; exact D4Levi.ksHSeries_mul_EPoly xs) _ _ (by omega), coeff_X_pow]
    by_cases hne : n = m
    · subst n
      simp
    · rw [if_neg hne, if_neg (by omega), sub_self]
  · rw [revAt_eq_self_of_lt (by omega), coeff_X_pow, if_neg (by omega)]
    rw [coeff_eq_zero_of_natDegree_lt, sub_self]
    apply lt_of_le_of_lt natDegree_mul_le
    have he := D4Levi.ksEPoly_natDegree_le xs
    have hh := PowerSeries.natDegree_trunc_lt (D4Levi.ksHSeries xs) (m - xs.length)
    omega

/-- Division by the characteristic polynomial is computed by the complete series. -/
theorem alphabetPower_division (xs : List A) (m : ℕ) (hm : xs.length ≤ m) :
    X ^ m %ₘ alphabetCharacteristic xs =
      X ^ m - alphabetCharacteristic xs * alphabetPowerQuotient xs m := by
  nontriviality A
  have hd : (alphabetCharacteristic xs).degree = (xs.length : WithBot ℕ) := by
    rw [degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
      alphabetCharacteristic_natDegree]
  exact (div_modByMonic_unique (alphabetPowerQuotient xs m) _
    (alphabetCharacteristic_monic xs)
    ⟨by ring, hd ▸ alphabetPowerQuotient_remainder_degree xs m hm⟩).2

/-- The tail of an inverse series gives a short initial convolution. -/
theorem inverseSeries_trunc_tail_coeff (E : A[X]) (H : PowerSeries A)
    (hEH : (E : PowerSeries A) * H = 1) (q s : ℕ) (hqs : q < s) :
    (if s = 0 then 1 else 0) - (E * PowerSeries.trunc (q + 1) H).coeff s =
      ∑ a ∈ Finset.range (s - q), E.coeff a * PowerSeries.coeff (s - a) H := by
  classical
  have hc := congrArg (PowerSeries.coeff s) hEH
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at hc
  simp only [Polynomial.coeff_coe] at hc
  rw [← hc, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_sub_distrib]
  symm
  trans ∑ a ∈ Finset.range (s - q), (E.coeff a * PowerSeries.coeff (s - a) H -
    E.coeff a * (PowerSeries.trunc (q + 1) H).coeff (s - a))
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [PowerSeries.coeff_trunc, if_neg (by omega), mul_zero, sub_zero]
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro a ha hnot
    have ha' := Finset.mem_range.mp ha
    have hnot' : s - q ≤ a := by simpa using hnot
    rw [PowerSeries.coeff_trunc, if_pos (by omega), sub_self]

/-- The explicit complete-function expression for every sufficiently high power. -/
theorem alphabetPowerRemainder_coeff_of_large (xs : List A) (m l : ℕ)
    (hm : xs.length ≤ m) (hl : l < xs.length) :
    alphabetPowerRemainder xs m l = ∑ a ∈ Finset.range (xs.length - l),
      (D4Levi.ksEPoly xs).coeff a * PowerSeries.coeff (m - l - a) (D4Levi.ksHSeries xs) := by
  rw [alphabetPowerRemainder, alphabetPower_division xs m hm, coeff_sub,
    alphabetPowerQuotient_product xs m hm, coeff_reflect, revAt_le (by omega), coeff_X_pow]
  have hle : l ≠ m := by omega
  rw [if_neg hle]
  have he := inverseSeries_trunc_tail_coeff (D4Levi.ksEPoly xs) (D4Levi.ksHSeries xs)
    (by rw [mul_comm]; exact D4Levi.ksHSeries_mul_EPoly xs) (m - xs.length) (m - l)
    (by omega)
  simpa only [show m - l ≠ 0 by omega, if_false,
    show m - l - (m - xs.length) = xs.length - l by omega] using he

/-- The complete-function formula, including powers smaller than the alphabet.
The conditional implements the convention that negative complete indices give zero. -/
theorem alphabetPowerRemainder_coeff (xs : List A) (m l : ℕ) (hl : l < xs.length) :
    alphabetPowerRemainder xs m l = ∑ a ∈ Finset.range (xs.length - l),
      if l + a ≤ m then (D4Levi.ksEPoly xs).coeff a *
        PowerSeries.coeff (m - l - a) (D4Levi.ksHSeries xs) else 0 := by
  classical
  by_cases hm : xs.length ≤ m
  · rw [alphabetPowerRemainder_coeff_of_large xs m l hm hl]
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos (by have := Finset.mem_range.mp ha; omega)]
  · nontriviality A
    have hd : (X ^ m : A[X]).degree < (alphabetCharacteristic xs).degree := by
      rw [degree_X_pow, degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
        alphabetCharacteristic_natDegree]
      exact_mod_cast (show m < xs.length by omega)
    rw [alphabetPowerRemainder, modByMonic_eq_self_iff
      (alphabetCharacteristic_monic xs) |>.mpr hd, coeff_X_pow]
    by_cases hlm : l ≤ m
    · have hc := congrArg (PowerSeries.coeff (m - l)) (D4Levi.ksHSeries_mul_EPoly xs)
      rw [mul_comm, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_one] at hc
      simp only [Polynomial.coeff_coe] at hc
      have hs : (∑ a ∈ Finset.range (xs.length - l),
          if l + a ≤ m then (D4Levi.ksEPoly xs).coeff a *
            PowerSeries.coeff (m - l - a) (D4Levi.ksHSeries xs) else 0) =
          ∑ a ∈ Finset.range (m - l + 1), (D4Levi.ksEPoly xs).coeff a *
            PowerSeries.coeff (m - l - a) (D4Levi.ksHSeries xs) := by
        symm
        trans ∑ a ∈ Finset.range (m - l + 1),
          if l + a ≤ m then (D4Levi.ksEPoly xs).coeff a *
            PowerSeries.coeff (m - l - a) (D4Levi.ksHSeries xs) else 0
        · apply Finset.sum_congr rfl
          intro a ha
          rw [if_pos (by have := Finset.mem_range.mp ha; omega)]
        · apply Finset.sum_subset (Finset.range_mono (by omega))
          intro a ha hnot
          have hbound : m - l + 1 ≤ a := by simpa using hnot
          rw [if_neg (by omega)]
      rw [hs, hc]
      by_cases he : l = m
      · subst l
        simp
      · rw [if_neg he, if_neg (by omega)]
    · rw [if_neg (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg (by omega)]

/-- Every column of the remainder matrix has the complete-function formula. -/
theorem alphabetRemainderMatrix_coeff (xs : List A) (N c : ℕ) (l : Fin xs.length) :
    alphabetRemainderMatrix xs N l c = ∑ a ∈ Finset.range (xs.length - l.val),
      if l.val + a ≤ N + c then (D4Levi.ksEPoly xs).coeff a *
        PowerSeries.coeff (N + c - l.val - a) (D4Levi.ksHSeries xs) else 0 :=
  alphabetPowerRemainder_coeff xs (N + c) l l.isLt

/-- In free root coordinates the entries are signed elementary-complete convolutions. -/
theorem finiteAlphabet_remainderMatrix_coeff (r N c : ℕ) (l : Fin r) :
    alphabetPowerRemainder
        (List.ofFn fun i : Fin r => (MvPolynomial.X i : MvPolynomial (Fin r) ℂ))
        (N + c) l.val =
      ∑ a ∈ Finset.range (r - l.val), if l.val + a ≤ N + c then
        (-1) ^ a * MvPolynomial.esymm (Fin r) ℂ a *
          MvPolynomial.hsymm (Fin r) ℂ (N + c - l.val - a) else 0 := by
  rw [alphabetPowerRemainder_coeff _ _ _ (by simpa only [List.length_ofFn] using l.isLt)]
  simp only [List.length_ofFn, elementaryProduct_coeff, D4Levi.ksHSeries_coeff_hsymm]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.inverseSeries_trunc_product_coeff
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerQuotient_product
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerQuotient_remainder_degree
#print axioms VOA.DeligneAudit.SL4T.alphabetPower_division
#print axioms VOA.DeligneAudit.SL4T.inverseSeries_trunc_tail_coeff
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_coeff_of_large
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_coeff
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainderMatrix_coeff
#print axioms VOA.DeligneAudit.SL4T.finiteAlphabet_remainderMatrix_coeff
