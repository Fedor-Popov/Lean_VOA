import VOA.DeligneAudit.SL4TFullFlagPowerRelations
import Mathlib.Algebra.Polynomial.Reverse

/-! # Characteristic polynomials and deletion of a full-flag root -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {A : Type*} [CommRing A]

/-- The monic characteristic polynomial of an alphabet, with descending coefficients. -/
def alphabetCharacteristic (xs : List A) : A[X] :=
  (D4Levi.ksEPoly xs).reflect xs.length

theorem alphabetCharacteristic_append (xs ys : List A) :
    alphabetCharacteristic (xs ++ ys) =
      alphabetCharacteristic xs * alphabetCharacteristic ys := by
  simp only [alphabetCharacteristic, D4Levi.ksEPoly, List.map_append, List.prod_append,
    List.length_append]
  exact reflect_mul _ _ (D4Levi.ksEPoly_natDegree_le xs)
    (D4Levi.ksEPoly_natDegree_le ys)

theorem alphabetCharacteristic_singleton (x : A) :
    alphabetCharacteristic [x] = X - Polynomial.C x := by
  simp only [alphabetCharacteristic, D4Levi.ksEPoly, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil,
    zero_add, reflect_sub, reflect_one, pow_one, reflect_C_mul, reflect_one_X]

theorem alphabetCharacteristic_product (xs : List A) :
    alphabetCharacteristic xs = (xs.map fun x => X - Polynomial.C x).prod := by
  induction xs with
  | nil => simp [alphabetCharacteristic, D4Levi.ksEPoly]
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, alphabetCharacteristic_append,
        alphabetCharacteristic_singleton, ih]
      rfl

theorem alphabetCharacteristic_monic (xs : List A) :
    (alphabetCharacteristic xs).Monic := by
  induction xs with
  | nil => simp [alphabetCharacteristic, D4Levi.ksEPoly]
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, alphabetCharacteristic_append,
        alphabetCharacteristic_singleton]
      exact (monic_X_sub_C x).mul ih

theorem alphabetCharacteristic_coeff (xs : List A) (l : ℕ) (hl : l ≤ xs.length) :
    (alphabetCharacteristic xs).coeff l = (D4Levi.ksEPoly xs).coeff (xs.length - l) := by
  rw [alphabetCharacteristic, coeff_reflect, revAt_le hl]

theorem alphabetCharacteristic_natDegree_le (xs : List A) :
    (alphabetCharacteristic xs).natDegree ≤ xs.length :=
  natDegree_reflect_le.trans (max_le le_rfl (D4Levi.ksEPoly_natDegree_le xs))

theorem alphabetCharacteristic_natDegree [Nontrivial A] (xs : List A) :
    (alphabetCharacteristic xs).natDegree = xs.length := by
  induction xs with
  | nil => simp [alphabetCharacteristic, D4Levi.ksEPoly]
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, alphabetCharacteristic_append,
        alphabetCharacteristic_singleton,
        (monic_X_sub_C x).natDegree_mul (alphabetCharacteristic_monic xs), ih]
      simp [Nat.add_comm]

theorem fullFlag_characteristicPolynomial (B N : ℕ) :
    alphabetCharacteristic (List.ofFn (fullFlagRoot B N)) = X ^ B := by
  rw [alphabetCharacteristic, fullFlag_elementaryPolynomial, List.length_ofFn, reflect_one]

/-- Deleting a root from a coinvariant alphabet gives the finite geometric polynomial. -/
theorem alphabetCharacteristic_delete_expansion (xs : List A) (z : A)
    (h : D4Levi.ksEPoly (xs ++ [z]) = 1) :
    alphabetCharacteristic xs =
      ∑ e ∈ Finset.range (xs.length + 1), Polynomial.C (z ^ e) * X ^ (xs.length - e) := by
  classical
  ext l
  rw [finsetSum_coeff]
  by_cases hl : l ≤ xs.length
  · rw [alphabetCharacteristic_coeff xs l hl, alphabetElementary_delete_root xs z h,
      Finset.sum_eq_single (xs.length - l)]
    · rw [coeff_C_mul_X_pow, show xs.length - (xs.length - l) = l by omega, if_pos rfl]
    · intro e he hne
      rw [coeff_C_mul_X_pow, if_neg]
      have := Finset.mem_range.mp he
      omega
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [coeff_eq_zero_of_natDegree_lt
      ((alphabetCharacteristic_natDegree_le xs).trans_lt (by omega))]
    symm
    apply Finset.sum_eq_zero
    intro e he
    rw [coeff_C_mul_X_pow, if_neg (by omega)]

/-- A subalphabet characteristic divides the characteristic after deleting a root. -/
theorem alphabetCharacteristic_deleted_mem (ys zs : List A) (z : A)
    (h : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) :
    (∑ e ∈ Finset.range ((ys ++ zs).length + 1),
      Polynomial.C (z ^ e) * X ^ ((ys ++ zs).length - e)) ∈
        Ideal.span {alphabetCharacteristic ys} := by
  rw [← alphabetCharacteristic_delete_expansion (ys ++ zs) z h,
    alphabetCharacteristic_append]
  exact Ideal.mem_span_singleton.mpr ⟨alphabetCharacteristic zs, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_append
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_singleton
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_product
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_monic
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_coeff
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_natDegree
#print axioms VOA.DeligneAudit.SL4T.fullFlag_characteristicPolynomial
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_delete_expansion
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_deleted_mem
