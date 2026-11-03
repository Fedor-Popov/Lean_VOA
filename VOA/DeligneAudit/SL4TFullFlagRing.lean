import VOA.DeligneAudit.SL4TCompletePolynomialSpecialization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The truncated full-flag ring and complementary alphabets

The ambient polynomial ring has one variable per flag position. Its relations are all
positive elementary symmetric functions and the common power cutoff. Complete functions
of a subalphabet become the signed elementary polynomial of its complement.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The ideal of positive elementary symmetric functions in the full alphabet. -/
def fullFlagSymmetricIdeal (B : ℕ) : Ideal (MvPolynomial (Fin B) ℂ) :=
  Ideal.span {p | ∃ s : ℕ, 0 < s ∧ MvPolynomial.esymm (Fin B) ℂ s = p}

/-- The symmetric ideal has exactly the usual finite set of elementary generators. -/
theorem fullFlagSymmetricIdeal_finite (B : ℕ) :
    fullFlagSymmetricIdeal B = Ideal.span {p | ∃ s : ℕ,
      0 < s ∧ s ≤ B ∧ MvPolynomial.esymm (Fin B) ℂ s = p} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, rfl⟩
    by_cases hsB : s ≤ B
    · exact Ideal.subset_span ⟨s, hs, hsB, rfl⟩
    · have he : MvPolynomial.esymm (Fin B) ℂ s = 0 := by
        rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr]
        · exact Finset.sum_empty
        · simpa using (show B < s by omega)
      rw [he]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, _, rfl⟩
    exact Ideal.subset_span ⟨s, hs, rfl⟩

/-- The full-flag ideal with a common power cutoff on all roots. -/
def fullFlagTruncationIdeal (B N : ℕ) : Ideal (MvPolynomial (Fin B) ℂ) :=
  fullFlagSymmetricIdeal B ⊔
    Ideal.span (Set.range fun i : Fin B => (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ N)

/-- The truncated coinvariant ring, with cutoff independent of the number of positions. -/
abbrev FullFlagRing (B N : ℕ) :=
  MvPolynomial (Fin B) ℂ ⧸ fullFlagTruncationIdeal B N

/-- The root at a position in the truncated full flag. -/
def fullFlagRoot (B N : ℕ) (i : Fin B) : FullFlagRing B N :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem fullFlag_elementary_zero (B N s : ℕ) (hs : 0 < s) :
    Ideal.Quotient.mk (fullFlagTruncationIdeal B N)
      (MvPolynomial.esymm (Fin B) ℂ s) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (show fullFlagSymmetricIdeal B ≤ fullFlagTruncationIdeal B N from le_sup_left)
    (Ideal.subset_span ⟨s, hs, rfl⟩)

theorem fullFlagRoot_pow (B N : ℕ) (i : Fin B) : fullFlagRoot B N i ^ N = 0 := by
  rw [fullFlagRoot, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (show Ideal.span _ ≤ fullFlagTruncationIdeal B N from le_sup_right)
    (Ideal.subset_span ⟨i, rfl⟩)

variable {A D : Type*} [CommRing A] [CommRing D]

/-- Signed elementary polynomials commute with specialization of the roots. -/
theorem alphabetElementary_map (f : A →+* D) (xs : List A) :
    (D4Levi.ksEPoly xs).map f = D4Levi.ksEPoly (xs.map f) := by
  induction xs with
  | nil => simp [D4Levi.ksEPoly]
  | cons x xs ih =>
      simp only [D4Levi.ksEPoly, List.map_cons, List.prod_cons] at ih ⊢
      rw [Polynomial.map_mul, ih]
      simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X]

/-- The elementary polynomial of the full flag is the constant polynomial one. -/
theorem fullFlag_elementaryPolynomial (B N : ℕ) :
    D4Levi.ksEPoly (List.ofFn (fullFlagRoot B N)) = 1 := by
  let q := Ideal.Quotient.mk (fullFlagTruncationIdeal B N)
  have he : List.ofFn (fullFlagRoot B N) =
      (List.ofFn fun i : Fin B => (MvPolynomial.X i : MvPolynomial (Fin B) ℂ)).map q := by
    rw [List.map_ofFn]
    rfl
  rw [he, ← alphabetElementary_map]
  ext s
  rw [coeff_map, elementaryProduct_coeff]
  cases s with
  | zero => simp
  | succ s =>
      simp only [map_mul, map_pow, map_neg, map_one]
      rw [show q (MvPolynomial.esymm (Fin B) ℂ (s + 1)) = 0 from
        fullFlag_elementary_zero B N (s + 1) (by omega)]
      simp only [mul_zero, coeff_one, Nat.add_one_ne_zero, if_false]

/-- In a coinvariant alphabet, the complete series is the elementary polynomial
of the complementary alphabet. -/
theorem alphabetComplete_eq_complement (xs ys : List A)
    (h : D4Levi.ksEPoly (xs ++ ys) = 1) :
    D4Levi.ksHSeries xs = (D4Levi.ksEPoly ys : PowerSeries A) := by
  have ht := D4Levi.ksHSeries_mul_EPoly (xs ++ ys)
  rw [h, Polynomial.coe_one, mul_one] at ht
  rw [D4Levi.ksHSeries_remove xs ys, ht, one_mul]

/-- Complete functions above the size of the complement vanish. -/
theorem alphabetComplete_vanish (xs ys : List A)
    (h : D4Levi.ksEPoly (xs ++ ys) = 1) (s : ℕ) (hs : ys.length < s) :
    PowerSeries.coeff s (D4Levi.ksHSeries xs) = 0 := by
  rw [alphabetComplete_eq_complement xs ys h, Polynomial.coeff_coe]
  exact D4Levi.ksEPoly_coeff_eq_zero ys s hs

/-- Deleting one root makes every signed elementary coefficient a power of that root. -/
theorem alphabetElementary_delete_root (xs : List A) (z : A)
    (h : D4Levi.ksEPoly (xs ++ [z]) = 1) (s : ℕ) :
    (D4Levi.ksEPoly xs).coeff s = z ^ s := by
  have he : D4Levi.ksEPoly ([z] ++ xs) = 1 := by
    simp only [D4Levi.ksEPoly, List.map_append, List.prod_append] at h ⊢
    rw [mul_comm]
    exact h
  have hc := congrArg (PowerSeries.coeff s) (alphabetComplete_eq_complement [z] xs he)
  simpa [D4Levi.ksHSeries, D4Levi.ksGeometricSeries] using hc.symm

/-- The complete function of two roots is the usual sum of monomials. -/
theorem twoRoot_complete (x y : A) (s : ℕ) :
    PowerSeries.coeff s (D4Levi.ksHSeries [x, y]) =
      ∑ a ∈ Finset.range (s + 1), x ^ a * y ^ (s - a) := by
  simp only [D4Levi.ksHSeries, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [D4Levi.ksGeometricSeries]

/-- In the full coinvariant ring, a two-root complete function vanishes above
the number of remaining roots. -/
theorem twoRoot_complete_vanish (x y : A) (xs : List A)
    (h : D4Levi.ksEPoly ([x, y] ++ xs) = 1) (s : ℕ) (hs : xs.length < s) :
    ∑ a ∈ Finset.range (s + 1), x ^ a * y ^ (s - a) = 0 := by
  rw [← twoRoot_complete]
  exact alphabetComplete_vanish [x, y] xs h s hs

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlag_elementary_zero
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_finite
#print axioms VOA.DeligneAudit.SL4T.fullFlagRoot_pow
#print axioms VOA.DeligneAudit.SL4T.alphabetElementary_map
#print axioms VOA.DeligneAudit.SL4T.fullFlag_elementaryPolynomial
#print axioms VOA.DeligneAudit.SL4T.alphabetComplete_eq_complement
#print axioms VOA.DeligneAudit.SL4T.alphabetComplete_vanish
#print axioms VOA.DeligneAudit.SL4T.alphabetElementary_delete_root
#print axioms VOA.DeligneAudit.SL4T.twoRoot_complete
#print axioms VOA.DeligneAudit.SL4T.twoRoot_complete_vanish
