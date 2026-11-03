import VOA.DeligneAudit.SL4TTopIdealGradedLevel

/-! # The zero-minor boundary of the graded remainder certificate -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {σ A : Type*} [CommRing A]

/-- The empty minor is one, independently of the cutoff and alphabet. -/
theorem remainderTopIdeal_zero (xs : List A) (N : ℕ) :
    remainderTopIdeal xs N 0 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := remainderTopMinor_mem xs N 0 (fun a => Fin.elim0 a)
  simpa only [remainderTopMinor, Matrix.det_isEmpty] using h

/-- The characteristic coefficient at the alphabet length is one over every ring. -/
theorem alphabetCharacteristic_top_coeff (xs : List A) :
    (alphabetCharacteristic xs).coeff xs.length = 1 := by
  rw [alphabetCharacteristic_coeff xs xs.length le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero]
  induction xs with
  | nil => simp [D4Levi.ksEPoly]
  | cons x xs ih => simpa [D4Levi.ksEPoly] using ih

/-- Removing the leading characteristic monomial leaves strictly smaller powers. -/
theorem alphabetCharacteristic_tail_degree (xs : List A) :
    (alphabetCharacteristic xs - Polynomial.X ^ xs.length).degree <
      (xs.length : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro l hl
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  by_cases he : l = xs.length
  · subst l
    rw [alphabetCharacteristic_top_coeff, if_pos rfl, sub_self]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((alphabetCharacteristic_natDegree_le xs).trans_lt (by omega)), if_neg he, sub_self]

/-- At the empty minor, the homogeneous characteristic relation supplies the certificate. -/
theorem remainderTopIdeal_zero_graded_certificate (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N : ℕ) (a : MvPolynomial σ A) (d : ℤ) (ha : a.IsWeightedHomogeneous w d) :
    ∃ p : Polynomial (MvPolynomial σ A),
      p.degree < (xs.length : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N 0) ∧
      (∀ l, (p.coeff l).IsWeightedHomogeneous w (d + xs.length - l)) ∧
      Polynomial.C a * Polynomial.X ^ xs.length + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  let p := Polynomial.C a * (alphabetCharacteristic xs - Polynomial.X ^ xs.length)
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro l hl
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (alphabetCharacteristic_tail_degree xs) (by exact_mod_cast hl)), mul_zero]
  · intro l
    rw [remainderTopIdeal_zero]
    exact Submodule.mem_top
  · exact polynomialCoefficientsHomogeneous_mul w _ _ d xs.length
      (polynomialCoefficientsHomogeneous_constant w a d ha)
      (polynomialCoefficientsHomogeneous_sub w _ _ xs.length
        (alphabetCharacteristic_homogeneous w xs hxs)
        (polynomialCoefficientsHomogeneous_power w xs.length))
  · have he : Polynomial.C a * Polynomial.X ^ xs.length + p =
        Polynomial.C a * alphabetCharacteristic xs := by dsimp [p]; ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- The graded certificate includes every possible minor size, including the empty minor. -/
theorem remainderTopIdeal_all_sizes_graded_certificate (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (hjr : j ≤ xs.length)
    (a : MvPolynomial σ A) (d : ℤ) (ha : a.IsWeightedHomogeneous w d)
    (hmem : a ∈ remainderTopIdeal xs N j) :
    ∃ p : Polynomial (MvPolynomial σ A),
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N j) ∧
      (∀ l, (p.coeff l).IsWeightedHomogeneous w (d + (xs.length - j : ℕ) - l)) ∧
      Polynomial.C a * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  by_cases hj : j = 0
  · subst j
    simpa only [Nat.sub_zero, sub_zero] using
      remainderTopIdeal_zero_graded_certificate w xs hxs N a d ha
  · exact remainderTopIdeal_graded_certificate w xs hxs N j (by omega) hjr a d ha hmem

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_zero
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_top_coeff
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_tail_degree
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_zero_graded_certificate
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_all_sizes_graded_certificate
